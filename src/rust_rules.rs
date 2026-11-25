//! Source-shape rules over rustc's unexpanded AST.

use indexmap::IndexMap;
use rustc_ast::{
    ast,
    visit::{self, Visitor},
};
use rustc_hash::{FxHashMap, FxHashSet};
use rustc_span::symbol::Ident;

use crate::diagnostic::{Report, Sink};
use crate::rust_syntax::{RustFile, is_test_path, test_attributes};
use crate::suggest::Code;
use crate::{Config, SourceInput, Span};

pub(crate) fn lint(sink: &mut Sink, file: &RustFile<'_>, source: &SourceInput, config: &Config) {
    let index = Collector::collect(file);
    let mut uses: FxHashMap<String, Uses> = FxHashMap::default();
    let callees: FxHashSet<_> = index
        .exprs
        .iter()
        .filter_map(|expr| match &expr.kind {
            ast::ExprKind::Call(callee, _) => Some(callee.span),
            _ => None,
        })
        .collect();
    for expr in &index.exprs {
        match &expr.kind {
            ast::ExprKind::Path(_, path) => {
                let qualified = path
                    .segments
                    .iter()
                    .map(|s| s.ident.name.as_str())
                    .collect::<Vec<_>>()
                    .join("::");
                let Some(last) = path.segments.last() else {
                    continue;
                };
                let name = last.ident.name.to_string();
                let names = if qualified == name {
                    vec![name]
                } else {
                    vec![qualified, name]
                };
                for name in names {
                    let entry = uses.entry(name).or_default();
                    if callees.contains(&expr.span) {
                        entry.calls += 1;
                    } else {
                        entry.as_value = Some(());
                    }
                }
            }
            ast::ExprKind::MethodCall(call) => {
                uses.entry(call.seg.ident.name.to_string())
                    .or_default()
                    .calls += 1
            }
            _ => {}
        }
    }
    let attrs = index
        .attrs
        .iter()
        .map(|attr| file.text(attr.span))
        .collect::<Vec<_>>()
        .join("\n");
    let mut owners = FxHashMap::default();
    for item in &index.items {
        let span = file.item_span(item.span, &item.attrs);
        let prefix = match &item.kind {
            ast::ItemKind::Struct(..) => "struct",
            ast::ItemKind::Enum(..) => "enum",
            ast::ItemKind::Static(..) => "static",
            ast::ItemKind::TyAlias(..) => "type",
            ast::ItemKind::Trait(..) => "trait",
            ast::ItemKind::Use(..) => "use",
            _ => "<item>",
        };
        let name = match &item.kind {
            ast::ItemKind::Use(..) => short(file.text(item.span), 60),
            _ => match item.kind.ident() {
                Some(ident) => format!("{prefix} {}", ident.name),
                None => prefix.into(),
            },
        };
        owners.insert(SpanKey::from(item.span), EnclosingItem { span, name });
    }
    for function in &index.functions {
        owners.insert(
            SpanKey::from(function.span),
            EnclosingItem {
                span: file.item_span(function.span, &function.attrs),
                name: format!("fn {}", fn_path(file, function)),
            },
        );
    }
    let cx = Context {
        file,
        index: &index,
        uses,
        attrs,
        source,
        config,
        owners,
    };
    for attr in &index.attrs {
        let Some(meta) = attr.meta() else { continue };
        let cfg = match meta.path.segments.last() {
            Some(segment)
                if segment.ident.name.as_str() == "cfg"
                    || segment.ident.name.as_str() == "cfg_attr" =>
            {
                Some(())
            }
            _ => None,
        };
        if let Some(()) = cfg {
            let mut pending = vec![&meta];
            while let Some(meta) = pending.pop() {
                if let ast::MetaItemKind::Word = meta.kind
                    && meta.path.segments.len() == 1
                    && meta.path.segments[0].ident.name.as_str() == "test"
                {
                    let span = file.span(attr.span);
                    let item = cx.enclosing(span);
                    sink.emit("test-only-production-path", item.span, item.name, Report::new("test configuration changes the compiled implementation", span, "test-dependent compilation")
                        .help("Keep one production implementation and place tests in a separate tests directory."));
                    break;
                }
                if let ast::MetaItemKind::List(items) = &meta.kind {
                    for item in items {
                        if let ast::MetaItemInner::MetaItem(item) = item {
                            pending.push(item);
                        }
                    }
                }
            }
        }
    }
    if std::path::Path::new(source.name.as_ref())
        .components()
        .any(|part| part.as_os_str() == "src")
    {
        for function in &index.functions {
            if let Some(_) = function.attrs.iter().find(|attr| {
                match attr
                    .meta()
                    .and_then(|meta| meta.path.segments.last().map(|segment| segment.ident.name))
                {
                    Some(name) => name.as_str() == "test",
                    None => false,
                }
            }) {
                let span = file.span(function.node.ident.span);
                sink.emit(
                    "test-only-production-path",
                    file.item_span(function.span, &function.attrs),
                    fn_path(file, function),
                    Report::new(
                        "test code lives under src",
                        span,
                        "test belongs in a separate tests directory",
                    )
                    .help("Exercise the production API from integration tests."),
                );
            }
        }
    }
    let mut allowed_parent_imports = Vec::new();
    for (item, tree) in &index.imports {
        let test = is_test_path(&source.name).or_else(|| {
            index
                .test_scopes
                .iter()
                .find(|span| span.contains(item.span))
                .map(|_| ())
        });
        if let Some(range) = check_use(sink, &cx, item, tree, test) {
            allowed_parent_imports.push(range);
        }
    }
    for (item, ident, fields) in &index.structs {
        check_struct(sink, &cx, item, *ident, fields);
    }
    for (item, imp) in &index.impls {
        check_impl(sink, &cx, item, imp);
    }
    for function in &index.functions {
        check_fn(sink, &cx, function);
    }
    for expr in &index.exprs {
        check_expr(sink, &cx, expr);
    }
    for local in &index.locals {
        let ast::PatKind::Tuple(parts) = &local.pat.kind else {
            continue;
        };
        let width = parts.len();
        if width < cx.config.t.tuple_destructure_min_width || width == 0 {
            continue;
        }
        let item = cx.enclosing(file.span(local.span));
        let report = Report::new(
            format!("destructures a {width}-tuple"),
            file.span(local.pat.span),
            format!("{width} positional parts"),
        )
        .help(NAMED_FIELDS_HELP);
        sink.emit("tuple-return", item.span, item.name, report);
    }
    let mut offset = 0u32;
    for token in rustc_lexer::tokenize(file.text, rustc_lexer::FrontmatterAllowed::No) {
        let span = Span {
            start: offset,
            end: offset + token.len,
        };
        offset += token.len;
        if token.kind != rustc_lexer::TokenKind::Ident
            || &file.text[std::ops::Range::from(span)] != "super"
        {
            continue;
        }
        if let Some(_) = allowed_parent_imports
            .iter()
            .find(|allowed: &&Span| allowed.start <= span.start && allowed.end >= span.end)
        {
            continue;
        }
        let item = cx.enclosing(span);
        let report = Report::new(
            "`super` is only allowed in `use super::*` in tests",
            span,
            "parent-relative path",
        )
        .help("use qualified paths starting with `crate::` instead of `super`");
        sink.emit("super-path", item.span, item.name, report);
    }
}

#[derive(Default)]
struct Uses {
    calls: usize,
    as_value: Option<()>,
}

struct Function<'a> {
    node: &'a ast::Fn,
    attrs: ast::AttrVec,
    span: rustc_span::Span,
    owner: visit::FnCtxt,
    self_ty: Option<rustc_span::Span>,
}

#[derive(Default)]
struct Index<'a> {
    functions: Vec<Function<'a>>,
    structs: Vec<(&'a ast::Item, Ident, &'a [ast::FieldDef])>,
    impls: Vec<(&'a ast::Item, &'a ast::Impl)>,
    imports: Vec<(&'a ast::Item, &'a ast::UseTree)>,
    items: Vec<&'a ast::Item>,
    exprs: Vec<&'a ast::Expr>,
    locals: Vec<&'a ast::Local>,
    attrs: Vec<&'a ast::Attribute>,
    test_scopes: Vec<rustc_span::Span>,
    owner_for_span: FxHashMap<SpanKey, rustc_span::Span>,
    owner_for_source: FxHashMap<SpanKey, rustc_span::Span>,
    exprs_by_owner: FxHashMap<SpanKey, Vec<&'a ast::Expr>>,
    locals_by_owner: FxHashMap<SpanKey, Vec<&'a ast::Local>>,
    functions_by_self_ty: FxHashMap<SpanKey, Vec<usize>>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct SpanKey(u32, u32);

impl From<rustc_span::Span> for SpanKey {
    fn from(span: rustc_span::Span) -> Self {
        Self(span.lo().0, span.hi().0)
    }
}

struct Collector<'file, 'a> {
    file: &'file RustFile<'a>,
    index: Index<'a>,
    self_ty: Option<rustc_span::Span>,
    current_owner: Option<rustc_span::Span>,
}

impl Collector<'_, '_> {
    fn record_owner(&mut self, span: rustc_span::Span, owner: rustc_span::Span) {
        self.index.owner_for_span.insert(SpanKey::from(span), owner);
        let span = self.file.span(span);
        self.index
            .owner_for_source
            .insert(SpanKey(span.start, span.end), owner);
    }
}

impl<'a> Visitor<'a> for Collector<'_, 'a> {
    fn visit_item(&mut self, item: &'a ast::Item) {
        let previous_owner = self.current_owner;
        self.current_owner = Some(item.span);
        for attr in &item.attrs {
            self.record_owner(attr.span, item.span);
        }
        self.index.items.push(item);
        if let Some(()) = test_attributes(&item.attrs) {
            self.index.test_scopes.push(item.span);
        }
        let previous = self.self_ty;
        match &item.kind {
            ast::ItemKind::Struct(ident, _, ast::VariantData::Struct { fields, .. }) => {
                self.index.structs.push((item, *ident, fields))
            }
            ast::ItemKind::Use(tree) => self.index.imports.push((item, tree)),
            ast::ItemKind::Impl(imp) => {
                self.index.impls.push((item, imp));
                self.self_ty = Some(imp.self_ty.span);
            }
            _ => {}
        }
        visit::walk_item(self, item);
        self.self_ty = previous;
        self.current_owner = previous_owner;
    }
    fn visit_fn(
        &mut self,
        kind: visit::FnKind<'a>,
        attrs: &ast::AttrVec,
        span: rustc_span::Span,
        _: ast::NodeId,
    ) {
        if let visit::FnKind::Fn(owner, _, node) = kind {
            let previous_owner = self.current_owner;
            self.current_owner = Some(span);
            for attr in attrs {
                self.record_owner(attr.span, span);
            }
            let self_ty = match owner {
                visit::FnCtxt::Assoc(_) => self.self_ty,
                visit::FnCtxt::Free | visit::FnCtxt::Foreign => None,
            };
            if let Some(owner) = self_ty {
                self.index
                    .functions_by_self_ty
                    .entry(SpanKey::from(owner))
                    .or_default()
                    .push(self.index.functions.len());
            }
            self.index.functions.push(Function {
                node,
                attrs: attrs.clone(),
                span,
                owner,
                self_ty,
            });
            if let Some(()) = test_attributes(attrs) {
                self.index.test_scopes.push(span);
            }
            visit::walk_fn(self, kind);
            self.current_owner = previous_owner;
            return;
        }
        visit::walk_fn(self, kind);
    }
    fn visit_expr(&mut self, expr: &'a ast::Expr) {
        self.index.exprs.push(expr);
        if let Some(owner) = self.current_owner {
            self.record_owner(expr.span, owner);
            self.index
                .exprs_by_owner
                .entry(SpanKey::from(owner))
                .or_default()
                .push(expr);
        }
        visit::walk_expr(self, expr);
    }
    fn visit_local(&mut self, local: &'a ast::Local) {
        self.index.locals.push(local);
        if let Some(owner) = self.current_owner {
            self.record_owner(local.span, owner);
            self.index
                .locals_by_owner
                .entry(SpanKey::from(owner))
                .or_default()
                .push(local);
        }
        visit::walk_local(self, local);
    }
    fn visit_attribute(&mut self, attr: &'a ast::Attribute) {
        self.index.attrs.push(attr);
    }
}

impl<'a> Collector<'_, 'a> {
    fn collect(file: &RustFile<'a>) -> Index<'a> {
        let mut collector = Collector {
            file,
            index: Index::default(),
            self_ty: None,
            current_owner: None,
        };
        collector.visit_crate(file.krate);
        collector.index
    }
}

struct Context<'a, 'b> {
    file: &'a RustFile<'b>,
    index: &'a Index<'b>,
    uses: FxHashMap<String, Uses>,
    attrs: String,
    source: &'a SourceInput,
    config: &'a Config,
    owners: FxHashMap<SpanKey, EnclosingItem>,
}
#[derive(Clone)]
struct EnclosingItem {
    span: Span,
    name: String,
}
impl<'a> Context<'_, 'a> {
    // shapelint: allow(shallow-helper) The owner-index lookup is the single source-ownership boundary.
    fn expressions_for(&self, owner: rustc_span::Span) -> &[&'a ast::Expr] {
        self.index
            .exprs_by_owner
            .get(&SpanKey::from(owner))
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    fn expressions_for_expr(&self, expr: rustc_span::Span) -> &[&'a ast::Expr] {
        let Some(owner) = self.index.owner_for_span.get(&SpanKey::from(expr)) else {
            return &[];
        };
        self.expressions_for(*owner)
    }

    // shapelint: allow(shallow-helper) The owner-index lookup is the single source-ownership boundary.
    fn locals_for(&self, owner: rustc_span::Span) -> &[&'a ast::Local] {
        self.index
            .locals_by_owner
            .get(&SpanKey::from(owner))
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    fn enclosing(&self, span: Span) -> EnclosingItem {
        if let Some(owner) = self
            .index
            .owner_for_source
            .get(&SpanKey(span.start, span.end))
            && let Some(item) = self.owners.get(&SpanKey::from(*owner))
        {
            return item.clone();
        }
        if let Some(function) = self.index.functions.iter().rev().find(|function| {
            let at = self.file.item_span(function.span, &function.attrs);
            at.start <= span.start && at.end >= span.end
        }) {
            return EnclosingItem {
                span: self.file.item_span(function.span, &function.attrs),
                name: format!("fn {}", fn_path(self.file, function)),
            };
        }
        if let Some(item) = self.index.items.iter().rev().find(|item| {
            let at = self.file.item_span(item.span, &item.attrs);
            at.start <= span.start && at.end >= span.end
        }) {
            let prefix = match &item.kind {
                ast::ItemKind::Struct(..) => "struct",
                ast::ItemKind::Enum(..) => "enum",
                ast::ItemKind::Static(..) => "static",
                ast::ItemKind::TyAlias(..) => "type",
                ast::ItemKind::Trait(..) => "trait",
                ast::ItemKind::Use(..) => {
                    return EnclosingItem {
                        span: self.file.item_span(item.span, &item.attrs),
                        name: short(self.file.text(item.span), 60),
                    };
                }
                _ => "<item>",
            };
            let name = match item.kind.ident() {
                Some(ident) => format!("{prefix} {}", ident.name),
                None => prefix.into(),
            };
            return EnclosingItem {
                span: self.file.item_span(item.span, &item.attrs),
                name,
            };
        }
        EnclosingItem {
            span,
            name: "<item>".into(),
        }
    }
}

fn short(text: &str, max: usize) -> String {
    let text = text.split_whitespace().collect::<Vec<_>>().join(" ");
    if text.chars().count() <= max {
        text
    } else {
        format!("{}…", text.chars().take(max).collect::<String>())
    }
}
fn fn_path(file: &RustFile<'_>, function: &Function<'_>) -> String {
    let name = function.node.ident.name;
    match (function.owner, function.self_ty) {
        (visit::FnCtxt::Assoc(_), Some(self_ty)) => {
            format!(
                "{}::{name}",
                file.text(self_ty)
                    .split_whitespace()
                    .collect::<Vec<_>>()
                    .join(" ")
            )
        }
        _ => name.to_string(),
    }
}

fn check_use(
    sink: &mut Sink,
    cx: &Context<'_, '_>,
    item: &ast::Item,
    tree: &ast::UseTree,
    test: Option<()>,
) -> Option<Span> {
    let file = cx.file;
    let text = file
        .text(item.span)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    let private = match item.vis.kind {
        ast::VisibilityKind::Inherited => Some(()),
        _ => None,
    };
    let allowed = match (&tree.kind, tree.prefix.segments.as_slice(), private, test) {
        (ast::UseTreeKind::Glob(_), [segment], Some(()), Some(()))
            if segment.ident.name.as_str() == "super" =>
        {
            Some(file.span(tree.span()))
        }
        _ => None,
    };
    let mut pending = vec![tree];
    while let Some(tree) = pending.pop() {
        match &tree.kind {
            ast::UseTreeKind::Simple(Some(ident)) if ident.name.as_str() != "_" => {
                let end = file.span(ident.span).end;
                let from = file.span(tree.prefix.span).end;
                let Some(at) = file.text[from as usize..end as usize].find("as") else {
                    continue;
                };
                let span = Span {
                    start: from + at as u32,
                    end,
                };
                let report = Report::new(
                    format!("use import is renamed to {}", Code(file.text(ident.span))),
                    span,
                    "named import alias",
                )
                .help("use qualified paths instead of renaming imports");
                sink.emit(
                    "import-alias",
                    file.item_span(item.span, &item.attrs),
                    short(&text, 60),
                    report,
                );
            }
            ast::UseTreeKind::Glob(span) if let (Some(()), None) = (private, allowed) => {
                let report = Report::new(format!("{} imports every public name", Code(short(&text, 60))), file.span(*span), "glob")
                    .help("name the items you use; globs are allowed only for `use super::*` in tests and public re-exports");
                sink.emit(
                    "glob-import",
                    file.item_span(item.span, &item.attrs),
                    short(&text, 60),
                    report,
                );
            }
            ast::UseTreeKind::Nested { items, .. } => {
                pending.extend(items.iter().rev().map(|tree| &tree.inner))
            }
            _ => {}
        }
    }
    allowed
}

struct Param {
    name: String,
    ty: String,
    span: Span,
}

#[derive(Default)]
struct ReturnTypes {
    widest_tuple: usize,
}

impl<'ast> Visitor<'ast> for ReturnTypes {
    fn visit_ty(&mut self, ty: &'ast ast::Ty) {
        match &ty.kind {
            ast::TyKind::Tup(fields) => self.widest_tuple = self.widest_tuple.max(fields.len()),
            _ => {}
        }
        visit::walk_ty(self, ty);
    }
}
const STRINGISH_TYPES: &[&str] = &[
    "&str",
    "String",
    "&String",
    "Option<String>",
    "Option<&str>",
    "&'static str",
];
const NAMED_FIELDS_HELP: &str =
    "use a struct with named fields, or an enum if the parts are alternatives";
fn identity(name: &str) -> Option<()> {
    if [
        "source",
        "destination",
        "topic",
        "group_id",
        "consumer_group",
        "bucket",
        "tenant",
    ]
    .contains(&name)
        || name.ends_with("_topic")
    {
        Some(())
    } else {
        match name.strip_suffix("_id") {
            Some(stem) if !stem.is_empty() => Some(()),
            Some(_) | None => None,
        }
    }
}
fn check_fn(sink: &mut Sink, cx: &Context<'_, '_>, function: &Function<'_>) {
    let file = cx.file;
    let node = function.node;
    let name = node.ident.name.as_str();
    let path = fn_path(file, function);
    let item = EnclosingItem {
        span: file.item_span(function.span, &function.attrs),
        name: format!("fn {path}"),
    };
    let params: Vec<_> = node
        .sig
        .decl
        .inputs
        .iter()
        .filter(|param| !param.is_self())
        .map(|param| Param {
            name: file
                .text(param.pat.span)
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" "),
            ty: file
                .text(param.ty.span)
                .split_whitespace()
                .collect::<Vec<_>>()
                .join(" "),
            span: file.span(param.span),
        })
        .collect();
    let ret_ty = match &node.sig.decl.output {
        ast::FnRetTy::Ty(ty) => Some(ty.as_ref()),
        ast::FnRetTy::Default(_) => None,
    };
    let mut returns = ReturnTypes::default();
    if let Some(ty) = ret_ty {
        returns.visit_ty(ty);
    }
    let ret = ret_ty.map_or(String::new(), |ty| {
        file.text(ty.span)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    });
    let trait_owner = match function.owner {
        visit::FnCtxt::Assoc(
            visit::AssocCtxt::Trait | visit::AssocCtxt::Impl { of_trait: true },
        ) => Some(()),
        _ => None,
    };
    let trait_impl = match function.owner {
        visit::FnCtxt::Assoc(visit::AssocCtxt::Impl { of_trait: true }) => Some(()),
        _ => None,
    };
    if let None = trait_owner
        && name != "main"
    {
        if let None = function
            .attrs
            .iter()
            .find(|attr| file.text(attr.span).contains("test"))
        {
            shallow_helper(sink, cx, function, &path, &item);
        }
        if !name.starts_with("assert") {
            check_passthrough(sink, cx, function, &path, &params, &ret, &item);
        }
    }
    if let Some(ret_ty) = ret_ty {
        let widest = returns.widest_tuple;
        if let None = trait_impl
            && widest >= cx.config.t.tuple_return_min_width
            && widest > 0
        {
            let report = Report::new(
                format!("{} returns a {widest}-tuple", Code(&path)),
                file.span(ret_ty.span),
                format!("{widest}-tuple"),
            )
            .help(NAMED_FIELDS_HELP);
            sink.emit("tuple-return", item.span, item.name.clone(), report);
        }
    }
    if function.owner == visit::FnCtxt::Free
        && name.starts_with("parse_")
        && params.len() == 1
        && ["&str", "&String", "String"].contains(&params[0].ty.as_str())
        && (ret.starts_with("Result<") || ret.starts_with("Option<"))
    {
        let report = Report::new(
            format!("{} takes {} and returns {}", Code(&path), Code(&params[0].ty), Code(short(&ret, 50))),
            file.span(node.ident.span),
            "named parser",
        )
        .help("Use `FromStr` for the canonical text format of a type this crate owns. Keep a named parser for a specific radix or format. Check existing implementations before changing callers.");
        sink.emit("std-trait-fn", item.span, item.name.clone(), report);
    }
    let hits: Vec<_> = params
        .iter()
        .filter(|param| match identity(&param.name) {
            Some(()) => STRINGISH_TYPES.contains(&param.ty.as_str()),
            None => false,
        })
        .collect();
    if let Some((first, rest)) = hits.split_first() {
        let names = hits
            .iter()
            .map(|param| Code(&param.name).to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let mut report = Report::new(
            format!(
                "{} takes identity values as plain strings ({names})",
                Code(&path)
            ),
            first.span,
            "string identity",
        );
        for param in rest {
            report = report.label(param.span, "string identity");
        }
        sink.emit("identity-string", item.span, item.name, report.help("give each identity a newtype so it can't be swapped with or mistaken for another string"));
    }
}

fn shallow_helper(
    sink: &mut Sink,
    cx: &Context<'_, '_>,
    function: &Function<'_>,
    path: &str,
    item: &EnclosingItem,
) {
    let Some(body) = &function.node.body else {
        return;
    };
    let [statement] = body.stmts.as_slice() else {
        return;
    };
    let tail = match &statement.kind {
        ast::StmtKind::Expr(expr) | ast::StmtKind::Semi(expr) => expr,
        _ => return,
    };
    match &tail.kind {
        ast::ExprKind::MacCall(_) => return,
        ast::ExprKind::Struct(record) if cx.file.text(record.path.span) == "Self" => return,
        _ => {}
    }
    if cx.source.name.contains("/benches/")
        || cx.source.name.contains("/examples/")
        || cx.file.text(body.span).contains("unsafe")
    {
        return;
    }
    let nodes: Vec<_> = cx
        .expressions_for(function.span)
        .iter()
        .filter(|expr| tail.span.contains(expr.span))
        .collect();
    struct Size(usize);
    impl<'a> Visitor<'a> for Size {
        fn visit_id(&mut self, _: ast::NodeId) {
            self.0 += 1;
        }
        fn visit_ident(&mut self, _: &'a Ident) {
            self.0 += 1;
        }
        fn visit_path(&mut self, path: &'a ast::Path) {
            self.0 += 1;
            visit::walk_path(self, path);
        }
        fn visit_expr(&mut self, expr: &'a ast::Expr) {
            // Argument lists have syntax of their own even though rustc stores them inline.
            if let ast::ExprKind::Call(..) | ast::ExprKind::MethodCall(..) = expr.kind {
                self.0 += 1;
            }
            visit::walk_expr(self, expr);
        }
    }
    let mut size = Size(0);
    size.visit_expr(tail);
    if size.0 > cx.config.t.shallow_max_nodes {
        return;
    }
    for node in nodes {
        match &node.kind {
            ast::ExprKind::If(..)
            | ast::ExprKind::Match(..)
            | ast::ExprKind::Loop(..)
            | ast::ExprKind::While(..)
            | ast::ExprKind::ForLoop(..)
            | ast::ExprKind::Try(..) => return,
            ast::ExprKind::Block(block, _) => {
                if let Some(_) = block.stmts.iter().find(|stmt| match stmt.kind {
                    ast::StmtKind::Expr(_) => false,
                    _ => true,
                }) {
                    return;
                }
            }
            _ => {}
        }
    }
    let name = function.node.ident.name.as_str();
    if cx.attrs.contains(&format!("\"{name}\"")) || cx.attrs.contains(&format!("::{name}\"")) {
        return;
    }
    let (calls, as_value) = cx
        .uses
        .get(name)
        .map_or((0, None), |usage| (usage.calls, usage.as_value));
    match function.owner {
        visit::FnCtxt::Assoc(visit::AssocCtxt::Impl { of_trait: false }) => {
            if let Some(Uses {
                as_value: Some(()), ..
            }) = cx.uses.get(path)
            {
                return;
            }
        }
        _ if let Some(()) = as_value => return,
        _ => {}
    }
    let report = Report::new(format!("{} only wraps one expression", Code(path)), cx.file.span(function.node.ident.span), "one-expression helper")
        .label(cx.file.span(tail.span), "the whole body")
        .note(format!("{calls} call site(s) in this file"))
        .help("inline it at the call sites, unless the name states a domain concept or the function owns an invariant");
    sink.emit("shallow-helper", item.span, item.name.clone(), report);
}

fn check_passthrough(
    sink: &mut Sink,
    cx: &Context<'_, '_>,
    function: &Function<'_>,
    path: &str,
    params: &[Param],
    ret: &str,
    item: &EnclosingItem,
) {
    if !(ret.starts_with("Result") || ret.contains("::Result")) {
        return;
    }
    let Some(body) = &function.node.body else {
        return;
    };
    let file = cx.file;
    let names: FxHashSet<_> = params.iter().map(|p| p.name.as_str()).collect();
    enum Success {
        Unit,
        Inputs,
    }
    let mut oks = Vec::new();
    let mut fails = None;
    let mut shape_match = None;
    let closures: Vec<_> = cx
        .expressions_for(function.span)
        .iter()
        .filter_map(|expr| match &expr.kind {
            ast::ExprKind::Closure(_) => Some(expr.span),
            _ => None,
        })
        .collect();
    let expressions = cx
        .expressions_for(function.span)
        .iter()
        .filter(|expr| body.span.contains(expr.span));
    for expr in expressions {
        match &expr.kind {
            ast::ExprKind::Call(callee, arguments) if file.text(callee.span) == "Ok" => {
                if let Some(_) = closures.iter().find(|closure| closure.contains(expr.span)) {
                    continue;
                }
                let [arg] = arguments.as_slice() else { return };
                let success = match &arg.kind {
                    ast::ExprKind::Tup(parts) if parts.is_empty() => Success::Unit,
                    ast::ExprKind::Tup(parts)
                        if parts
                            .iter()
                            .all(|part| names.contains(file.text(part.span))) =>
                    {
                        Success::Inputs
                    }
                    _ if names.contains(file.text(arg.span)) => Success::Inputs,
                    _ => return,
                };
                oks.push((file.span(expr.span), success));
            }
            ast::ExprKind::Try(_) => fails = Some(()),
            ast::ExprKind::Call(callee, _) if file.text(callee.span) == "Err" => fails = Some(()),
            ast::ExprKind::MacCall(mac)
                if ["bail", "ensure", "anyhow::bail", "anyhow::ensure"]
                    .contains(&file.text(mac.path.span)) =>
            {
                fails = Some(())
            }
            ast::ExprKind::Match(value, arms, _) if file.text(value.span).starts_with('(') => {
                if let Some(_) = arms.iter().find(|arm| {
                    let pat = file.text(arm.pat.span);
                    pat.contains("None") && pat.contains("Some(")
                }) {
                    shape_match = Some(value.span);
                }
            }
            _ => {}
        }
    }
    if oks.is_empty() {
        return;
    }
    let Some(()) = fails else { return };
    let nonunit = oks.iter().find(|(_, success)| match success {
        Success::Unit => false,
        Success::Inputs => true,
    });
    let name = function.node.ident.name.as_str();
    if let (None, None, None) = (
        nonunit,
        shape_match,
        [
            "validate", "check", "verify", "ensure", "require", "is_valid",
        ]
        .iter()
        .find(|prefix| name.starts_with(*prefix)),
    ) {
        return;
    }
    let (message, primary) = match nonunit {
        None => (
            format!("{} checks its input and returns `Ok(())`", Code(path)),
            "the check's result is discarded",
        ),
        Some(_) => (
            format!(
                "{} checks its inputs and returns them unchanged",
                Code(path)
            ),
            "callers keep the unrefined values",
        ),
    };
    let mut report = Report::new(message, file.span(function.node.ident.span), primary);
    for (span, success) in oks {
        report = report.label(
            span,
            match success {
                Success::Unit => "returns nothing learned",
                Success::Inputs => "returns its inputs",
            },
        );
    }
    if let Some(span) = shape_match {
        report = report.label(
            file.span(span),
            "matches a discriminator against Some/None shapes",
        );
    }
    report = report.help("return a type that records the check (`TryFrom`, `FromStr`, or a constructor), so callers can't keep the unchecked value");
    if let Some(_) = shape_match {
        report =
            report.help("make each legal shape an enum variant that carries exactly its fields");
    }
    let callers = cx.uses.get(name).map_or(0, |usage| usage.calls);
    if callers > 1 {
        report = report.note(format!(
            "called {callers} times in this file; each call repeats the check"
        ));
    }
    sink.emit("check-passthrough", item.span, item.name.clone(), report);
}

fn check_struct(
    sink: &mut Sink,
    cx: &Context<'_, '_>,
    node: &ast::Item,
    ident: Ident,
    fields: &[ast::FieldDef],
) {
    let file = cx.file;
    let name = ident.name.as_str();
    let item = EnclosingItem {
        span: file.item_span(node.span, &node.attrs),
        name: format!("struct {name}"),
    };
    let deserialize = node
        .attrs
        .iter()
        .find(|attr| file.text(attr.span).contains("Deserialize"));
    let mut stems: IndexMap<String, Vec<(&ast::FieldDef, String, Option<()>)>> = IndexMap::new();
    let mut identities = Vec::new();
    for field in fields {
        let Some(field_ident) = field.ident else {
            continue;
        };
        let fname = field_ident.name.to_string();
        let ty = file
            .text(field.ty.span)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        if let Some(_) = deserialize
            && let Some(_) = field
                .attrs
                .iter()
                .find(|attr| file.text(attr.span).contains("flatten"))
            && (ty.contains("Map<String, String>") || ty.contains("Map<String,String>"))
        {
            let report = Report::new(format!("{} collects unmodeled keys into a flattened string map", Code(format!("{name}.{fname}"))), file.span(field_ident.span), "catch-all for config the type doesn't model")
                .help("deserialize known keys into typed fields or variants; keep the map only for true extensions");
            sink.emit(
                "config-bag",
                item.span,
                format!("{}.{fname}", item.name),
                report,
            );
        }
        if let Some(suffix) = [
            "_ms", "_us", "_ns", "_secs", "_s", "_millis", "_micros", "_nanos",
        ]
        .iter()
        .find(|suffix| fname.ends_with(*suffix) && fname.len() > suffix.len())
        {
            let optional = ty.starts_with("Option<").then_some(());
            stems
                .entry(fname[..fname.len() - suffix.len()].to_string())
                .or_default()
                .push((field, fname.clone(), optional));
        }
        if STRINGISH_TYPES.contains(&ty.as_str())
            && let Some(()) = identity(&fname)
        {
            identities.push((field, fname));
        }
    }
    for (stem, members) in stems {
        let [_, _, ..] = members.as_slice() else {
            continue;
        };
        let Some(_) = members.iter().find(|(_, _, optional)| match optional {
            Some(()) => true,
            None => false,
        }) else {
            continue;
        };
        let names = members
            .iter()
            .map(|(_, name, _)| Code(name).to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let mut report = Report::new(
            format!(
                "{} has fields for {} with different unit suffixes ({names})",
                Code(name),
                Code(&stem)
            ),
            file.span(ident.span),
            format!("{} fields share the stem {}", members.len(), Code(&stem)),
        );
        for (field, _, optional) in members {
            report = report.label(
                file.span(field.span),
                match optional {
                    Some(()) => "optional field",
                    None => "required field",
                },
            );
        }
        sink.emit(
            "unit-fields",
            item.span,
            item.name.clone(),
            report.help(
                "Check how producers and consumers combine these fields. Parse alternative encodings into one typed value. Keep additive components distinct when both contribute.",
            ),
        );
    }
    if identities.len() >= cx.config.t.identity_fields_min && !identities.is_empty() {
        let names = identities
            .iter()
            .map(|(_, name)| Code(name).to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let mut report = Report::new(
            format!(
                "{} stores {} identity values as plain strings ({names})",
                Code(name),
                identities.len()
            ),
            file.span(ident.span),
            "string identities",
        );
        for (field, _) in identities {
            report = report.label(file.span(field.span), "string identity");
        }
        sink.emit(
            "identity-string",
            item.span,
            item.name,
            report.help(
                "give each identity a newtype so they can't be swapped or mixed with other strings",
            ),
        );
    }
}

fn check_impl(sink: &mut Sink, cx: &Context<'_, '_>, item: &ast::Item, imp: &ast::Impl) {
    if let Some(_) = imp.of_trait {
        return;
    }
    let file = cx.file;
    let self_text = file
        .text(imp.self_ty.span)
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ");
    let Some(base) = self_text.split('<').next() else {
        return;
    };
    let base = base.trim();
    let Some((strukt, _, fields)) = cx
        .index
        .structs
        .iter()
        .find(|(_, ident, _)| ident.name.as_str() == base)
    else {
        return;
    };
    let methods: Vec<_> = cx
        .index
        .functions_by_self_ty
        .get(&SpanKey::from(imp.self_ty.span))
        .into_iter()
        .flat_map(|indices| indices.iter().map(|&index| &cx.index.functions[index]))
        .filter(|function| item.span.contains(function.span))
        .collect();
    if let Some(_) = strukt
        .attrs
        .iter()
        .find(|attr| file.text(attr.span).contains("Deserialize"))
    {
        for method in &methods {
            let Some(body) = &method.node.body else {
                continue;
            };
            let nodes: Vec<_> = cx
                .expressions_for(method.span)
                .iter()
                .filter(|expr| body.span.contains(expr.span))
                .collect();
            let has_get = nodes.iter().find(|expr| match &expr.kind {
                ast::ExprKind::MethodCall(call) => call.seg.ident.name.as_str() == "get",
                _ => false,
            });
            let mut sites = Vec::new();
            for expr in &nodes {
                match &expr.kind {
                    ast::ExprKind::Call(callee, _)
                        if file.text(callee.span).ends_with("Regex::new") =>
                    {
                        sites.push((expr.span, "compiles a pattern at use time"))
                    }
                    ast::ExprKind::MethodCall(call) => match call.seg.ident.name.as_str() {
                        "split" => sites.push((call.seg.ident.span, "splits a string at use time")),
                        "parse" => sites.push((call.seg.ident.span, "parses at use time")),
                        _ => {}
                    },
                    ast::ExprKind::MacCall(mac)
                        if let Some(_) = has_get
                            && file.text(mac.path.span) == "format" =>
                    {
                        sites.push((expr.span, "builds a lookup key at use time"))
                    }
                    _ => {}
                }
            }
            if sites.is_empty() {
                continue;
            }
            let path = fn_path(file, method);
            let mut report = Report::new(
                format!("{} re-parses deserialized config at use time", Code(&path)),
                file.span(method.node.ident.span),
                "parses config after loading",
            );
            for (span, why) in sites {
                report = report.label(file.span(span), why);
            }
            sink.emit("config-bag", file.item_span(method.span, &method.attrs), format!("fn {path}"), report.help("move this into deserialization (typed variants, compiled patterns) so bad config fails when it loads"));
        }
    }
    for field in *fields {
        if !file.text(field.ty.span).starts_with("Option<") {
            continue;
        }
        let Some(ident) = field.ident else { continue };
        let receiver = format!("self.{}", ident.name);
        let mut proofs = Vec::new();
        for method in &methods {
            let Some(body) = &method.node.body else {
                continue;
            };
            let locals = cx.locals_for(method.span).iter();
            for local in locals {
                if let ast::LocalKind::InitElse(init, _) = &local.kind
                    && file.text(init.span).replace(' ', "").starts_with(&receiver)
                {
                    proofs.push(init.span);
                }
            }
            let expressions = cx
                .expressions_for(method.span)
                .iter()
                .filter(|expr| body.span.contains(expr.span));
            for expr in expressions {
                if let ast::ExprKind::MethodCall(call) = &expr.kind {
                    let on = file.text(call.receiver.span).replace(' ', "");
                    if ["ok_or", "ok_or_else", "expect", "unwrap"]
                        .contains(&call.seg.ident.name.as_str())
                        && (on == receiver || on == format!("{receiver}.as_ref()"))
                    {
                        proofs.push(expr.span);
                    }
                }
            }
        }
        if proofs.is_empty() {
            continue;
        }
        proofs.sort_by_key(|span| span.lo());
        let mut report = Report::new(
            format!(
                "methods of {} re-check that {} is `Some`",
                Code(base),
                Code(&receiver)
            ),
            file.span(imp.self_ty.span),
            "optional state",
        );
        for span in proofs {
            report = report.label(file.span(span), "checked again here");
        }
        sink.emit("optional-state", file.item_span(item.span, &item.attrs), format!("impl {base}"), report.help("model the phases as an enum, or pass the present value, so code that needs it can't run without it"));
    }
}

fn check_expr(sink: &mut Sink, cx: &Context<'_, '_>, expr: &ast::Expr) {
    let file = cx.file;
    let item = cx.enclosing(file.span(expr.span));
    match &expr.kind {
        ast::ExprKind::ForLoop(for_loop) => {
            let ast::ExprKind::MethodCall(outer) = &for_loop.iter.kind else {
                return;
            };
            let mut depth = 0;
            let mut current = for_loop.iter.as_ref();
            while let ast::ExprKind::MethodCall(call) = &current.kind {
                depth += 1;
                current = &call.receiver;
            }
            if depth < cx.config.t.for_chain_min_calls {
                return;
            }
            let report = Report::new(
                format!("`for` header builds a {depth}-call iterator chain"),
                file.span(outer.seg.ident.span),
                "chain ends here",
            )
            .label(file.span(for_loop.iter.span), "iterator chain")
            .help("bind the chain to a named variable, then loop over the variable");
            sink.emit("for-chain", item.span, item.name, report);
        }
        ast::ExprKind::MethodCall(call) => match call.seg.ident.name.as_str() {
            "for_each" => {
                let report = Report::new(
                    "`for_each` used where a `for` loop would do",
                    file.span(call.seg.ident.span),
                    "for_each",
                )
                .help("use a `for` loop");
                sink.emit("for-chain", item.span, item.name, report);
            }
            "concat" => {
                let ast::ExprKind::Array(_) = &call.receiver.kind else {
                    return;
                };
                let pieces: Vec<_> = cx
                    .expressions_for_expr(expr.span)
                    .iter()
                    .filter(|expr| call.receiver.span.contains(expr.span))
                    .filter_map(|expr| match &expr.kind {
                        ast::ExprKind::MethodCall(piece)
                            if ["to_be_bytes", "to_le_bytes", "to_ne_bytes"]
                                .contains(&piece.seg.ident.name.as_str()) =>
                        {
                            Some(piece.seg.ident.span)
                        }
                        _ => None,
                    })
                    .collect();
                if pieces.len() < cx.config.t.byte_format_min_pieces || pieces.is_empty() {
                    return;
                }
                let mut report = Report::new(
                    format!(
                        "byte format assembled by hand from {} `to_*_bytes()` pieces",
                        pieces.len()
                    ),
                    file.span(call.seg.ident.span),
                    "assembled here",
                );
                for span in pieces {
                    report = report.label(file.span(span), "piece");
                }
                sink.emit("byte-format", item.span, item.name, report.help("give the format a type with one encoder and reuse it (search for an existing one first)"));
            }
            _ => {}
        },
        ast::ExprKind::Call(callee, _) if file.text(callee.span).ends_with("spawn_blocking") => {
            if let Some(_) = cx.source.text.nearby_comment(
                file.span(expr.span).start,
                cx.config.t.blocking_comment_lines,
            ) {
                return;
            }
            let report = Report::new("`spawn_blocking` has no comment saying which call blocks", file.span(callee.span), "offloaded to a blocking thread")
                .help("add a comment naming the blocking call, or drop the offload if nothing inside blocks");
            sink.emit("blocking-rationale", item.span, item.name, report);
        }
        _ => {}
    }
}
