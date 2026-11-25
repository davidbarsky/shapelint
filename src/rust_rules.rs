//! Source-shape rules over rustc's unexpanded AST.

use rustc_ast::{
    ast,
    visit::{self, Visitor},
};
use rustc_hash::FxHashMap;

use crate::diagnostic::{Report, Sink};
use crate::rust_syntax::{RustFile, is_test_path, test_attributes};
use crate::suggest::Code;
use crate::{Config, SourceInput, Span};

pub(crate) fn lint(sink: &mut Sink, file: &RustFile<'_>, source: &SourceInput, config: &Config) {
    let index = Collector::collect(file);
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
    imports: Vec<(&'a ast::Item, &'a ast::UseTree)>,
    items: Vec<&'a ast::Item>,
    exprs: Vec<&'a ast::Expr>,
    locals: Vec<&'a ast::Local>,
    attrs: Vec<&'a ast::Attribute>,
    test_scopes: Vec<rustc_span::Span>,
    owner_for_source: FxHashMap<SpanKey, rustc_span::Span>,
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
            ast::ItemKind::Use(tree) => self.index.imports.push((item, tree)),
            ast::ItemKind::Impl(imp) => {
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
        }
        visit::walk_expr(self, expr);
    }
    fn visit_local(&mut self, local: &'a ast::Local) {
        self.index.locals.push(local);
        if let Some(owner) = self.current_owner {
            self.record_owner(local.span, owner);
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
    config: &'a Config,
    owners: FxHashMap<SpanKey, EnclosingItem>,
}
#[derive(Clone)]
struct EnclosingItem {
    span: Span,
    name: String,
}
impl<'a> Context<'_, 'a> {
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
const NAMED_FIELDS_HELP: &str =
    "use a struct with named fields, or an enum if the parts are alternatives";
fn check_fn(sink: &mut Sink, cx: &Context<'_, '_>, function: &Function<'_>) {
    let file = cx.file;
    let node = function.node;
    let name = node.ident.name.as_str();
    let path = fn_path(file, function);
    let item = EnclosingItem {
        span: file.item_span(function.span, &function.attrs),
        name: format!("fn {path}"),
    };
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
    let trait_impl = match function.owner {
        visit::FnCtxt::Assoc(visit::AssocCtxt::Impl { of_trait: true }) => Some(()),
        _ => None,
    };
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
    let parameter_type = node.sig.decl.inputs.first().map_or(String::new(), |param| {
        file.text(param.ty.span)
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ")
    });
    if function.owner == visit::FnCtxt::Free
        && name.starts_with("parse_")
        && node.sig.decl.inputs.len() == 1
        && ["&str", "&String", "String"].contains(&parameter_type.as_str())
        && (ret.starts_with("Result<") || ret.starts_with("Option<"))
    {
        let report = Report::new(
            format!("{} takes {} and returns {}", Code(&path), Code(&parameter_type), Code(short(&ret, 50))),
            file.span(node.ident.span),
            "named parser",
        )
        .help("Use `FromStr` for the canonical text format of a type this crate owns. Keep a named parser for a specific radix or format. Check existing implementations before changing callers.");
        sink.emit("std-trait-fn", item.span, item.name.clone(), report);
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
            _ => {}
        },
        _ => {}
    }
}
