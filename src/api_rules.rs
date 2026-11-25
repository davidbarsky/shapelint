use rustc_ast::token::TokenKind;
use rustc_ast::{
    ast,
    visit::{self, AssocCtxt, FnCtxt, FnKind, Visitor},
};
use rustc_span::sym;

use crate::Span;
use crate::diagnostic::{Report, Sink};
use crate::expression_rules::{compact, tokens};
use crate::rust_syntax::RustFile;

pub(crate) fn lint(sink: &mut Sink, file: &RustFile<'_>) {
    let mut visitor = Apis {
        sink,
        file,
        functions: Vec::new(),
        scope: Vec::new(),
        implementation: None,
        item: None,
    };
    visitor.visit_crate(file.krate);
    let mut groups: rustc_hash::FxHashMap<(&[String], &str), Vec<&Function<'_>>> =
        rustc_hash::FxHashMap::default();
    for function in &visitor.functions {
        let name = function.function.ident.name.as_str();
        let base = match api_stem(name) {
            Some(base) => base,
            None => name,
        };
        groups
            .entry((&function.scope, base))
            .or_default()
            .push(function);
    }
    for function in &visitor.functions {
        let name = function.function.ident.name.as_str();
        if let Some(base) = api_stem(name)
            && let Some(siblings) = groups.get(&(function.scope.as_slice(), base))
            && let Some(other) = siblings.iter().find(|other| other.span != function.span)
        {
            let report = Report::new(
                format!("`{name}` and `{}` share an API name stem", other.path),
                file.span(function.function.ident.span), "variant entry point",
            ).label(file.span(other.function.ident.span), "related entry point")
                .help("Compare the signatures and callers. Consolidate the entry points if one operation serves both. Keep separate APIs when their behavior or external contracts differ.");
            visitor.sink.emit(
                "parallel-api",
                function.item_span,
                format!("fn {}", function.path),
                report,
            );
        }
    }
}

struct Function<'a> {
    function: &'a ast::Fn,
    span: rustc_span::Span,
    path: String,
    scope: Vec<String>,
    item_span: Span,
}

struct Apis<'a, 'b, 'c, 'ast> {
    sink: &'a mut Sink<'b>,
    file: &'a RustFile<'c>,
    functions: Vec<Function<'ast>>,
    scope: Vec<String>,
    implementation: Option<String>,
    item: Option<(Span, String)>,
}

impl Apis<'_, '_, '_, '_> {
    fn emit(&mut self, rule: &'static str, fallback: rustc_span::Span, report: Report) {
        let (span, name) = match &self.item {
            Some((span, name)) => (*span, name.clone()),
            None => (self.file.span(fallback), "<item>".to_owned()),
        };
        self.sink.emit(rule, span, name, report);
    }
}

impl<'ast> Visitor<'ast> for Apis<'_, '_, '_, 'ast> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        if let ast::ItemKind::Use(_) = &item.kind {
            return;
        }
        let previous = self.item.clone();
        let implementation = self.implementation.clone();
        let depth = self.scope.len();
        if let Some(named) = self.file.named_item(item) {
            self.item = Some(named);
        }
        match &item.kind {
            ast::ItemKind::Impl(value) => {
                let owner = compact(self.file.text(value.self_ty.span));
                self.scope.push(format!("impl:{owner}"));
                self.implementation = Some(owner);
            }
            ast::ItemKind::Mod(_, name, _) => self.scope.push(format!("mod:{name}")),
            ast::ItemKind::TyAlias(value) => {
                if let Some(attr) = item
                    .attrs
                    .iter()
                    .find(|attr| attr.has_name(sym::deprecated))
                {
                    let report = Report::new("deprecated type alias retains an alternate API name", self.file.span(value.ident.span), "compatibility alias")
                        .label(self.file.span(attr.span), "deprecated here")
                        .help("Check published API users and the supported migration window. Keep the alias while consumers depend on it. Once they have migrated, remove it.");
                    self.emit("compatibility-scaffolding", item.span, report);
                }
            }
            _ => {}
        }
        visit::walk_item(self, item);
        self.scope.truncate(depth);
        self.implementation = implementation;
        self.item = previous;
    }

    fn visit_fn(
        &mut self,
        kind: FnKind<'ast>,
        attrs: &ast::AttrVec,
        span: rustc_span::Span,
        _: ast::NodeId,
    ) {
        let previous = self.item.clone();
        let depth = self.scope.len();
        if let FnKind::Fn(context, _, function) = kind {
            let path = match (&self.implementation, context) {
                (Some(owner), FnCtxt::Assoc(_)) => format!("{owner}::{}", function.ident),
                _ => function.ident.to_string(),
            };
            self.item = Some((self.file.item_span(span, attrs), format!("fn {path}")));
            if let FnCtxt::Free | FnCtxt::Assoc(AssocCtxt::Impl { of_trait: false }) = context {
                self.functions.push(Function {
                    function,
                    span,
                    path: path.clone(),
                    scope: self.scope.clone(),
                    item_span: self.file.item_span(span, attrs),
                });
                let name = function.ident.name.as_str();
                let count = function
                    .sig
                    .decl
                    .inputs
                    .iter()
                    .filter(|param| !param.is_self())
                    .count();
                if let ast::FnRetTy::Ty(ret) = &function.sig.decl.output {
                    let conversion = match (name, count, function.sig.decl.has_self()) {
                        ("as_str", 0, true) => Some("AsRef<str>"),
                        ("from_iter", 1, false) => Some("FromIterator"),
                        ("into_iter", 0, true) => Some("IntoIterator"),
                        ("to_bytes" | "into_bytes", 0, true) => {
                            Some("From / TryFrom, or Encoder for a framed protocol")
                        }
                        (_, 0, true) if name.starts_with("to_") || name.starts_with("into_") => {
                            Some("From / TryFrom")
                        }
                        (_, 1, false)
                            if name.starts_with("from_")
                                || name.starts_with("try_from_")
                                || name.contains("_to_") =>
                        {
                            Some("From / TryFrom")
                        }
                        (_, 1, false)
                            if name.starts_with("encode_") || name.starts_with("decode_") =>
                        {
                            Some("From / TryFrom, or Encoder / Decoder for a framed protocol")
                        }
                        (_, 1, false)
                            if context == FnCtxt::Assoc(AssocCtxt::Impl { of_trait: false })
                                && name.starts_with("parse_") =>
                        {
                            Some("FromStr / TryFrom")
                        }
                        _ => None,
                    };
                    if let Some(traits) = conversion {
                        let report = Report::new(format!("`{path}` has a representation-conversion shape"), self.file.span(function.ident.span), "bespoke conversion entry point")
                            .label(self.file.span(ret.span), "converted representation")
                            .help(format!("consider `{traits}` on the owning type; check ownership, lifetimes, and orphan rules before replacing this API"));
                        self.emit("conversion-trait", span, report);
                    }
                }
                let marker = attrs
                    .iter()
                    .find(|attr| attr.has_name(sym::deprecated))
                    .map(|_| "is marked deprecated")
                    .or_else(|| {
                        (name.starts_with("legacy_") || name.ends_with("_compat"))
                            .then_some("has a compatibility name")
                    });
                if let Some(marker) = marker
                    && let Some(body) = &function.body
                    && let [statement] = body.stmts.as_slice()
                    && let ast::StmtKind::Expr(expr) | ast::StmtKind::Semi(expr) = &statement.kind
                    && let ast::ExprKind::Call(..) | ast::ExprKind::MethodCall(_) = &expr.kind
                {
                    let report = Report::new(format!("`{name}` {marker} and its body consists of a call"), self.file.span(function.ident.span), marker)
                        .label(self.file.span(expr.span), "call expression")
                        .help("Check whether this call forwards to an equivalent supported API or implements distinct behavior. Keep behavior and entry points that supported clients need. Migrate callers before removing a redundant wrapper.");
                    self.emit("compatibility-scaffolding", span, report);
                }
            }
            self.scope.push(format!("fn:{}", span.lo().0));
        }
        visit::walk_fn(self, kind);
        self.scope.truncate(depth);
        self.item = previous;
    }

    fn visit_path(&mut self, path: &'ast ast::Path) {
        for segment in &path.segments {
            if let "BTreeMap" | "BTreeSet" = segment.ident.name.as_str() {
                let report = Report::new(format!("this path names `{}`", segment.ident), self.file.span(segment.ident.span), "collection named here")
                    .help("Resolve the type and trace its uses. Keep the tree for key ranges or key-ordered output. For lookup alone, consider a hash collection. For insertion order, consider an insertion-ordered collection.")
                    .note("The source check matches the written type name. Callers determine the ordering contract.");
                self.emit("collection-choice", path.span, report);
            }
        }
        visit::walk_path(self, path);
    }

    fn visit_attribute(&mut self, attr: &'ast ast::Attribute) {
        if attr.has_name(rustc_span::Symbol::intern("serde"))
            && let ast::AttrKind::Normal(normal) = &attr.kind
            && let ast::AttrArgs::Delimited(args) = &normal.item.args
        {
            let tokens = tokens(&args.tokens);
            for pair in tokens.windows(2) {
                if let TokenKind::Ident(name, _) = pair[0].kind
                    && name.as_str() == "alias"
                    && pair[1].kind == TokenKind::Eq
                {
                    let report = Report::new("deserialization accepts a compatibility field alias", self.file.span(pair[0].span), "alternate wire name")
                        .help("Check deployed producers and stored data for the old field name. Keep the alias while either uses it. Remove it once both use the canonical name.");
                    self.emit("compatibility-scaffolding", attr.span, report);
                }
            }
        }
        visit::walk_attribute(self, attr);
    }
}

fn api_stem(name: &str) -> Option<&str> {
    for suffix in ["_with_options", "_many", "_one", "_compat", "_legacy"] {
        if let Some(base) = name.strip_suffix(suffix) {
            return Some(base);
        }
    }
    let (base, version) = name.rsplit_once("_v")?;
    match version {
        "" => None,
        version if version.bytes().all(|byte| byte.is_ascii_digit()) => Some(base),
        _ => None,
    }
}
