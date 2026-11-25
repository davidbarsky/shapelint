//! Rules over written expressions and state representations, before macro expansion.

use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_ast::{
    ast,
    visit::{self, AssocCtxt, FnCtxt, FnKind, Visitor},
};
use rustc_span::sym;

use crate::Span;
use crate::diagnostic::{Report, Sink};
use crate::rust_syntax::RustFile;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum JsonContext {
    Boundary,
    Domain,
}

pub(crate) fn lint(sink: &mut Sink, file: &RustFile<'_>, boundary: JsonContext) {
    let mut visitor = Expressions {
        sink,
        file,
        boundary,
        item: None,
        implementation: None,
        method: None,
    };
    visitor.visit_crate(file.krate);
}

struct Expressions<'a, 'b, 'c> {
    sink: &'a mut Sink<'b>,
    file: &'a RustFile<'c>,
    boundary: JsonContext,
    item: Option<(Span, String)>,
    implementation: Option<String>,
    method: Option<String>,
}

impl Expressions<'_, '_, '_> {
    fn emit(&mut self, rule: &'static str, span: rustc_span::Span, report: Report) {
        let (span, name) = match &self.item {
            Some((span, name)) => (*span, name.clone()),
            None => (self.file.span(span), "<item>".to_owned()),
        };
        self.sink.emit(rule, span, name, report);
    }

    fn macro_call(&mut self, name: &str, span: rustc_span::Span, nested: &str) {
        let report = match name {
            "matches" => Some(("matches-macro", Report::new(
                "`matches!` reduces a variant decision to a boolean", self.file.span(span),
                format!("{nested}`matches!` invocation"),
            ).help("write an explicit `match` so the selected variant and any payload stay available"))),
            "json" if self.boundary == JsonContext::Domain => Some(("json-in-domain", Report::new(
                "constructs JSON with a macro outside the configured boundary", self.file.span(span),
                "generic JSON construction",
            ).help("serialize a typed struct or enum at the JSON boundary"))),
            "task_local" | "thread_local" => Some(("implicit-dependency", Report::new(
                format!("`{name}!` stores dependency state outside the function signature"), self.file.span(span),
                "implicit context state",
            ).help("pass request or execution context as an explicit argument"))),
            _ => None,
        };
        if let Some((rule, report)) = report {
            self.emit(rule, span, report);
        }
    }

    fn fields(&mut self, fields: &ast::VariantData, span: Span, name: String) {
        for field in fields.fields() {
            if let Some(()) = serde(&field.attrs) {
                continue;
            }
            if let Some(()) = boolean_type(&field.ty) {
                let label = match field.ident {
                    Some(_) => "boolean field",
                    None => "boolean tuple field",
                };
                self.sink.emit(
                    "boolean-state",
                    span,
                    name.clone(),
                    Report::new(
                        "type stores a bool-shaped field",
                        self.file.span(field.ty.span),
                        label,
                    )
                    .help(
                        "use a named state enum when the boolean represents a domain alternative",
                    ),
                );
            }
        }
    }
}

impl<'ast> Visitor<'ast> for Expressions<'_, '_, '_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        let previous = self.item.clone();
        let implementation = self.implementation.clone();
        if let Some(named) = self.file.named_item(item) {
            self.item = Some(named);
        }
        match &item.kind {
            ast::ItemKind::Impl(value) => {
                self.implementation = Some(compact(self.file.text(value.self_ty.span)));
            }
            ast::ItemKind::Struct(name, _, fields) => {
                if let (None, None) = (serde(&item.attrs), repr_c(&item.attrs)) {
                    self.fields(
                        fields,
                        self.file.item_span(item.span, &item.attrs),
                        format!("struct {name}"),
                    );
                }
            }
            ast::ItemKind::Enum(name, _, definition) => {
                if let (None, None) = (serde(&item.attrs), repr_c(&item.attrs)) {
                    for variant in &definition.variants {
                        self.fields(
                            &variant.data,
                            self.file.item_span(item.span, &item.attrs),
                            format!("enum {name}::{}", variant.ident),
                        );
                    }
                }
            }
            ast::ItemKind::Static(value) => {
                let ty = compact(self.file.text(value.ty.span));
                let state = match value.mutability {
                    ast::Mutability::Mut => Some(()),
                    ast::Mutability::Not => [
                        "Mutex", "RwLock", "OnceLock", "LazyLock", "RefCell", "Cell<", "Atomic",
                        "Context",
                    ]
                    .iter()
                    .find(|marker| ty.contains(**marker))
                    .map(|_| ()),
                };
                if let Some(()) = state {
                    self.emit(
                        "implicit-dependency",
                        item.span,
                        Report::new(
                            format!(
                                "global state `{}` hides a dependency from callers",
                                value.ident
                            ),
                            self.file.span(item.span),
                            "global or context state",
                        )
                        .help("pass the state or context through the API that needs it"),
                    );
                }
            }
            _ => {}
        }
        visit::walk_item(self, item);
        self.item = previous;
        self.implementation = implementation;
    }

    fn visit_fn(
        &mut self,
        kind: FnKind<'ast>,
        attrs: &ast::AttrVec,
        span: rustc_span::Span,
        _: ast::NodeId,
    ) {
        let previous = self.item.clone();
        if let FnKind::Fn(context, _, function) = kind {
            let path = match (&self.implementation, context) {
                (Some(owner), FnCtxt::Assoc(_)) => format!("{owner}::{}", function.ident),
                _ => function.ident.to_string(),
            };
            self.item = Some((self.file.item_span(span, attrs), format!("fn {path}")));
            if let FnCtxt::Free | FnCtxt::Assoc(AssocCtxt::Impl { of_trait: false }) = context
                && let ast::Extern::None = function.sig.header.ext
                && let None = serde(attrs)
            {
                for param in &function.sig.decl.inputs {
                    if let Some(()) = boolean_type(&param.ty) {
                        self.emit("boolean-state", span, Report::new(
                            format!("{} takes boolean state in a parameter", crate::suggest::Code(&path)),
                            self.file.span(param.ty.span), "boolean parameter",
                        ).help("use a named outcome or enum when the value represents domain state"));
                    }
                }
                if let ast::FnRetTy::Ty(ty) = &function.sig.decl.output
                    && let Some(()) = boolean_type(ty)
                {
                    self.emit(
                        "boolean-state",
                        span,
                        Report::new(
                            format!("{} returns boolean state", crate::suggest::Code(&path)),
                            self.file.span(ty.span),
                            "boolean return type",
                        )
                        .help("return a named outcome or enum when the value carries domain state"),
                    );
                }
            }
        }
        visit::walk_fn(self, kind);
        self.item = previous;
    }

    fn visit_expr(&mut self, expr: &'ast ast::Expr) {
        let previous = self.method.clone();
        match &expr.kind {
            ast::ExprKind::MethodCall(call) => {
                let name = call.seg.ident.name.as_str();
                if name == "ok" {
                    self.emit("error-erasure", expr.span, Report::new(
                        "`.ok()` can discard an error and change failure into absence",
                        self.file.span(call.seg.ident.span), "error discarded here",
                    ).help("handle the error explicitly or return it from the responsible boundary"));
                }
                self.method = Some(name.to_owned());
            }
            ast::ExprKind::Path(_, path) => {
                let names: Vec<_> = path
                    .segments
                    .iter()
                    .map(|segment| segment.ident.name.as_str())
                    .collect();
                if names.ends_with(&["Result", "ok"])
                    && let Some("filter_map") = self.method.as_deref()
                {
                    self.emit(
                        "error-erasure",
                        expr.span,
                        Report::new(
                            "`filter_map(Result::ok)` drops every failed result",
                            self.file.span(expr.span),
                            "error discarded here",
                        )
                        .help("handle each error explicitly or return the error from the boundary"),
                    );
                }
            }
            _ => {}
        }
        visit::walk_expr(self, expr);
        self.method = previous;
    }

    fn visit_arm(&mut self, arm: &'ast ast::Arm) {
        if let ast::PatKind::TupleStruct(_, path, fields) = &arm.pat.kind
            && let Some(segment) = path.segments.last()
            && segment.ident.name.as_str() == "Err"
            && let [field] = fields.as_slice()
            && let Some(()) = wildcard(field)
            && let Some(body) = &arm.body
            && let Some(()) = fallback(body)
        {
            self.emit(
                "error-erasure",
                arm.span,
                Report::new(
                    "an `Err(_)` branch erases a failure as absence, a default, or `continue`",
                    self.file.span(arm.pat.span),
                    "error discarded here",
                )
                .help("preserve the error or handle the best-effort case with an explicit reason"),
            );
        }
        visit::walk_arm(self, arm);
    }

    fn visit_mac_call(&mut self, call: &'ast ast::MacCall) {
        if let Some(segment) = call.path.segments.last() {
            self.macro_call(segment.ident.name.as_str(), call.path.span, "");
        }
        let tokens = tokens(&call.args.tokens);
        let pairs = tokens.windows(2).enumerate();
        for (index, pair) in pairs {
            if let TokenKind::Ident(name, _) = pair[0].kind
                && pair[1].kind == TokenKind::Bang
            {
                let mut start = index;
                while start >= 2 && tokens[start - 1].kind == TokenKind::PathSep {
                    if let TokenKind::Ident(..) = tokens[start - 2].kind {
                        start -= 2;
                    } else {
                        break;
                    }
                }
                self.macro_call(
                    name.as_str(),
                    tokens[start].span.to(pair[0].span),
                    "nested ",
                );
            }
        }
    }
}

fn wildcard(pattern: &ast::Pat) -> Option<()> {
    match &pattern.kind {
        ast::PatKind::Wild => Some(()),
        ast::PatKind::Paren(inner) => wildcard(inner),
        _ => None,
    }
}

fn fallback(expr: &ast::Expr) -> Option<()> {
    match &expr.kind {
        ast::ExprKind::Path(_, path) => path
            .segments
            .last()
            .filter(|segment| segment.ident.name.as_str() == "None")
            .map(|_| ()),
        ast::ExprKind::Continue(_) => Some(()),
        ast::ExprKind::Block(block, _) => match block.stmts.last() {
            Some(ast::Stmt {
                kind: ast::StmtKind::Expr(tail),
                ..
            }) => fallback(tail),
            _ => None,
        },
        ast::ExprKind::Ret(Some(value)) => fallback(value),
        ast::ExprKind::Call(callee, _) => match &callee.kind {
            ast::ExprKind::Path(_, path) => path
                .segments
                .last()
                .filter(|segment| segment.ident.name.as_str() == "default")
                .map(|_| ()),
            _ => None,
        },
        _ => None,
    }
}

fn boolean_type(ty: &ast::Ty) -> Option<()> {
    #[derive(Default)]
    struct Shape {
        boolean: Option<()>,
        callback: Option<()>,
    }
    impl<'ast> Visitor<'ast> for Shape {
        fn visit_ty(&mut self, ty: &'ast ast::Ty) {
            match &ty.kind {
                ast::TyKind::FnPtr(_) => self.callback = Some(()),
                ast::TyKind::Path(_, path) => {
                    if let Some(_) = path
                        .segments
                        .iter()
                        .find(|segment| segment.ident.name == sym::bool)
                    {
                        self.boolean = Some(());
                    }
                }
                _ => {}
            }
            visit::walk_ty(self, ty);
        }
    }
    let mut shape = Shape::default();
    shape.visit_ty(ty);
    match shape {
        Shape {
            boolean: Some(()),
            callback: None,
        } => Some(()),
        _ => None,
    }
}

fn serde(attrs: &[ast::Attribute]) -> Option<()> {
    attrs.iter().find_map(|attr| {
        if attr.has_name(rustc_span::Symbol::intern("serde")) {
            return Some(());
        }
        if !attr.has_name(sym::derive) {
            return None;
        }
        attr.meta_item_list()?.iter().find_map(|meta| {
            let item = meta.meta_item()?;
            item.path
                .segments
                .iter()
                .find(|segment| ["Serialize", "Deserialize"].contains(&segment.ident.name.as_str()))
                .map(|_| ())
        })
    })
}

fn repr_c(attrs: &[ast::Attribute]) -> Option<()> {
    attrs.iter().find_map(|attr| {
        if !attr.has_name(sym::repr) {
            return None;
        }
        attr.meta_item_list()?
            .iter()
            .find(|meta| meta.has_name(sym::C))
            .map(|_| ())
    })
}

pub(crate) fn compact(text: &str) -> String {
    let mut offset = 0;
    let mut result = String::new();
    for token in rustc_lexer::tokenize(text, rustc_lexer::FrontmatterAllowed::No) {
        let end = offset + token.len as usize;
        match token.kind {
            rustc_lexer::TokenKind::Whitespace
            | rustc_lexer::TokenKind::LineComment { .. }
            | rustc_lexer::TokenKind::BlockComment { .. } => {}
            _ => result.push_str(&text[offset..end]),
        }
        offset = end;
    }
    result
}

pub(crate) fn tokens(stream: &TokenStream) -> Vec<Token> {
    fn collect(stream: &TokenStream, out: &mut Vec<Token>) {
        for tree in stream.iter() {
            match tree {
                TokenTree::Token(token, _) => out.push(*token),
                TokenTree::Delimited(_, _, _, stream) => collect(stream, out),
            }
        }
    }
    let mut result = Vec::new();
    collect(stream, &mut result);
    result
}
