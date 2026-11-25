//! Hegel input construction and execution rules over the written AST.

use rustc_ast::{
    ast,
    visit::{self, Visitor},
};
use rustc_hash::FxHashSet;

use crate::diagnostic::{Report, Sink};
use crate::rust_syntax::RustFile;
use crate::test_review_rules::{
    Body, Function, Traversal, attribute_path, collect_body, expr_path, functions,
    hegel_test_attribute, path_name,
};

pub(crate) fn lint(sink: &mut Sink<'_>, file: &RustFile<'_>) {
    let functions = functions(file);
    let generated = generated_types(file);
    for function in functions {
        let Some(block) = &function.function.body else {
            continue;
        };
        let body = collect_body(block, Traversal::Execution);
        let cases = function
            .function
            .sig
            .decl
            .inputs
            .iter()
            .filter_map(|param| {
                test_case_type(&param.ty)?;
                let ast::PatKind::Ident(_, ident, None) = param.pat.kind else {
                    return None;
                };
                Some(ident.name.to_string())
            })
            .collect::<FxHashSet<_>>();
        if let Some(_) = hegel_test_attribute(function.attrs) {
            check_test(sink, file, &function, &body, &cases);
        } else {
            check_operation(sink, file, &function, &body, &cases, &generated);
        }
    }
    struct Filters<'a, 'b, 'c> {
        sink: &'a mut Sink<'b>,
        file: &'a RustFile<'c>,
        item: Option<(rustc_span::Span, String)>,
    }
    impl<'a> Visitor<'a> for Filters<'_, '_, '_> {
        fn visit_item(&mut self, item: &'a ast::Item) {
            let previous = self.item.take();
            self.item = Some((
                item.span,
                match &item.kind {
                    ast::ItemKind::Fn(function) => format!("fn {}", function.ident.name),
                    _ => "<item>".to_owned(),
                },
            ));
            visit::walk_item(self, item);
            self.item = previous;
        }
        fn visit_assoc_item(&mut self, item: &'a ast::AssocItem, ctxt: visit::AssocCtxt) {
            let previous = self.item.take();
            self.item = Some((
                item.span,
                match &item.kind {
                    ast::AssocItemKind::Fn(function) => format!("fn {}", function.ident.name),
                    _ => "<item>".to_owned(),
                },
            ));
            visit::walk_assoc_item(self, item, ctxt);
            self.item = previous;
        }
        fn visit_expr(&mut self, expr: &'a ast::Expr) {
            if let ast::ExprKind::MethodCall(call) = &expr.kind
                && call.seg.ident.name.as_str() == "filter"
                && let Some(()) = generator_expression(&call.receiver)
                && let Some((span, name)) = &self.item
            {
                let report = Report::new("Hegel generator filters generated values after construction", self.file.span(call.seg.ident.span), "generator filter")
                    .help("construct the valid input directly with a typed generator, so shrinking stays inside the input domain");
                self.sink.emit(
                    "hegel-generator-filter",
                    self.file.span(*span),
                    name,
                    report,
                );
            }
            visit::walk_expr(self, expr);
        }
    }
    Filters {
        sink,
        file,
        item: None,
    }
    .visit_crate(file.krate);
}

fn test_case_type(ty: &ast::Ty) -> Option<()> {
    match &ty.kind {
        ast::TyKind::Ref(_, inner) => test_case_type(&inner.ty),
        ast::TyKind::Paren(inner) => test_case_type(inner),
        ast::TyKind::Path(_, path) if path.segments.last()?.ident.name.as_str() == "TestCase" => {
            Some(())
        }
        _ => None,
    }
}

fn case_receiver(
    receiver: &ast::Expr,
    at: rustc_span::Span,
    body: &Body<'_>,
    cases: &FxHashSet<String>,
) -> Option<()> {
    let name = expr_path(receiver)?;
    match body.binding(&name, at) {
        None if cases.contains(&name) => Some(()),
        Some(_) | None => None,
    }
}

fn draw(expr: &ast::Expr, body: &Body<'_>, cases: &FxHashSet<String>) -> Option<()> {
    match &expr.kind {
        ast::ExprKind::MethodCall(call) if call.seg.ident.name.as_str() == "draw" => {
            case_receiver(&call.receiver, expr.span, body, cases)
        }
        ast::ExprKind::Call(callee, _) => {
            let name = expr_path(callee)?;
            let mut segments = name.rsplit("::");
            match (segments.next(), segments.next()) {
                (Some("draw"), Some("TestCase")) => Some(()),
                _ => None,
            }
        }
        _ => None,
    }
}

fn check_test(
    sink: &mut Sink<'_>,
    file: &RustFile<'_>,
    function: &Function<'_>,
    body: &Body<'_>,
    cases: &FxHashSet<String>,
) {
    let draws: Vec<_> = body
        .expressions
        .iter()
        .filter_map(|expr| draw(expr, body, cases).map(|()| *expr))
        .collect();
    if let [first, second, ..] = draws.as_slice() {
        let report = Report::new("Hegel test draws random input in multiple execution steps", file.span(second.span), "second execution-level draw")
            .label(file.span(first.span), "first execution-level draw")
            .help("draw one typed case at the test boundary and construct its dependent values in the generator");
        sink.emit(
            "hegel-scattered-draws",
            file.item_span(function.span, function.attrs),
            &function.name,
            report,
        );
    }
    for expr in &body.expressions {
        if let ast::ExprKind::If(condition, _, _) = &expr.kind {
            let direct = draws
                .iter()
                .find(|draw| condition.span.contains(draw.span))
                .map(|expr| expr.span);
            let selected = direct.or_else(|| {
                body.expressions
                    .iter()
                    .filter(|path| condition.span.contains(path.span))
                    .find_map(|path| {
                        let name = expr_path(path)?;
                        let binding = body.binding(&name, expr.span)?;
                        let initializer = binding.initializer?;
                        draws
                            .iter()
                            .find(|draw| initializer.span.contains(draw.span))
                            .map(|_| path.span)
                    })
            });
            if let Some(span) = selected {
                let report = Report::new("Hegel test branches with an input drawn during execution", file.span(span), "drawn input controls this condition")
                    .help("draw one typed case and match on its variants, or construct the branch in the generator");
                sink.emit(
                    "hegel-input-branch",
                    file.item_span(function.span, function.attrs),
                    &function.name,
                    report,
                );
            }
        }
        if let ast::ExprKind::MethodCall(call) = &expr.kind
            && call.seg.ident.name.as_str() == "assume"
            && let Some(()) = case_receiver(&call.receiver, expr.span, body, cases)
        {
            let report = Report::new("Hegel test discards generated cases with `TestCase::assume`", file.span(call.seg.ident.span), "case filtering")
                .help("construct valid cases in the generator, or match and call `reject()` only for an explicitly unavailable subject");
            sink.emit(
                "hegel-assume",
                file.item_span(function.span, function.attrs),
                &function.name,
                report,
            );
        }
    }
}

fn generator_expression(expr: &ast::Expr) -> Option<()> {
    match &expr.kind {
        ast::ExprKind::Paren(inner) | ast::ExprKind::AddrOf(_, _, inner) => {
            generator_expression(inner)
        }
        ast::ExprKind::Path(_, path) => generator_path(path),
        ast::ExprKind::Call(callee, _) => generator_expression(callee),
        ast::ExprKind::MacCall(call) => generator_path(&call.path),
        ast::ExprKind::MethodCall(call) => match call.seg.ident.name.as_str() {
            "iter" | "iter_mut" | "into_iter" => None,
            _ => generator_expression(&call.receiver),
        },
        _ => None,
    }
}

fn generator_path(path: &ast::Path) -> Option<()> {
    let mut qualifiers = path.segments.iter().rev().skip(1);
    qualifiers
        .find(|segment| segment.ident.name.as_str() == "generators")
        .map(|_| ())
}

fn check_operation(
    sink: &mut Sink<'_>,
    file: &RustFile<'_>,
    function: &Function<'_>,
    body: &Body<'_>,
    cases: &FxHashSet<String>,
    generated: &FxHashSet<String>,
) {
    let name = function.function.ident.name.as_str();
    if name != "apply" && name != "after" && !name.starts_with("resolve") {
        return;
    }
    let attrs = function.attrs.iter().chain(
        function
            .implementation
            .into_iter()
            .flat_map(|item| item.attrs.iter()),
    );
    if let Some(_) = attrs.filter_map(attribute_path).find(|path| {
        [
            "rule",
            "invariant",
            "state_machine",
            "concurrent_state_machine",
        ]
        .contains(&path.rsplit("::").next().expect("path has a segment"))
    }) {
        return;
    }
    if cases.is_empty() {
        let Some(ast::Item {
            kind: ast::ItemKind::Impl(implementation),
            ..
        }) = function.implementation
        else {
            return;
        };
        let ast::TyKind::Path(_, path) = &implementation.self_ty.kind else {
            return;
        };
        let Some(name) = path.segments.last() else {
            return;
        };
        if !generated.contains(name.ident.name.as_str()) {
            return;
        }
        let random = body.expressions.iter().find_map(|expr| {
            if let Some(()) = draw(expr, body, cases) {
                return Some(());
            }
            match &expr.kind {
                ast::ExprKind::MethodCall(call)
                    if ["gen", "gen_range", "random", "random_range"]
                        .contains(&call.seg.ident.name.as_str()) =>
                {
                    file.text(call.receiver.span)
                        .to_ascii_lowercase()
                        .contains("rng")
                        .then_some(())
                }
                ast::ExprKind::Call(callee, _) => expr_path(callee)
                    .filter(|path| path.contains("rand::"))
                    .map(|_| ()),
                _ => None,
            }
        });
        let Some(()) = random else { return };
    }
    let report = Report::new("generated operation accepts Hegel context or performs random construction", file.span(function.function.ident.span), "random operation method")
        .help("draw and construct the complete operation before applying it; an operation should consume generated values without further randomness");
    sink.emit(
        "hegel-random-operation",
        file.item_span(function.span, function.attrs),
        &function.name,
        report,
    );
}

fn generated_types(file: &RustFile<'_>) -> FxHashSet<String> {
    struct Generated(FxHashSet<String>);
    impl<'a> Visitor<'a> for Generated {
        fn visit_item(&mut self, item: &'a ast::Item) {
            match &item.kind {
                ast::ItemKind::Struct(ident, _, _) | ast::ItemKind::Enum(ident, _, _) => {
                    if let Some(_) = item.attrs.iter().find(|attribute| {
                        let ast::AttrKind::Normal(attribute) = &attribute.kind else {
                            return false;
                        };
                        if path_name(&attribute.item.path) != "derive" {
                            return false;
                        }
                        attribute
                            .item
                            .args
                            .inner_tokens()
                            .iter()
                            .any(|tree| match tree {
                                rustc_ast::tokenstream::TokenTree::Token(token, _) => {
                                    match token.kind {
                                        rustc_ast::token::Ident(name, _) => {
                                            name.as_str() == "DefaultGenerator"
                                        }
                                        _ => false,
                                    }
                                }
                                _ => false,
                            })
                    }) {
                        self.0.insert(ident.name.to_string());
                    }
                }
                ast::ItemKind::Impl(implementation) => {
                    if let Some(trait_) = &implementation.of_trait
                        && trait_
                            .trait_ref
                            .path
                            .segments
                            .last()
                            .map(|segment| segment.ident.name.as_str())
                            == Some("DefaultGenerator")
                        && let ast::TyKind::Path(_, path) = &implementation.self_ty.kind
                        && let Some(segment) = path.segments.last()
                    {
                        self.0.insert(segment.ident.name.to_string());
                    }
                }
                _ => {}
            }
            visit::walk_item(self, item);
        }
    }
    let mut visitor = Generated(FxHashSet::default());
    visitor.visit_crate(file.krate);
    visitor.0
}
