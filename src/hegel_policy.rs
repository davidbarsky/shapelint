//! Hegel run settings and action-history rules over the written AST.

use rustc_ast::{ast, tokenstream::TokenTree};
use rustc_hash::FxHashMap;
use rustc_span::{BytePos, Span, Symbol};

use crate::diagnostic::{Report, Sink};
use crate::rust_syntax::RustFile;
use crate::test_review_rules::{
    Function, Traversal, attribute_path, collect_body, functions, hegel_test_attribute, path_name,
    setting,
};

pub(crate) fn lint(sink: &mut Sink<'_>, file: &RustFile<'_>) {
    for function in functions(file) {
        if let Some(attribute) = hegel_test_attribute(function.attrs) {
            for name in ["seed", "derandomize"] {
                if let Some((span, _)) = setting(attribute, name) {
                    let report = Report::new("Hegel test configures a local randomness policy", file.span(span), "local fixed-seed setting")
                        .help("keep run policy in the Hegel profile or failure database so the test can explore new cases");
                    sink.emit(
                        "hegel-fixed-seed",
                        file.item_span(function.span, function.attrs),
                        &function.name,
                        report,
                    );
                }
            }
            if let Some((span, value)) = setting(attribute, "suppress_health_check") {
                let configured = match value.as_slice() {
                    [] => None,
                    [TokenTree::Delimited(_, _, _, tokens)] if tokens.is_empty() => None,
                    _ => Some(()),
                };
                if let Some(()) = configured {
                    let report = Report::new("Hegel health-check suppression needs a measured rationale", file.span(span), "health check suppression")
                        .help("measure the health check first, or construct valid cases in the generator to avoid FilterTooMuch");
                    sink.emit(
                        "hegel-health-check",
                        file.item_span(function.span, function.attrs),
                        &function.name,
                        report,
                    );
                }
            }
            check_early_exit(sink, file, &function);
        }
        let Some(implementation) = function.implementation else {
            continue;
        };
        let state_machine = implementation
            .attrs
            .iter()
            .filter_map(attribute_path)
            .find(|path| {
                [
                    "hegel::state_machine",
                    "hegeltest::state_machine",
                    "hegel::concurrent_state_machine",
                    "hegeltest::concurrent_state_machine",
                ]
                .contains(&path.as_str())
            });
        let Some(_) = state_machine else { continue };
        for attribute in function.attrs {
            match attribute_path(attribute).as_deref() {
                Some("rule") => {
                    if let Some((span, _)) = setting(attribute, "weight") {
                        let report = Report::new("Hegel state-machine rule sets a manual selection weight", file.span(span), "manual rule weight")
                            .help("let Hegel sample enabled rules uniformly unless a measured workload justifies a weight");
                        sink.emit(
                            "hegel-rule-weight",
                            file.item_span(function.span, function.attrs),
                            &function.name,
                            report,
                        );
                    }
                }
                Some("invariant") => {
                    let ast::AttrKind::Normal(attribute) = &attribute.kind else {
                        continue;
                    };
                    let tokens = attribute.item.args.inner_tokens();
                    let always = tokens.iter().find(|tree| match tree {
                        TokenTree::Token(token, _) => match token.kind {
                            rustc_ast::token::Ident(name, _) => name.as_str() == "always_run",
                            _ => false,
                        },
                        _ => false,
                    });
                    if let Some(_) = always {
                        continue;
                    }
                    let report = Report::new("plain Hegel state-machine invariant is sampled", file.span(attribute.item.path.span), "sampled invariant")
                        .help("mark safety invariants with `#[invariant(always_run)]` so Hegel checks them after every action");
                    sink.emit(
                        "hegel-sampled-invariant",
                        file.item_span(function.span, function.attrs),
                        &function.name,
                        report,
                    );
                }
                _ => {}
            }
        }
    }
}

struct HistoryLoop<'a> {
    expr: &'a ast::Expr,
    label: Option<Symbol>,
    action_history: Option<()>,
    rejected_base: usize,
}

fn history_loop<'a>(
    expr: &'a ast::Expr,
    action_history: Option<()>,
    rejected_base: usize,
) -> Option<HistoryLoop<'a>> {
    let label = match &expr.kind {
        ast::ExprKind::ForLoop(loop_) => loop_.label.map(|label| label.ident.name),
        ast::ExprKind::While(_, _, label) | ast::ExprKind::Loop(_, label, _) => {
            label.map(|label| label.ident.name)
        }
        _ => return None,
    };
    Some(HistoryLoop {
        expr,
        label,
        action_history,
        rejected_base,
    })
}

struct ActionHistoryIndex {
    identifiers: Vec<u32>,
}

impl ActionHistoryIndex {
    fn new(file: &RustFile<'_>, span: Span) -> Self {
        let text = file.text(span);
        let base = file.span(span).start;
        let mut identifiers = Vec::new();
        let mut offset = 0usize;
        for token in rustc_lexer::tokenize(text, rustc_lexer::FrontmatterAllowed::No) {
            let start = offset;
            offset += token.len as usize;
            if token.kind != rustc_lexer::TokenKind::Ident {
                continue;
            }
            let name = &text[start..offset];
            if [
                "history",
                "actions",
                "operations",
                "commands",
                "events",
                "steps",
                "apply",
                "step",
                "replay",
                "execute",
            ]
            .iter()
            .any(|candidate| name.eq_ignore_ascii_case(candidate))
            {
                let start = u32::try_from(start).expect("source token offset fits in u32");
                identifiers.push(
                    base.checked_add(start)
                        .expect("source token position fits in u32"),
                );
            }
        }
        Self { identifiers }
    }

    fn contains(&self, file: &RustFile<'_>, span: Span) -> Option<()> {
        let span = file.span(span);
        let index = self
            .identifiers
            .partition_point(|&position| position < span.start);
        match self.identifiers.get(index) {
            Some(&position) if position < span.end => Some(()),
            _ => None,
        }
    }
}

#[derive(Clone, Copy)]
struct RejectedRegion {
    body: Span,
}

fn rejected_regions(expressions: &[&ast::Expr]) -> Vec<RejectedRegion> {
    let mut regions = Vec::new();
    for expr in expressions {
        match &expr.kind {
            ast::ExprKind::Match(_, arms, _) => {
                for arm in arms {
                    if let Some(()) = error_pattern(&arm.pat)
                        && let Some(body) = arm.body.as_ref()
                    {
                        regions.push(RejectedRegion { body: body.span });
                    }
                }
            }
            ast::ExprKind::If(condition, then, _) => {
                if let Some(()) = error_condition(condition) {
                    regions.push(RejectedRegion { body: then.span });
                }
            }
            _ => {}
        }
    }
    regions.sort_by_key(|region| (region.body.lo(), std::cmp::Reverse(region.body.hi())));
    regions
}

fn error_pattern(pattern: &ast::Pat) -> Option<()> {
    match &pattern.kind {
        ast::PatKind::TupleStruct(_, path, _)
        | ast::PatKind::Struct(_, path, _, _)
        | ast::PatKind::Path(_, path)
            if path_name(path).rsplit("::").next() == Some("Err") =>
        {
            Some(())
        }
        ast::PatKind::Or(patterns) => patterns.iter().find_map(error_pattern),
        _ => None,
    }
}

fn error_condition(expr: &ast::Expr) -> Option<()> {
    match &expr.kind {
        ast::ExprKind::Let(pattern, _, _, _) => error_pattern(pattern),
        ast::ExprKind::Binary(_, left, right) => {
            error_condition(left).or_else(|| error_condition(right))
        }
        _ => None,
    }
}

fn check_early_exit(sink: &mut Sink<'_>, file: &RustFile<'_>, function: &Function<'_>) {
    let Some(block) = &function.function.body else {
        return;
    };
    let body = collect_body(block, Traversal::Execution);
    let action_history = ActionHistoryIndex::new(file, block.span);
    let rejected = rejected_regions(&body.expressions);
    let mut next_rejected = 0;
    let mut active_rejected: Vec<RejectedRegion> = Vec::new();
    let mut loops: Vec<HistoryLoop<'_>> = Vec::new();
    let mut active_loops: Vec<usize> = Vec::new();
    let mut active_history_loops: Vec<usize> = Vec::new();
    let mut labels: FxHashMap<Symbol, Vec<usize>> = FxHashMap::default();
    for expr in &body.expressions {
        while let Some(&loop_id) = active_loops.last() {
            if loops[loop_id].expr.span.hi() > expr.span.lo() {
                break;
            }
            active_loops.pop();
            let loop_ = &loops[loop_id];
            if let Some(()) = loop_.action_history {
                let popped = active_history_loops.pop();
                debug_assert_eq!(popped, Some(loop_id));
            }
            if let Some(label) = loop_.label
                && let Some(stack) = labels.get_mut(&label)
            {
                let popped = stack.pop();
                debug_assert_eq!(popped, Some(loop_id));
                if stack.is_empty() {
                    labels.remove(&label);
                }
            }
        }
        while let Some(region) = active_rejected.last()
            && region.body.hi() <= expr.span.lo()
        {
            active_rejected.pop();
        }
        while let Some(region) = rejected.get(next_rejected)
            && region.body.lo() <= expr.span.lo()
        {
            next_rejected += 1;
            if region.body.hi() > expr.span.lo() {
                active_rejected.push(*region);
            }
        }
        let has_action_history = match expr.kind {
            ast::ExprKind::ForLoop(..) | ast::ExprKind::While(..) | ast::ExprKind::Loop(..) => {
                action_history.contains(file, expr.span)
            }
            _ => None,
        };
        if let Some(loop_) = history_loop(expr, has_action_history, active_rejected.len()) {
            let loop_id = loops.len();
            if let Some(()) = loop_.action_history {
                active_history_loops.push(loop_id);
            }
            if let Some(label) = loop_.label {
                labels.entry(label).or_default().push(loop_id);
            }
            loops.push(loop_);
            active_loops.push(loop_id);
        }
        let (label, keyword) = match &expr.kind {
            ast::ExprKind::Break(label, _) => (*label, "break"),
            ast::ExprKind::Ret(_) => (None, "return"),
            _ => continue,
        };
        let selected = match (keyword, label) {
            (_, Some(target)) => labels
                .get(&target.ident.name)
                .and_then(|stack| stack.last())
                .copied(),
            ("break", None) => active_loops.last().copied(),
            (_, None) => active_history_loops.last().copied(),
        };
        if let Some(loop_id) = selected {
            let loop_ = &loops[loop_id];
            let Some(()) = loop_.action_history else {
                continue;
            };
            let Some(_) = active_rejected.get(loop_.rejected_base) else {
                continue;
            };
            let span = Span::new(
                expr.span.lo(),
                expr.span.lo() + BytePos(keyword.len() as u32),
                expr.span.ctxt(),
                None,
            );
            let report = Report::new(
                "Hegel action-history test exits after an error",
                file.span(span),
                "early exit stops later observations",
            )
            .label(file.span(loop_.expr.span), "action history loop")
            .help("continue observing after an expected rejection while the system remains usable");
            sink.emit(
                "hegel-early-exit",
                file.item_span(function.span, function.attrs),
                &function.name,
                report,
            );
        }
    }
}
