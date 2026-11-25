//! Test-shape and source-comment rules over rustc's written AST.

use rustc_ast::{
    ast,
    visit::{self, Visitor},
};
use rustc_hash::FxHashMap;

use crate::Span;
use crate::diagnostic::{Report, Sink};
use crate::rust_syntax::{RustFile, is_test_path, test_attributes};

pub(crate) struct Function<'a> {
    pub function: &'a ast::Fn,
    pub attrs: &'a [ast::Attribute],
    pub span: rustc_span::Span,
    pub name: String,
    pub test: Option<()>,
}

pub(crate) fn functions<'a>(file: &RustFile<'a>) -> Vec<Function<'a>> {
    struct Collect<'a> {
        functions: Vec<Function<'a>>,
        implementation: Option<&'a ast::Item>,
        scope: Vec<String>,
        test: Option<()>,
    }
    impl<'a> Visitor<'a> for Collect<'a> {
        fn visit_item(&mut self, item: &'a ast::Item) {
            let implementation = self.implementation;
            let test = self.test;
            self.test = test.or_else(|| test_attributes(&item.attrs));
            let scope = self.scope.len();
            match &item.kind {
                ast::ItemKind::Impl(_) => self.implementation = Some(item),
                ast::ItemKind::Mod(_, name, _) => self.scope.push(name.name.to_string()),
                ast::ItemKind::Fn(function) => {
                    self.functions.push(Function {
                        function,
                        attrs: &item.attrs,
                        span: item.span,
                        name: format!(
                            "fn {}",
                            self.scope
                                .iter()
                                .map(String::as_str)
                                .chain([function.ident.name.as_str()])
                                .collect::<Vec<_>>()
                                .join("::")
                        ),
                        test: self.test,
                    });
                    self.scope.push(function.ident.name.to_string());
                }
                _ => {}
            }
            visit::walk_item(self, item);
            self.scope.truncate(scope);
            self.implementation = implementation;
            self.test = test;
        }
        fn visit_assoc_item(&mut self, item: &'a ast::AssocItem, ctxt: visit::AssocCtxt) {
            if let ast::AssocItemKind::Fn(function) = &item.kind {
                let owner = match self.implementation.map(|item| &item.kind) {
                    Some(ast::ItemKind::Impl(implementation)) => {
                        rustc_ast_pretty::pprust::ty_to_string(&implementation.self_ty)
                    }
                    _ => String::new(),
                };
                self.functions.push(Function {
                    function,
                    attrs: &item.attrs,
                    span: item.span,
                    name: format!(
                        "fn {}{}{}",
                        owner,
                        if owner.is_empty() { "" } else { "::" },
                        function.ident.name
                    ),
                    test: self.test.or_else(|| test_attributes(&item.attrs)),
                });
            }
            visit::walk_assoc_item(self, item, ctxt);
        }
    }
    let mut visitor = Collect {
        functions: Vec::new(),
        implementation: None,
        scope: Vec::new(),
        test: None,
    };
    visitor.visit_crate(file.krate);
    visitor.functions
}

pub(crate) fn path_name(path: &ast::Path) -> String {
    let mut name = String::new();
    for segment in &path.segments {
        if !name.is_empty() {
            name.push_str("::");
        }
        name.push_str(segment.ident.name.as_str());
    }
    name
}

pub(crate) struct Binding<'a> {
    pub statement: rustc_span::Span,
    pub scope: rustc_span::Span,
    pub initializer: Option<&'a ast::Expr>,
}

#[derive(Default)]
pub(crate) struct Body<'a> {
    pub expressions: Vec<&'a ast::Expr>,
    bindings: FxHashMap<String, Vec<Binding<'a>>>,
}

struct BodyVisitor<'a> {
    body: Body<'a>,
    scopes: Vec<rustc_span::Span>,
}

pub(crate) fn collect_body<'a>(block: &'a ast::Block) -> Body<'a> {
    let mut visitor = BodyVisitor {
        body: Body::default(),
        scopes: Vec::new(),
    };
    visitor.visit_block(block);
    let mut body = visitor.body;
    for bindings in body.bindings.values_mut() {
        bindings.sort_by_key(|binding| binding.statement.lo());
    }
    body
}

impl<'a> Body<'a> {
    pub fn binding(&self, name: &str, at: rustc_span::Span) -> Option<&Binding<'a>> {
        let bindings = self.bindings.get(name)?;
        let end = bindings.partition_point(|binding| binding.statement.lo() < at.lo());
        bindings[..end]
            .iter()
            .rev()
            .find(|binding| binding.scope.contains(at))
    }
}

impl<'a> BodyVisitor<'a> {
    fn bind(
        &mut self,
        pat: &'a ast::Pat,
        statement: rustc_span::Span,
        scope: rustc_span::Span,
        initializer: Option<&'a ast::Expr>,
    ) {
        struct Names(Vec<String>);
        impl<'a> Visitor<'a> for Names {
            fn visit_pat(&mut self, pat: &'a ast::Pat) {
                if let ast::PatKind::Ident(_, ident, _) = pat.kind {
                    self.0.push(ident.name.to_string());
                }
                visit::walk_pat(self, pat);
            }
        }
        let mut names = Names(Vec::new());
        names.visit_pat(pat);
        for name in names.0 {
            self.body.bindings.entry(name).or_default().push(Binding {
                statement,
                scope,
                initializer,
            });
        }
    }
    fn condition_bindings(&mut self, expr: &'a ast::Expr, scope: rustc_span::Span) {
        match &expr.kind {
            ast::ExprKind::Let(pat, _, _, _) => self.bind(pat, pat.span, scope, None),
            ast::ExprKind::Binary(_, left, right) => {
                self.condition_bindings(left, scope);
                self.condition_bindings(right, scope);
            }
            _ => {}
        }
    }
}

impl<'a> Visitor<'a> for BodyVisitor<'a> {
    fn visit_item(&mut self, _: &'a ast::Item) {}
    fn visit_block(&mut self, block: &'a ast::Block) {
        self.scopes.push(block.span);
        visit::walk_block(self, block);
        self.scopes.pop();
    }
    fn visit_local(&mut self, local: &'a ast::Local) {
        let scope = *self.scopes.last().expect("locals belong to a block");
        self.bind(&local.pat, local.span, scope, local.kind.init());
        visit::walk_local(self, local);
    }
    fn visit_expr(&mut self, expr: &'a ast::Expr) {
        self.body.expressions.push(expr);
        match &expr.kind {
            ast::ExprKind::ForLoop(loop_) => {
                self.bind(&loop_.pat, loop_.pat.span, loop_.body.span, None)
            }
            ast::ExprKind::If(condition, body, _) | ast::ExprKind::While(condition, body, _) => {
                self.condition_bindings(condition, body.span)
            }
            ast::ExprKind::Match(_, arms, _) => {
                for arm in arms {
                    self.bind(&arm.pat, arm.pat.span, arm.span, None);
                }
            }
            _ => {}
        }
        visit::walk_expr(self, expr);
    }
}

pub(crate) fn lint(sink: &mut Sink<'_>, file: &RustFile<'_>, path: &str) {
    let functions = functions(file);
    for function in &functions {
        let Some(block) = &function.function.body else {
            continue;
        };
        let body = collect_body(block);
        let test = function.test.or_else(|| is_test_path(path));
        for expr in &body.expressions {
            if let Some(()) = test {
                check_cases(sink, file, function, &body, expr);
                check_primitive(sink, file, function, &body, expr);
            }
        }
    }
    struct Bounds<'a, 'b, 'c> {
        sink: &'a mut Sink<'b>,
        file: &'a RustFile<'c>,
        item: Option<(Span, String)>,
        decimals: FxHashMap<(u32, u32), Option<rustc_span::Span>>,
    }
    impl<'a> Visitor<'a> for Bounds<'_, '_, '_> {
        fn visit_item(&mut self, item: &'a ast::Item) {
            let previous = self.item.take();
            let name = match &item.kind {
                ast::ItemKind::Fn(function) => format!("fn {}", function.ident.name),
                ast::ItemKind::Const(item) => format!("const {}", item.ident.name),
                ast::ItemKind::Static(item) => format!("static {}", item.ident.name),
                _ => "<item>".to_owned(),
            };
            self.item = Some((self.file.item_span(item.span, &item.attrs), name));
            visit::walk_item(self, item);
            self.item = previous;
        }
        fn visit_assoc_item(&mut self, item: &'a ast::AssocItem, ctxt: visit::AssocCtxt) {
            let previous = self.item.take();
            let name = match &item.kind {
                ast::AssocItemKind::Fn(function) => format!("fn {}", function.ident.name),
                ast::AssocItemKind::Const(item) => format!("const {}", item.ident.name),
                _ => "<item>".to_owned(),
            };
            self.item = Some((self.file.item_span(item.span, &item.attrs), name));
            visit::walk_assoc_item(self, item, ctxt);
            self.item = previous;
        }
        fn visit_expr(&mut self, expr: &'a ast::Expr) {
            if let Some((span, name)) = &self.item {
                check_bound(self.sink, self.file, *span, name, expr, &mut self.decimals);
            }
            visit::walk_expr(self, expr);
        }
    }
    Bounds {
        sink,
        file,
        item: None,
        decimals: FxHashMap::default(),
    }
    .visit_crate(file.krate);
    check_comments(sink, file, &functions);
}

fn array_like(expr: &ast::Expr) -> Option<()> {
    match &expr.kind {
        ast::ExprKind::Array(_) | ast::ExprKind::Repeat(_, _) => Some(()),
        ast::ExprKind::AddrOf(_, _, inner) | ast::ExprKind::Paren(inner) => array_like(inner),
        ast::ExprKind::MacCall(call) if path_name(&call.path) == "vec" => Some(()),
        ast::ExprKind::MethodCall(call)
            if ["iter", "into_iter"].contains(&call.seg.ident.name.as_str()) =>
        {
            array_like(&call.receiver)
        }
        _ => None,
    }
}

fn iterable_name(expr: &ast::Expr) -> Option<String> {
    match &expr.kind {
        ast::ExprKind::Path(None, path) if path.segments.len() == 1 => Some(path_name(path)),
        ast::ExprKind::AddrOf(_, _, inner) | ast::ExprKind::Paren(inner) => iterable_name(inner),
        ast::ExprKind::MethodCall(call)
            if ["iter", "into_iter"].contains(&call.seg.ident.name.as_str()) =>
        {
            iterable_name(&call.receiver)
        }
        _ => None,
    }
}

fn check_cases(
    sink: &mut Sink<'_>,
    file: &RustFile<'_>,
    function: &Function<'_>,
    body: &Body<'_>,
    expr: &ast::Expr,
) {
    let ast::ExprKind::ForLoop(loop_) = &expr.kind else {
        return;
    };
    let fixed = array_like(&loop_.iter).or_else(|| {
        let name = iterable_name(&loop_.iter)?;
        array_like(body.binding(&name, expr.span)?.initializer?)
    });
    let Some(()) = fixed else { return };
    struct Operations {
        assertion: Option<()>,
        state: Option<()>,
    }
    impl<'a> Visitor<'a> for Operations {
        fn visit_mac_call(&mut self, call: &'a ast::MacCall) {
            if let Some(segment) = call.path.segments.last()
                && [
                    "assert",
                    "assert_eq",
                    "assert_ne",
                    "debug_assert",
                    "debug_assert_eq",
                    "debug_assert_ne",
                ]
                .contains(&segment.ident.name.as_str())
            {
                self.assertion = Some(());
            }
        }
        fn visit_expr(&mut self, expr: &'a ast::Expr) {
            match &expr.kind {
                ast::ExprKind::MethodCall(call)
                    if ["apply", "step", "replay"].contains(&call.seg.ident.name.as_str()) =>
                {
                    self.state = Some(())
                }
                ast::ExprKind::Call(callee, _)
                    if expr_path(callee)
                        .as_deref()
                        .and_then(|path| path.rsplit("::").next())
                        == Some("replay") =>
                {
                    self.state = Some(())
                }
                _ => {}
            }
            visit::walk_expr(self, expr);
        }
    }
    let mut operations = Operations {
        assertion: None,
        state: None,
    };
    operations.visit_block(&loop_.body);
    let (Some(()), None) = (operations.assertion, operations.state) else {
        return;
    };
    let report = Report::new(
        "test loops over fixed cases and asserts inside one test",
        file.span(expr.span),
        "fixed cases share one test outcome",
    )
    .help(
        "give each case a named test, or generate a typed case that carries its expected behavior",
    );
    sink.emit(
        "literal-test-cases",
        file.item_span(function.span, function.attrs),
        &function.name,
        report,
    );
}

pub(crate) fn expr_path(expr: &ast::Expr) -> Option<String> {
    let ast::ExprKind::Path(_, path) = &expr.kind else {
        return None;
    };
    Some(path_name(path))
}

fn primitive_generator(expr: &ast::Expr) -> Option<()> {
    struct Primitive(Option<()>);
    impl<'a> Visitor<'a> for Primitive {
        fn visit_expr(&mut self, expr: &'a ast::Expr) {
            match &expr.kind {
                ast::ExprKind::Range(_, _, _) => self.0 = Some(()),
                ast::ExprKind::Call(callee, _) => {
                    if let Some("integers" | "booleans") = expr_path(callee)
                        .as_deref()
                        .and_then(|path| path.rsplit("::").next())
                    {
                        self.0 = Some(());
                    }
                }
                _ => {}
            }
            visit::walk_expr(self, expr);
        }
    }
    let mut primitive = Primitive(None);
    primitive.visit_expr(expr);
    primitive.0
}

fn check_primitive(
    sink: &mut Sink<'_>,
    file: &RustFile<'_>,
    function: &Function<'_>,
    body: &Body<'_>,
    expr: &ast::Expr,
) {
    let args = match &expr.kind {
        ast::ExprKind::MethodCall(call) if call.seg.ident.name.as_str() == "draw" => &call.args,
        ast::ExprKind::Call(callee, args)
            if expr_path(callee)
                .as_deref()
                .and_then(|path| path.rsplit("::").next())
                == Some("draw") =>
        {
            args
        }
        _ => return,
    };
    let Some(arg) = args.first() else { return };
    let Some(()) = primitive_generator(arg) else {
        return;
    };
    let matching = body.expressions.iter().find(|candidate| {
        let ast::ExprKind::Match(scrutinee, _, _) = &candidate.kind else {
            return false;
        };
        if scrutinee.span.contains(expr.span) {
            return true;
        }
        let Some(name) = expr_path(scrutinee) else {
            return false;
        };
        match body
            .binding(&name, candidate.span)
            .and_then(|binding| binding.initializer)
        {
            Some(initializer) => initializer.span.contains(expr.span),
            None => false,
        }
    });
    let Some(matching) = matching else { return };
    let report = Report::new("test matches on a primitive random choice", file.span(expr.span), "primitive draw controls this match")
        .label(file.span(matching.span), "the action mapping")
        .help("generate a typed action when these cases represent domain operations; keep numeric draws when testing a numeric or wire-format contract");
    sink.emit(
        "primitive-test-actions",
        file.item_span(function.span, function.attrs),
        &function.name,
        report,
    );
}

fn decimal(expr: &ast::Expr, file: &RustFile<'_>) -> Option<rustc_span::Span> {
    struct Decimal<'a, 'b> {
        file: &'a RustFile<'b>,
        literal: Option<rustc_span::Span>,
        symbol: Option<()>,
    }
    impl<'a> Visitor<'a> for Decimal<'_, '_> {
        fn visit_expr(&mut self, expr: &'a ast::Expr) {
            match &expr.kind {
                ast::ExprKind::Path(_, _) => self.symbol = Some(()),
                ast::ExprKind::Lit(lit) if lit.kind == rustc_ast::token::Integer => {
                    let text = self.file.text(expr.span);
                    if ["0x", "0o", "0b"]
                        .iter()
                        .all(|prefix| !text.starts_with(prefix))
                        && let None = self.literal
                    {
                        self.literal = Some(expr.span);
                    }
                }
                _ => {}
            }
            visit::walk_expr(self, expr);
        }
    }
    let mut decimal = Decimal {
        file,
        literal: None,
        symbol: None,
    };
    decimal.visit_expr(expr);
    match decimal.symbol {
        Some(()) => None,
        None => decimal.literal,
    }
}

fn decimal_cached(
    expr: &ast::Expr,
    file: &RustFile<'_>,
    cache: &mut FxHashMap<(u32, u32), Option<rustc_span::Span>>,
) -> Option<rustc_span::Span> {
    let key = (expr.span.lo().0, expr.span.hi().0);
    *cache.entry(key).or_insert_with(|| decimal(expr, file))
}

fn check_bound(
    sink: &mut Sink<'_>,
    file: &RustFile<'_>,
    item_span: Span,
    item_name: &str,
    expr: &ast::Expr,
    decimals: &mut FxHashMap<(u32, u32), Option<rustc_span::Span>>,
) {
    let selected = match &expr.kind {
        ast::ExprKind::MethodCall(call) => Some((
            call.seg.ident.name.to_string(),
            file.text(call.receiver.span).to_owned(),
            call.args.first().map(Box::as_ref),
        )),
        ast::ExprKind::Call(callee, args) => expr_path(callee).map(|path| {
            (
                path.rsplit("::")
                    .next()
                    .expect("a path has a segment")
                    .to_owned(),
                path,
                args.first().map(Box::as_ref),
            )
        }),
        _ => None,
    };
    let selected = match selected {
        Some((name, receiver, Some(arg)))
            if [
                "truncate",
                "take",
                "with_capacity",
                "retry",
                "max",
                "max_value",
                "max_size",
            ]
            .contains(&name.as_str()) =>
        {
            if name == "max"
                && !["gen", "generator", "proptest", "arbitrary", "sample"]
                    .iter()
                    .any(|word| receiver.to_ascii_lowercase().contains(word))
            {
                return;
            }
            decimal_cached(arg, file, decimals)
                .map(|span| (span, format!("numeric `{name}` bound")))
        }
        _ => {
            let ast::ExprKind::Binary(op, left, right) = &expr.kind else {
                return;
            };
            match op.node {
                ast::BinOpKind::Eq
                | ast::BinOpKind::Ne
                | ast::BinOpKind::Lt
                | ast::BinOpKind::Le
                | ast::BinOpKind::Gt
                | ast::BinOpKind::Ge => {}
                _ => return,
            }
            [(left, right), (right, left)]
                .into_iter()
                .find_map(|(subject, bound)| {
                    let text = file
                        .text(subject.span)
                        .replace(' ', "")
                        .to_ascii_lowercase();
                    if !text.ends_with(".len()") && !text.ends_with("length()") {
                        return None;
                    }
                    let span = decimal_cached(bound, file, decimals)?;
                    let text = file.text(span);
                    let digits = text
                        .split(|c: char| c.is_ascii_alphabetic())
                        .next()?
                        .replace('_', "");
                    match digits.parse::<u128>() {
                        Ok(0 | 1) => None,
                        _ => Some((span, "numeric length comparison".into())),
                    }
                })
        }
    };
    let Some((span, label)) = selected else {
        return;
    };
    let report = Report::new(
        "numeric bound may encode an unexplained policy",
        file.span(span),
        label,
    )
    .help("name a domain bound or document the resource or protocol limit that gives it meaning");
    sink.emit("arbitrary-bound", item_span, item_name, report);
}

fn check_comments(sink: &mut Sink<'_>, file: &RustFile<'_>, functions: &[Function<'_>]) {
    let mut ranges: Vec<_> = functions
        .iter()
        .map(|function| {
            let span = file.item_span(function.span, function.attrs);
            (span.start as usize, span.end as usize, function)
        })
        .collect();
    ranges.sort_by_key(|(start, _, _)| *start);
    let mut next_range = 0;
    let mut active = Vec::new();
    let mut offset = 0usize;
    for token in rustc_lexer::tokenize(file.text, rustc_lexer::FrontmatterAllowed::No) {
        let start = offset;
        offset += token.len as usize;
        match token.kind {
            rustc_lexer::TokenKind::LineComment { .. }
            | rustc_lexer::TokenKind::BlockComment { .. } => {}
            _ => continue,
        }
        let text = &file.text[start..offset];
        let content = comment_content(text);
        while let Some((range_start, _, _)) = ranges.get(next_range)
            && *range_start <= start
        {
            active.push(next_range);
            next_range += 1;
        }
        active.retain(|index| ranges[*index].1 >= offset);
        let next = file.text[offset..]
            .lines()
            .find(|line| !line.trim().is_empty())
            .map(str::trim);
        let function = active
            .iter()
            .min_by_key(|index| {
                let function = ranges[**index].2;
                function.span.hi().0 - function.span.lo().0
            })
            .map(|index| ranges[*index].2)
            .or_else(|| {
                ranges
                    .get(next_range)
                    .and_then(|(range_start, _, function)| {
                        (offset <= *range_start
                            && file.text[offset..*range_start].trim().is_empty())
                        .then_some(*function)
                    })
            });
        let kind = if text.starts_with("///") || text.starts_with("//!") {
            None
        } else {
            comment_kind(&content)
        };
        let kind = kind.or_else(|| {
            let next = next?;
            if next.starts_with("//") || next.starts_with("/*") {
                return None;
            }
            let comment = normalize_words(&content);
            if [
                "because",
                "invariant",
                "required",
                "otherwise",
                "safety",
                "must",
                "so that",
            ]
            .iter()
            .any(|word| comment.contains(word))
            {
                return None;
            }
            let mut masked = String::new();
            let mut at = 0usize;
            for token in rustc_lexer::tokenize(next, rustc_lexer::FrontmatterAllowed::No) {
                let end = at + token.len as usize;
                match token.kind {
                    rustc_lexer::TokenKind::Literal { .. } => masked.push(' '),
                    _ => masked.push_str(&next[at..end]),
                }
                at = end;
            }
            let next = normalize_words(&masked);
            let name =
                function.map(|function| normalize_words(function.function.ident.name.as_str()));
            if name.as_deref() == Some(comment.as_str())
                || (comment.split_whitespace().count() >= 2 && next.contains(&comment))
            {
                Some((
                    "comment repeats the adjacent signature or operation",
                    "restates code below",
                ))
            } else {
                None
            }
        });
        let Some((message, label)) = kind else {
            continue;
        };
        let span = Span {
            start: start as u32,
            end: offset as u32,
        };
        let (item_span, name) = match function {
            Some(function) => (
                file.item_span(function.span, function.attrs),
                function.name.as_str(),
            ),
            None => (span, "<item>"),
        };
        let report = Report::new(message, span, label).help("remove comments that add no information; keep comments that explain a non-obvious reason or invariant");
        sink.emit("redundant-comment", item_span, name, report);
    }
}

fn normalize_words(text: &str) -> String {
    text.chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || c == '_' {
                c.to_ascii_lowercase()
            } else {
                ' '
            }
        })
        .collect::<String>()
        .split_whitespace()
        .collect::<Vec<_>>()
        .join(" ")
}

fn comment_kind(content: &str) -> Option<(&'static str, &'static str)> {
    let lower = content.to_ascii_lowercase();
    if ["todo", "fixme", "xxx"]
        .iter()
        .any(|word| lower.starts_with(word))
    {
        return Some((
            "TODO comment remains in the source",
            "deferred work comment",
        ));
    }
    let separators = content.chars().filter(|c| "=-_*#~".contains(*c)).count();
    let words = content
        .split_whitespace()
        .filter(|word| word.chars().any(char::is_alphanumeric))
        .count();
    if separators >= 6 && words <= 2 {
        Some((
            "section-divider comment adds no information",
            "section divider",
        ))
    } else {
        None
    }
}

fn comment_content(text: &str) -> String {
    let text = text.trim();
    if let Some(rest) = text.strip_prefix("//") {
        return rest.trim_start_matches('/').trim().to_owned();
    }
    match text
        .strip_prefix("/*")
        .and_then(|rest| rest.strip_suffix("*/"))
    {
        Some(content) => content.trim().to_owned(),
        None => text.trim().to_owned(),
    }
}
