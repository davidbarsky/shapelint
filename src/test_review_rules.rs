//! Test-shape and source-comment rules over rustc's written AST.

use rustc_ast::{
    ast,
    visit::{self, Visitor},
};

use crate::Span;
use crate::diagnostic::{Report, Sink};
use crate::rust_syntax::RustFile;

pub(crate) struct Function<'a> {
    pub function: &'a ast::Fn,
    pub attrs: &'a [ast::Attribute],
    pub span: rustc_span::Span,
    pub name: String,
}

pub(crate) fn functions<'a>(file: &RustFile<'a>) -> Vec<Function<'a>> {
    struct Collect<'a> {
        functions: Vec<Function<'a>>,
        implementation: Option<&'a ast::Item>,
        scope: Vec<String>,
    }
    impl<'a> Visitor<'a> for Collect<'a> {
        fn visit_item(&mut self, item: &'a ast::Item) {
            let implementation = self.implementation;
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
                    });
                    self.scope.push(function.ident.name.to_string());
                }
                _ => {}
            }
            visit::walk_item(self, item);
            self.scope.truncate(scope);
            self.implementation = implementation;
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
                });
            }
            visit::walk_assoc_item(self, item, ctxt);
        }
    }
    let mut visitor = Collect {
        functions: Vec::new(),
        implementation: None,
        scope: Vec::new(),
    };
    visitor.visit_crate(file.krate);
    visitor.functions
}

pub(crate) fn lint(sink: &mut Sink<'_>, file: &RustFile<'_>) {
    check_comments(sink, file, &functions(file));
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
