//! `shapelint: allow(rule, ...)` comments. Only real comments count, so the phrase in a
//! string literal neither suppresses anything nor gets reported.

use crate::text_syntax::{Token, TokenKind};
use crate::{LintError, SourceInput, Span};
use rustc_hash::FxHashMap;

pub(crate) const MARKER: &str = "shapelint: allow(";

pub(crate) struct Allow {
    lines: std::ops::RangeInclusive<usize>,
    pub(crate) name: String,
    pub(crate) span: Span,
}

/// Indexes the allow comments in one source file by line and rule.
#[derive(Default)]
pub struct Suppressions {
    by_rule: FxHashMap<String, LineIntervals>,
    all: LineIntervals,
}

#[derive(Default)]
struct LineIntervals {
    entries: Vec<(std::ops::RangeInclusive<usize>, Span)>,
    longest: Vec<usize>,
}

impl LineIntervals {
    // shapelint: allow(shallow-helper) This method is the interval-index insertion boundary.
    fn push(&mut self, allow: &Allow) {
        self.entries.push((allow.lines.clone(), allow.span));
    }

    // shapelint: allow(for-chain) This single pass records the prefix maximum for interval queries.
    fn finish(&mut self) {
        self.entries.sort_by_key(|(lines, _)| *lines.start());
        self.longest = Vec::with_capacity(self.entries.len());
        let mut longest = None;
        for (index, (lines, _)) in self.entries.iter().enumerate() {
            let best = match longest {
                Some((end, previous)) if end >= *lines.end() => (end, previous),
                _ => (*lines.end(), index),
            };
            self.longest.push(best.1);
            longest = Some(best);
        }
    }

    fn covers(&self, line: usize) -> Option<Span> {
        let end = self
            .entries
            .partition_point(|(lines, _)| *lines.start() <= line);
        let index = end
            .checked_sub(1)
            .and_then(|index| self.longest.get(index).copied())?;
        let (lines, span) = &self.entries[index];
        (lines.contains(&line) || line.checked_sub(1) == Some(*lines.end())).then_some(*span)
    }
}

impl Suppressions {
    /// Returns the directive covering a finding or its enclosing item's first line.
    /// Both line numbers are one-based and belong to the indexed source.
    pub fn for_finding(&self, rule: &str, line: usize, item_line: usize) -> Option<Span> {
        let for_line = |line| {
            self.by_rule
                .get(rule)
                .and_then(|intervals| intervals.covers(line))
                .or_else(|| self.all.covers(line))
        };
        [line, item_line].into_iter().find_map(for_line)
    }
}

impl From<Vec<Allow>> for Suppressions {
    fn from(allows: Vec<Allow>) -> Self {
        let mut by_rule: FxHashMap<_, LineIntervals> = FxHashMap::default();
        let mut all = LineIntervals::default();
        for allow in &allows {
            if allow.name == "all" {
                all.push(allow);
            } else {
                by_rule.entry(allow.name.clone()).or_default().push(allow);
            }
        }
        all.finish();
        for intervals in by_rule.values_mut() {
            intervals.finish();
        }
        Self { by_rule, all }
    }
}

struct CommentBlock {
    allows: Vec<Allow>,
    end: usize,
}

impl CommentBlock {
    fn finish(mut self, out: &mut Vec<Allow>) {
        for allow in &mut self.allows {
            allow.lines = *allow.lines.start()..=self.end;
        }
        out.append(&mut self.allows);
    }
}

/// Indexes directives in Rust comments using the source's original line numbers.
pub fn rust_suppressions(input: &SourceInput) -> Result<Suppressions, LintError> {
    use rustc_lexer::TokenKind::{BlockComment, Eof, LineComment, Whitespace};

    let text = input.as_ref();
    if !text.contains(MARKER) {
        return Ok(Suppressions::default());
    }
    let mut cursor = rustc_lexer::Cursor::new(text, rustc_lexer::FrontmatterAllowed::No);
    let mut line_at = input.text.line_cursor();
    let mut marker_line = input.text.line_cursor();
    let mut directives = Vec::new();
    let mut block: Option<CommentBlock> = None;
    let mut prefix_is_whitespace = true;
    loop {
        let before = cursor.as_str();
        let token = cursor.advance_token();
        if token.kind == Eof {
            break;
        }
        let body = before
            .get(..token.len as usize)
            .ok_or_else(|| LintError::Parse {
                name: input.name.to_string(),
            })?;
        let standalone = prefix_is_whitespace;
        prefix_is_whitespace = match body.rsplit_once('\n') {
            Some((_, last_line)) => last_line.chars().all(char::is_whitespace),
            None => standalone && body.chars().all(char::is_whitespace),
        };
        match token.kind {
            LineComment { doc_style: None }
            | BlockComment {
                doc_style: None, ..
            } => {
                if !standalone && let Some(finished) = block.take() {
                    finished.finish(&mut directives);
                }
                let marked = body.contains(MARKER);
                if !marked && block.is_none() {
                    continue;
                }
                let range = text.substr_range(body).ok_or_else(|| LintError::Parse {
                    name: input.name.to_string(),
                })?;
                let span = Span {
                    start: range.start as u32,
                    end: range.end as u32,
                };
                let start = line_at(span.start);
                if let Some(active) = &block
                    && start.checked_sub(1) != Some(active.end)
                    && let Some(finished) = block.take()
                {
                    finished.finish(&mut directives);
                    if !marked {
                        continue;
                    }
                }
                let end = line_at(span.end);
                let allows = if standalone {
                    let active = block.get_or_insert_with(|| CommentBlock {
                        end,
                        allows: Vec::new(),
                    });
                    active.end = end;
                    &mut active.allows
                } else {
                    &mut directives
                };
                if marked {
                    scan_comment(input, body, span, end, &mut marker_line, allows)?;
                }
            }
            Whitespace => {}
            _ => {
                if let Some(finished) = block.take() {
                    finished.finish(&mut directives);
                }
            }
        }
    }
    if let Some(finished) = block {
        finished.finish(&mut directives);
    }
    Ok(Suppressions::from(directives))
}

pub(crate) fn scan_hash_comments(
    input: &SourceInput,
    tokens: &[Token],
) -> Result<Suppressions, LintError> {
    let text = input.as_ref();
    let mut line_at = input.text.line_cursor();
    let mut marker_line = input.text.line_cursor();
    let mut allows = Vec::new();
    for token in tokens {
        if token.kind == TokenKind::Comment {
            let body = text.get(std::ops::Range::from(token.span)).ok_or_else(|| {
                LintError::InvalidSpan {
                    name: input.name.to_string(),
                    span: token.span,
                }
            })?;
            if body.contains(MARKER) {
                scan_comment(
                    input,
                    body,
                    token.span,
                    line_at(token.span.end),
                    &mut marker_line,
                    &mut allows,
                )?;
            }
        }
    }
    Ok(Suppressions::from(allows))
}

fn scan_comment(
    input: &SourceInput,
    mut comment: &str,
    span: Span,
    end_line: usize,
    marker_line: &mut impl FnMut(u32) -> usize,
    allows: &mut Vec<Allow>,
) -> Result<(), LintError> {
    let source = input.as_ref();
    let invalid = || LintError::InvalidSpan {
        name: input.name.to_string(),
        span,
    };
    while let Some((_, suffix)) = comment.split_once(MARKER) {
        comment = suffix;
        let Some((list, _)) = suffix.split_once(')') else {
            continue;
        };
        let start = source.substr_range(suffix).ok_or_else(invalid)?.start;
        let line = marker_line(start as u32);
        let names = list
            .split(',')
            .map(str::trim)
            .filter(|name| !name.is_empty());
        for name in names {
            let range = source.substr_range(name).ok_or_else(invalid)?;
            allows.push(Allow {
                lines: line..=end_line,
                name: name.to_owned(),
                span: Span {
                    start: range.start as u32,
                    end: range.end as u32,
                },
            });
        }
    }
    Ok(())
}
