//! Findings as data, and their rendering.

use std::ops::Range;

use annotate_snippets::{
    AnnotationKind, Group, Level, Patch, Renderer, Snippet, renderer::DecorStyle,
};
use serde::Serialize;

use crate::config::{Config, SourceMode};
use crate::source::{LintError, Position, SourceInput};
use crate::suggest::{Code, suggest};
use crate::suppress::{MARKER, Suppressions};
use crate::{Kind, RULES, Span};

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
pub enum Footer {
    Note {
        message: String,
    },
    Help {
        message: String,
    },
    /// A machine-applicable edit: replace `span` with `replacement`.
    Suggestion {
        message: String,
        span: Span,
        replacement: String,
    },
}

#[derive(Clone, Debug, Serialize)]
pub struct Related {
    pub input: SourceInput,
    pub label: Label,
}

#[derive(Clone, Debug, Serialize)]
pub struct Finding {
    pub rule: &'static str,
    pub kind: Kind,
    pub path: String,
    /// 1-based position of the primary label.
    pub line: usize,
    pub col: usize,
    /// Enclosing item, e.g. `fn row_images` or `struct Stamp`.
    pub item: String,
    /// The enclosing item's span, so a reviewer can be handed exactly that slice.
    pub item_span: Span,
    pub message: String,
    pub primary: Label,
    /// Secondary labels, in source order.
    pub labels: Vec<Label>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub related: Vec<Related>,
    pub footers: Vec<Footer>,
    /// Versioned stable identifier used for deduplication and hook state.
    pub fingerprint: String,
    /// The enclosing item's text, when `Config::with_source` includes it.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
}

/// What a rule reports; [`Sink::emit`] turns it into a [`Finding`].
pub(crate) struct Report {
    message: String,
    primary: Label,
    labels: Vec<Label>,
    related: Vec<Related>,
    footers: Vec<Footer>,
}

impl Report {
    pub(crate) fn new(
        message: impl Into<String>,
        at: impl Into<Span>,
        label: impl Into<String>,
    ) -> Report {
        Report {
            message: message.into(),
            primary: Label {
                span: at.into(),
                message: label.into(),
            },
            labels: Vec::new(),
            related: Vec::new(),
            footers: Vec::new(),
        }
    }

    pub(crate) fn label(mut self, at: impl Into<Span>, message: impl Into<String>) -> Report {
        self.labels.push(Label {
            span: at.into(),
            message: message.into(),
        });
        self
    }

    pub(crate) fn help(mut self, message: impl Into<String>) -> Report {
        self.footers.push(Footer::Help {
            message: message.into(),
        });
        self
    }

    pub(crate) fn suggest(
        mut self,
        message: impl Into<String>,
        at: impl Into<Span>,
        replacement: impl Into<String>,
    ) -> Report {
        self.footers.push(Footer::Suggestion {
            message: message.into(),
            span: at.into(),
            replacement: replacement.into(),
        });
        self
    }
}

/// Collects findings for one source, applying suppressions and computing positions.
pub(crate) struct Sink<'a> {
    input: &'a SourceInput,
    config: &'a Config,
    suppressions: &'a Suppressions,
    findings: Result<Vec<Finding>, LintError>,
    items: rustc_hash::FxHashMap<Span, ItemCache>,
}

struct ItemCache {
    digest: String,
    source: Option<String>,
}

impl<'a> Sink<'a> {
    pub(crate) fn new(
        input: &'a SourceInput,
        config: &'a Config,
        suppressions: &'a Suppressions,
    ) -> Sink<'a> {
        Sink {
            input,
            config,
            suppressions,
            findings: Ok(Vec::new()),
            items: rustc_hash::FxHashMap::default(),
        }
    }

    /// Reports misspelled rule names in suppression comments.
    pub(crate) fn report_unknown(&mut self) {
        let known = || RULES.iter().map(|r| r.id).chain(std::iter::once("all"));
        let unknown = self.suppressions.unknown();
        for allow in unknown {
            let name = allow.name.as_str();
            let span = allow.span;
            let mut report = Report::new(
                format!(
                    "{} names a rule that doesn't exist",
                    Code(format!("{MARKER}{name})"))
                ),
                span,
                format!("no rule named {}", Code(name)),
            );
            report = match suggest(name, known()) {
                Some(close) => {
                    report.suggest(format!("did you mean {}?", Code(close)), span, close)
                }
                None => report.help("run `shapelint rules` to list the rule names"),
            };
            self.emit("unknown-allow", span, "allow comment", report);
        }
    }

    /// `item` is the enclosing item's span: its text goes into the fingerprint, and a
    /// suppression on its first line covers every finding inside it.
    pub(crate) fn emit(
        &mut self,
        id: &'static str,
        item: Span,
        item_name: impl Into<String>,
        mut report: Report,
    ) {
        let Some(rule) = RULES.iter().find(|r| r.id == id) else {
            unreachable!("rule `{id}` is not in RULES")
        };
        let Some(item_text) = self.input.as_ref().get(Range::from(item)) else {
            self.findings = Err(LintError::InvalidSpan {
                name: self.input.name.to_string(),
                span: item,
            });
            return;
        };
        if let Some(set) = self.config.only
            && let None = set.select(rule)
        {
            return;
        }
        let Position { line, col } = self.input.text.line_col(report.primary.span.start);
        let Position {
            line: item_line,
            col: _,
        } = self.input.text.line_col(item.start);
        if let Some(_) = self.suppressions.for_finding(id, line, item_line) {
            return;
        }
        report.labels.sort_by_key(|l| l.span);
        let item_name = item_name.into();
        // The primary label's offset within the item separates otherwise identical findings
        // (two `for_each` calls in one function) without depending on where the item sits.
        let within = report
            .primary
            .span
            .start
            .saturating_sub(item.start)
            .to_string();
        let source_mode = self.config.with_source;
        let source_lines = self.config.t.source_lines;
        let cache = self.items.entry(item).or_insert_with(|| {
            let normalized = item_text.split_whitespace().collect::<Vec<_>>().join(" ");
            ItemCache {
                digest: fnv1a(&[&normalized]),
                source: match source_mode {
                    SourceMode::Include => Some(cap_lines(item_text, source_lines)),
                    SourceMode::Omit => None,
                },
            }
        });
        let fingerprint = format!(
            "v2:{}",
            fnv1a(&[
                &cache.digest,
                id,
                &self.input.name,
                &item_name,
                &report.message,
                &within,
            ])
        );
        let source = cache.source.clone();
        let Ok(findings) = &mut self.findings else {
            return;
        };
        findings.push(Finding {
            rule: id,
            kind: rule.kind(),
            path: self.input.name.to_string(),
            line,
            col,
            item: item_name,
            item_span: item,
            message: report.message,
            primary: report.primary,
            labels: report.labels,
            related: report.related,
            footers: report.footers,
            fingerprint,
            source,
        });
    }

    /// Findings in source order. The sort is stable, so findings sharing a primary span keep
    /// emission order, which rules produce in source order.
    pub(crate) fn finish(self) -> Result<Vec<Finding>, LintError> {
        let mut findings = self.findings?;
        findings.sort_by_key(|f| f.primary.span);
        // Identical text (two equal config lines) gives identical fingerprints; an occurrence
        // ordinal keeps them distinct so the hook's dedupe never hides a finding.
        let mut next_ordinal: rustc_hash::FxHashMap<&str, usize> = rustc_hash::FxHashMap::default();
        for finding in &mut findings {
            if let Some(ordinal) = next_ordinal.get_mut(finding.fingerprint.as_str()) {
                finding.fingerprint = format!(
                    "v2:{}",
                    fnv1a(&[&finding.fingerprint, &ordinal.to_string()])
                );
                *ordinal += 1;
            } else {
                next_ordinal.insert(&finding.fingerprint, 1);
            }
        }
        Ok(findings)
    }
}

/// FNV-1a: stable across builds and runs, unlike `DefaultHasher`.
pub(crate) fn fnv1a(parts: &[&str]) -> String {
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325;
    for part in parts {
        let bytes = part.bytes().chain(std::iter::once(0xff));
        for byte in bytes {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x0100_0000_01b3);
        }
    }
    format!("{hash:016x}")
}

fn cap_lines(text: &str, max: usize) -> String {
    let lines: Vec<&str> = text.lines().collect();
    if lines.len() <= max {
        text.to_string()
    } else {
        format!(
            "{}\n… ({} more lines)",
            lines[..max].join("\n"),
            lines.len() - max
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Style {
    Plain,
    Ansi,
}

/// Renders findings for one source as annotated snippets.
///
/// If a label refers to invalid byte offsets, the diagnostic includes its title and
/// the offending source location.
pub fn render(findings: &[Finding], input: &SourceInput, style: Style) -> String {
    let renderer = match style {
        Style::Plain => Renderer::plain(),
        Style::Ansi => Renderer::styled(),
    }
    .decor_style(DecorStyle::Unicode);
    let mut out = String::new();
    for finding in findings {
        let rendered = match render_finding(&renderer, finding, input) {
            Ok(rendered) => rendered,
            Err(error) => {
                let message = error.to_string();
                let group = Group::with_title(
                    finding
                        .kind
                        .level()
                        .primary_title(finding.message.as_str())
                        .id(finding.rule),
                )
                .element(Level::NOTE.message(message.as_str()));
                renderer.render(&[group])
            }
        };
        out.push_str(&rendered);
        out.push_str("\n\n");
    }
    out
}

impl Kind {
    fn level(self) -> Level<'static> {
        match self {
            Kind::AnalysisGap => Level::NOTE,
            Kind::Lint => Level::WARNING,
        }
        .with_name(self.label())
    }
}

fn render_finding(
    renderer: &Renderer,
    finding: &Finding,
    input: &SourceInput,
) -> Result<String, LintError> {
    let mut extent = finding.primary.span;
    for label in &finding.labels {
        extent.start = extent.start.min(label.span.start);
        extent.end = extent.end.max(label.span.end);
    }
    let window = input.window(extent)?;
    let mut snippet = Snippet::source(window.text)
        .line_start(window.line)
        .path(input.name.as_ref())
        .annotation(
            AnnotationKind::Primary
                .span(window.relative(finding.primary.span)?)
                .label(finding.primary.message.as_str()),
        );
    for label in &finding.labels {
        snippet = snippet.annotation(
            AnnotationKind::Context
                .span(window.relative(label.span)?)
                .label(label.message.as_str()),
        );
    }
    let mut group = Group::with_title(
        finding
            .kind
            .level()
            .primary_title(finding.message.as_str())
            .id(finding.rule),
    );
    for related in &finding.related {
        let window = related.input.window(related.label.span)?;
        group = group.element(
            Snippet::source(window.text)
                .line_start(window.line)
                .path(related.input.name.as_ref())
                .annotation(
                    AnnotationKind::Context
                        .span(window.relative(related.label.span)?)
                        .label(related.label.message.as_str()),
                ),
        );
    }
    group = group.element(snippet);
    let mut patches = Vec::new();
    for footer in &finding.footers {
        match footer {
            Footer::Note { message } => {
                group = group.element(Level::NOTE.message(message.as_str()))
            }
            Footer::Help { message } => {
                group = group.element(Level::HELP.message(message.as_str()))
            }
            Footer::Suggestion {
                message,
                span,
                replacement,
            } => {
                let window = input.window(*span)?;
                patches.push(
                    Group::with_title(Level::HELP.secondary_title(message.as_str())).element(
                        Snippet::source(window.text)
                            .line_start(window.line)
                            .path(input.name.as_ref())
                            .patch(Patch::new(window.relative(*span)?, replacement.as_str())),
                    ),
                );
            }
        }
    }
    let mut report = vec![group];
    report.extend(patches);
    Ok(renderer.render(&report))
}
