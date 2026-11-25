//! Findings as data, and their rendering.

use annotate_snippets::{
    AnnotationKind, Group, Level, Patch, Renderer, Snippet, renderer::DecorStyle,
};
use serde::Serialize;

use crate::{Kind, LintError, SourceInput, Span};

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
    /// The enclosing item's text, when requested.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
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
