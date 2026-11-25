#![feature(rustc_private)]

use std::ops::Range;

use annotate_snippets::{
    AnnotationKind, Group, Level, Patch, Renderer, Snippet, renderer::DecorStyle,
};
use shapelint::{Finding, Footer, Kind, Label, Related, SourceInput, Span, Style, render};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Encoding {
    Lf,
    CrLf,
    BomLf,
    BomCrLf,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Line {
    Ascii,
    Unicode,
    Blank,
    Tab,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Extent {
    Token,
    MultipleLines,
    EmptyEnd,
    ThroughEnd,
    LineBoundary,
    Whole,
    EmptyStart,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Secondary {
    None,
    SameLine,
    SeparateLines,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Replacement {
    Token,
    MultipleLines,
    InsertEnd,
    Delete,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Ending {
    Newline,
    Text,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Color {
    Plain,
    Ansi,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Case {
    before: Vec<Line>,
    after: Vec<Line>,
    encoding: Encoding,
    extent: Extent,
    secondary: Secondary,
    replacement: Replacement,
    ending: Ending,
    color: Color,
}

#[hegel::test]
fn rendering_windows_preserve_full_source_diagnostics(tc: hegel::TestCase) {
    let Case {
        before,
        after,
        encoding,
        extent,
        secondary,
        replacement,
        ending,
        color,
    } = tc.draw(hegel::generators::default::<Case>());
    let mut text = String::new();
    for line in before {
        text.push_str(match line {
            Line::Ascii => "// prefix\n",
            Line::Unicode => "// λ🙂\n",
            Line::Blank => "\n",
            Line::Tab => "\t// indent\n",
        });
    }
    text.push_str("first();\nsecond(é);\nthird();\n");
    for line in after {
        text.push_str(match line {
            Line::Ascii => "// suffix\n",
            Line::Unicode => "// λ🙂\n",
            Line::Blank => "\n",
            Line::Tab => "\t// indent\n",
        });
    }
    match ending {
        Ending::Newline => {}
        Ending::Text => text.push_str("// final"),
    }
    let text = match encoding {
        Encoding::Lf => text,
        Encoding::CrLf => text.replace('\n', "\r\n"),
        Encoding::BomLf => format!("\u{feff}{text}"),
        Encoding::BomCrLf => format!("\u{feff}{}", text.replace('\n', "\r\n")),
    };
    let first = text.find("first").expect("first marker") as u32;
    let second = text.find("second").expect("second marker") as u32;
    let third = text.find("third").expect("third marker") as u32;
    let end = text.len() as u32;
    let span = match extent {
        Extent::Token => Span {
            start: second,
            end: second + "second(é)".len() as u32,
        },
        Extent::MultipleLines => Span {
            start: first,
            end: third + "third()".len() as u32,
        },
        Extent::EmptyEnd => Span { start: end, end },
        Extent::ThroughEnd => Span { start: third, end },
        Extent::LineBoundary => Span {
            start: first,
            end: second,
        },
        Extent::Whole => Span { start: 0, end },
        Extent::EmptyStart => Span { start: 0, end: 0 },
    };
    let labels = match secondary {
        Secondary::None => Vec::new(),
        Secondary::SameLine => vec![Label {
            span: Span {
                start: second,
                end: second + 6,
            },
            message: "same line".into(),
        }],
        Secondary::SeparateLines => vec![
            Label {
                span: Span {
                    start: first,
                    end: first + 5,
                },
                message: "first context".into(),
            },
            Label {
                span: Span {
                    start: third,
                    end: third + 5,
                },
                message: "third context".into(),
            },
        ],
    };
    let (patch, replacement) = match replacement {
        Replacement::Token => (
            Span {
                start: second,
                end: second + 6,
            },
            "changed",
        ),
        Replacement::MultipleLines => (
            Span {
                start: first,
                end: third + 8,
            },
            "replacement();\nnext();",
        ),
        Replacement::InsertEnd => (Span { start: end, end }, "\nappended();"),
        Replacement::Delete => (
            Span {
                start: first,
                end: second,
            },
            "",
        ),
    };
    let input = SourceInput::try_new("source.rs", &text).expect("generated source fits");
    let related = SourceInput::try_new("related.rs", &text).expect("generated source fits");
    let finding = Finding {
        rule: "render-window",
        kind: Kind::Lint,
        path: "source.rs".into(),
        line: 1,
        col: 1,
        item: "example".into(),
        item_span: Span { start: 0, end },
        message: "the complete diagnostic is preserved".into(),
        primary: Label {
            span,
            message: "primary".into(),
        },
        labels,
        related: vec![Related {
            input: related,
            label: Label {
                span,
                message: "related".into(),
            },
        }],
        footers: vec![
            Footer::Note {
                message: "note".into(),
            },
            Footer::Help {
                message: "help".into(),
            },
            Footer::Suggestion {
                message: "replace".into(),
                span: patch,
                replacement: replacement.into(),
            },
        ],
        fingerprint: "render-window".into(),
        source: None,
    };
    let style = match color {
        Color::Plain => Style::Plain,
        Color::Ansi => Style::Ansi,
    };
    assert_eq!(
        render(std::slice::from_ref(&finding), &input, style),
        full_source(&finding, &input, style),
        "{encoding:?}, {extent:?}, {secondary:?}, {ending:?}, {color:?}"
    );
}

#[test]
fn empty_source_rendering_keeps_its_one_line() {
    let input = SourceInput::try_new("empty.rs", "").expect("empty source");
    let finding = Finding {
        rule: "render-window",
        kind: Kind::Lint,
        path: "empty.rs".into(),
        line: 1,
        col: 1,
        item: "empty".into(),
        item_span: Span { start: 0, end: 0 },
        message: "empty source".into(),
        primary: Label {
            span: Span { start: 0, end: 0 },
            message: "here".into(),
        },
        labels: Vec::new(),
        related: Vec::new(),
        footers: Vec::new(),
        fingerprint: "empty".into(),
        source: None,
    };
    assert_eq!(
        render(std::slice::from_ref(&finding), &input, Style::Plain),
        full_source(&finding, &input, Style::Plain)
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum LabelPosition {
    Primary,
    Context,
    Related,
    Suggestion,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum InvalidRange {
    Reversed,
    PastEnd,
    InsideCharacter,
}

#[hegel::test]
fn a_malformed_label_keeps_the_diagnostic_title(tc: hegel::TestCase) {
    let (position, range) = tc.draw(hegel::generators::default::<(LabelPosition, InvalidRange)>());
    let input = SourceInput::try_new("source.rs", "abc\né\nz\n").unwrap();
    let valid = Span { start: 0, end: 3 };
    let span = match range {
        InvalidRange::Reversed => Span { start: 7, end: 1 },
        InvalidRange::PastEnd => Span { start: 4, end: 10 },
        InvalidRange::InsideCharacter => Span { start: 5, end: 6 },
    };
    let mut findings = shapelint::lint_compiler(
        &input,
        &shapelint::Config::default(),
        &[shapelint::CompilerFinding {
            item: "example".into(),
            item_span: valid,
            span: valid,
            evidence: shapelint::CompilerEvidence::UnnecessaryFallibility,
        }],
    )
    .unwrap();
    let [finding] = findings.as_mut_slice() else {
        panic!("expected one diagnostic")
    };
    let label = Label {
        span,
        message: "invalid".into(),
    };
    match position {
        LabelPosition::Primary => finding.primary = label,
        LabelPosition::Context => finding.labels.push(label),
        LabelPosition::Related => finding.related.push(Related {
            input: input.clone(),
            label,
        }),
        LabelPosition::Suggestion => finding.footers.push(Footer::Suggestion {
            message: "edit".into(),
            span,
            replacement: String::new(),
        }),
    }
    let output = render(std::slice::from_ref(finding), &input, Style::Plain);
    assert!(output.contains(&finding.message));
    assert!(output.contains("invalid source span"));
    assert!(output.contains("source.rs"));
}

fn full_source(finding: &Finding, input: &SourceInput, style: Style) -> String {
    let renderer = match style {
        Style::Plain => Renderer::plain(),
        Style::Ansi => Renderer::styled(),
    }
    .decor_style(DecorStyle::Unicode);
    let mut snippet = Snippet::source(input.as_ref())
        .path(input.name.as_ref())
        .annotation(
            AnnotationKind::Primary
                .span(Range::from(finding.primary.span))
                .label(finding.primary.message.as_str()),
        );
    for label in &finding.labels {
        snippet = snippet.annotation(
            AnnotationKind::Context
                .span(Range::from(label.span))
                .label(label.message.as_str()),
        );
    }
    let mut group = Group::with_title(
        Level::WARNING
            .with_name("lint")
            .primary_title(finding.message.as_str())
            .id(finding.rule),
    );
    for related in &finding.related {
        group = group.element(
            Snippet::source(related.input.as_ref())
                .path(related.input.name.as_ref())
                .annotation(
                    AnnotationKind::Context
                        .span(Range::from(related.label.span))
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
            } => patches.push(
                Group::with_title(Level::HELP.secondary_title(message.as_str())).element(
                    Snippet::source(input.as_ref())
                        .path(input.name.as_ref())
                        .patch(Patch::new(Range::from(*span), replacement.as_str())),
                ),
            ),
        }
    }
    let mut report = vec![group];
    report.extend(patches);
    format!("{}\n\n", renderer.render(&report))
}
