#![feature(rustc_private)]

use shapelint::{
    CompilerEvidence, CompilerFinding, Config, LintError, SourceInput, Span, lint_compiler,
};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum RangeCase {
    Whole,
    EmptyEnd,
    Reversed,
    PastEnd,
    SplitCharacter,
    MaximumOffset,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Field {
    Item,
    Primary,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Suppression {
    Absent,
    Present,
}

#[hegel::test]
fn compiler_spans_are_checked_before_suppression(tc: hegel::TestCase) {
    let (field, case, suppression) =
        tc.draw(hegel::generators::default::<(Field, RangeCase, Suppression)>());
    let (prefix, expected_findings) = match suppression {
        Suppression::Present => ("// shapelint: allow(unnecessary-fallibility)\n", 0),
        Suppression::Absent => ("", 1),
    };
    let input = SourceInput::try_new("src/lib.rs", format!("{prefix}// λ\n")).expect("fixture");
    let start = prefix.len() as u32;
    let end = start + 6;
    let valid = Span { start, end };
    let span = match case {
        RangeCase::Whole => valid,
        RangeCase::EmptyEnd => Span { start: end, end },
        RangeCase::Reversed => Span {
            start: end,
            end: start,
        },
        RangeCase::PastEnd => Span {
            start,
            end: end + 1,
        },
        RangeCase::SplitCharacter => Span {
            start: start + 4,
            end: start + 5,
        },
        RangeCase::MaximumOffset => Span {
            start: u32::MAX,
            end: u32::MAX,
        },
    };
    let (item_span, primary_span) = match field {
        Field::Item => (span, valid),
        Field::Primary => (valid, span),
    };
    let evidence = CompilerFinding {
        item: "fixture".into(),
        item_span,
        span: primary_span,
        evidence: CompilerEvidence::UnnecessaryFallibility,
    };
    let result = lint_compiler(&input, &Config::default(), &[evidence]);
    match (case, result) {
        (RangeCase::Whole | RangeCase::EmptyEnd, Ok(findings)) => {
            assert_eq!(findings.len(), expected_findings);
        }
        (
            RangeCase::Reversed
            | RangeCase::PastEnd
            | RangeCase::SplitCharacter
            | RangeCase::MaximumOffset,
            Err(LintError::InvalidSpan {
                name,
                span: rejected,
            }),
        ) => {
            assert_eq!(name, input.name.as_ref());
            assert_eq!(rejected, span);
        }
        (_, result) => panic!("{case:?}: {result:?}"),
    }
}
