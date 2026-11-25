#![feature(rustc_private)]

use shapelint::{Config, SourceInput, lint};

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum MacroArgument {
    Invocation,
    String,
    RawString,
    Comment,
}

#[hegel::test]
fn macro_review_distinguishes_invocations_from_token_text(tc: hegel::TestCase) {
    let argument = tc.draw(hegel::generators::default::<MacroArgument>());
    let (argument, expected) = match argument {
        MacroArgument::Invocation => ("core::matches!(value, Some(_))", Some("core::matches")),
        MacroArgument::String => ("\"core::matches!(value, Some(_))\"", None),
        MacroArgument::RawString => ("r###\"core::matches!(value, Some(_))\"###", None),
        MacroArgument::Comment => ("/* core::matches!(value, Some(_)) */ value", None),
    };
    let source = format!("fn observe() {{ outer!({argument}); }}");
    let input = SourceInput::try_new("src/example.rs", &source).expect("small fixture");
    let findings = lint(&input, &Config::default()).expect("fixture lints");
    let findings: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "matches-macro")
        .collect();
    match expected {
        Some(expected) => {
            assert_eq!(findings.len(), 1);
            let span = findings[0].primary.span;
            assert_eq!(&source[span.start as usize..span.end as usize], expected);
        }
        None => assert!(findings.is_empty()),
    }
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum BooleanBoundary {
    Domain,
    Serde,
    CRepresentation,
    Callback,
}

#[hegel::test]
fn boolean_review_preserves_wire_and_callback_boundaries(tc: hegel::TestCase) {
    let boundary = tc.draw(hegel::generators::default::<BooleanBoundary>());
    let (source, expected) = match boundary {
        BooleanBoundary::Domain => ("struct State { value: Option<bool> }", 1),
        BooleanBoundary::Serde => (
            "#[derive(serde::Serialize)] struct State { value: Option<bool> }",
            0,
        ),
        BooleanBoundary::CRepresentation => ("#[repr(C)] struct State { value: bool }", 0),
        BooleanBoundary::Callback => ("struct State { callback: Option<fn() -> bool> }", 0),
    };
    let input = SourceInput::try_new("src/example.rs", source).expect("small fixture");
    let findings = lint(&input, &Config::default()).expect("fixture lints");
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "boolean-state")
            .count(),
        expected
    );
}
