#![feature(rustc_private)]

use shapelint::{Config, Finding, SourceInput, lint};

fn fixture(path: &str, text: &'static str) -> Vec<Finding> {
    let input = SourceInput::try_new(path, text).expect("fixture fits in a source input");
    lint(&input, &Config::default()).expect("fixture lints successfully")
}

#[test]
fn matches_macro_reports_exact_invocations_and_ignores_text() {
    let text = include_str!("../fixtures/feedback/expressions/matches.rs");
    let findings = fixture("src/matches.rs", text);
    let matches: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "matches-macro")
        .collect();
    assert_eq!(matches.len(), 3);
    assert_eq!(
        matches
            .iter()
            .map(|finding| {
                &text[finding.primary.span.start as usize..finding.primary.span.end as usize]
            })
            .collect::<Vec<_>>(),
        ["matches", "core::matches", "std::matches"]
    );
}

#[test]
fn boolean_state_reports_domain_shapes_and_respects_boundaries() {
    let text = include_str!("../fixtures/feedback/expressions/booleans.rs");
    let findings = fixture("src/booleans.rs", text);
    let booleans: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "boolean-state")
        .collect();
    assert_eq!(booleans.len(), 10);
    assert_eq!(
        booleans
            .iter()
            .map(|finding| {
                &text[finding.primary.span.start as usize..finding.primary.span.end as usize]
            })
            .collect::<Vec<_>>(),
        [
            "bool",
            "Result<bool, String>",
            "Vec<bool>",
            "bool",
            "(bool, u8)",
            "bool",
            "bool",
            "bool",
            "bool",
            "Result<bool, String>"
        ]
    );
}

#[test]
fn error_erasure_reports_ok_filters_and_discarding_match_arms() {
    let text = include_str!("../fixtures/feedback/expressions/errors.rs");
    let findings = fixture("src/errors.rs", text);
    let erasures: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "error-erasure")
        .collect();
    assert_eq!(erasures.len(), 7);
    assert_eq!(
        &text[erasures[0].primary.span.start as usize..erasures[0].primary.span.end as usize],
        "ok"
    );
    assert_eq!(
        &text[erasures[1].primary.span.start as usize..erasures[1].primary.span.end as usize],
        "Result::ok"
    );
    assert_eq!(
        &text[erasures[2].primary.span.start as usize..erasures[2].primary.span.end as usize],
        "Err(_)"
    );
    assert_eq!(
        &text[erasures[3].primary.span.start as usize..erasures[3].primary.span.end as usize],
        "Err(_)"
    );
    assert_eq!(
        &text[erasures[4].primary.span.start as usize..erasures[4].primary.span.end as usize],
        "Err(_)"
    );
    assert_eq!(
        &text[erasures[5].primary.span.start as usize..erasures[5].primary.span.end as usize],
        "other::Err(_)"
    );
    assert_eq!(
        &text[erasures[6].primary.span.start as usize..erasures[6].primary.span.end as usize],
        "Err(_)"
    );
}

#[test]
fn implicit_dependency_reports_context_macros_and_global_state() {
    let text = include_str!("../fixtures/feedback/expressions/dependencies.rs");
    let findings = fixture("src/dependencies.rs", text);
    let dependencies: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "implicit-dependency")
        .collect();
    assert_eq!(dependencies.len(), 4);
    assert_eq!(
        &text[dependencies[0].primary.span.start as usize
            ..dependencies[0].primary.span.end as usize],
        "thread_local"
    );
    assert_eq!(
        &text[dependencies[1].primary.span.start as usize
            ..dependencies[1].primary.span.end as usize],
        "tokio::task_local"
    );
    assert!(
        &text[dependencies[2].primary.span.start as usize
            ..dependencies[2].primary.span.end as usize]
            .contains("static mut GLOBAL_STATE")
    );
    assert!(
        &text[dependencies[3].primary.span.start as usize
            ..dependencies[3].primary.span.end as usize]
            .contains("static CONTEXT")
    );
}

#[test]
fn json_macro_extension_reports_unqualified_and_qualified_calls() {
    let text = include_str!("../fixtures/feedback/expressions/json.rs");
    let findings = fixture("src/json.rs", text);
    let json: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "json-in-domain")
        .collect();
    assert_eq!(json.len(), 3);
    assert_eq!(
        json.iter()
            .map(|finding| {
                &text[finding.primary.span.start as usize..finding.primary.span.end as usize]
            })
            .collect::<Vec<_>>(),
        ["json", "serde_json::json", "serde_json::json"]
    );
}

#[test]
fn json_boundary_and_allow_suppression_are_honored() {
    let text = include_str!("../fixtures/feedback/expressions/json.rs");
    let input = SourceInput::try_new("src/wire/json.rs", text).expect("fixture fits");
    let config = Config {
        json_boundary: vec!["src/wire".parse().expect("valid path pattern")],
        ..Config::default()
    };
    let findings = lint(&input, &config).expect("fixture lints successfully");
    assert!(
        findings
            .iter()
            .all(|finding| finding.rule != "json-in-domain")
    );

    let suppressed = include_str!("../fixtures/feedback/expressions/suppressed.rs");
    let findings = fixture("src/suppressed.rs", suppressed);
    let matches: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "matches-macro")
        .collect();
    assert_eq!(matches.len(), 1);
    assert_eq!(
        &suppressed[matches[0].primary.span.start as usize..matches[0].primary.span.end as usize],
        "matches"
    );
}
