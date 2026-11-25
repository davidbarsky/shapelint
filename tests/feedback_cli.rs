#![feature(rustc_private)]

use std::process::Command;

#[derive(serde::Deserialize)]
struct Footer {
    kind: String,
}

#[derive(serde::Deserialize)]
struct Diagnostic {
    rule: String,
    kind: String,
    line: u32,
    col: u32,
    footers: Vec<Footer>,
}

#[test]
fn cli_reports_feedback_fixtures_with_actionable_json_diagnostics() {
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures/feedback"))
        .args([
            "--format",
            "json",
            "--exit-zero",
            "api",
            "expressions",
            "tests",
            "bounds",
            "comments",
            "hegel_inputs",
            "hegel_policy",
        ])
        .output()
        .expect("run fixture CLI");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stderr, b"");
    let output = String::from_utf8(output.stdout).expect("UTF-8 diagnostics");
    let diagnostics: Vec<Diagnostic> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("diagnostic JSON"))
        .collect();
    let expected = [
        "matches-macro",
        "boolean-state",
        "error-erasure",
        "implicit-dependency",
        "json-in-domain",
        "conversion-trait",
        "parallel-api",
        "collection-choice",
        "literal-test-cases",
        "primitive-test-actions",
        "hegel-local-case-budget",
        "hegel-scattered-draws",
        "hegel-input-branch",
        "hegel-assume",
        "hegel-generator-filter",
        "hegel-random-operation",
        "hegel-fixed-seed",
        "hegel-health-check",
        "hegel-sampled-invariant",
        "hegel-rule-weight",
        "hegel-early-exit",
        "arbitrary-bound",
        "redundant-comment",
        "compatibility-scaffolding",
        "shallow-helper",
    ];
    let missing: Vec<_> = expected
        .into_iter()
        .filter(|rule| {
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.rule == *rule)
        })
        .collect();
    assert_eq!(
        missing,
        Vec::<&str>::new(),
        "fixture rules missing from CLI output"
    );
    for diagnostic in diagnostics {
        assert!(diagnostic.line > 0 && diagnostic.col > 0);
        assert!(
            diagnostic
                .footers
                .iter()
                .any(|footer| footer.kind == "help" || footer.kind == "suggestion")
        );
        assert_eq!(diagnostic.kind, "lint", "{}", diagnostic.rule);
    }
}

#[test]
fn mechanical_filter_selects_policy_rules_at_the_common_lint_level() {
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures/feedback"))
        .args([
            "--format",
            "json",
            "--only",
            "mechanical",
            "expressions/matches.rs",
        ])
        .output()
        .expect("run mechanical fixture CLI");
    assert_eq!(output.status.code(), Some(1));
    let output = String::from_utf8(output.stdout).expect("UTF-8 diagnostics");
    let diagnostics: Vec<Diagnostic> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("diagnostic JSON"))
        .collect();
    assert_eq!(diagnostics.len(), 3);
    for diagnostic in diagnostics {
        assert_eq!(diagnostic.rule, "matches-macro");
        assert_eq!(diagnostic.kind, "lint");
    }
}
