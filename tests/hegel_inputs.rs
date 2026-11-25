#![feature(rustc_private)]

use shapelint::{Config, Finding, SourceInput, lint};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum InputCase {
    Scattered,
    Branch,
    Assume,
    GeneratorFilter,
    RandomOperation,
    Clean,
}
#[hegel::test]
fn generated_input_shapes_report_their_local_rule(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<InputCase>());
    let (source, rule, expected) = match case {
        InputCase::Scattered => (
            "#[hegel::test]\nfn check(tc: TestCase) { let a = tc.draw(generated()); let b = tc.draw(generated()); use_(a, b); }",
            "hegel-scattered-draws",
            "tc.draw(generated())",
        ),
        InputCase::Branch => (
            "#[hegel::test]\nfn check(tc: TestCase) { let input = tc.draw(generated()); if input { use_(input); } }",
            "hegel-input-branch",
            "input",
        ),
        InputCase::Assume => (
            "#[hegel::test]\nfn check(tc: TestCase) { tc.assume(true); }",
            "hegel-assume",
            "assume",
        ),
        InputCase::GeneratorFilter => (
            "fn make() { let _ = generators::integers::<u8>().filter(|value| *value > 0); }",
            "hegel-generator-filter",
            "filter",
        ),
        InputCase::RandomOperation => (
            "impl Op { fn apply(&self, tc: &TestCase) { let _ = tc.draw(generated()); } }",
            "hegel-random-operation",
            "apply",
        ),
        InputCase::Clean => (
            "fn clean() { let _ = values.iter().filter(|value| **value > 0); }",
            "hegel-generator-filter",
            "",
        ),
    };
    let findings = findings_for("src/generated.rs", source);
    let matching: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == rule)
        .collect();
    assert_eq!(
        matching.len(),
        usize::from(!expected.is_empty()),
        "{source}"
    );
    if let Some(finding) = matching.first() {
        assert_eq!(
            &source[finding.primary.span.start as usize..finding.primary.span.end as usize],
            expected
        );
    }
}

#[test]
fn fixture_reports_inputs_and_respects_shadowing_and_suppression() {
    let text = include_str!("../fixtures/feedback/hegel_inputs/inputs.rs");
    let findings = findings_for("fixtures/feedback/hegel_inputs/inputs.rs", text);
    let count = |rule| {
        findings
            .iter()
            .filter(|finding| finding.rule == rule)
            .count()
    };
    assert_eq!(count("hegel-scattered-draws"), 2);
    assert_eq!(count("hegel-input-branch"), 3);
    assert_eq!(count("hegel-assume"), 1);
    assert_eq!(count("hegel-generator-filter"), 1);
    assert_eq!(count("hegel-random-operation"), 3);
    assert!(findings.iter().all(|finding| {
        !finding.item.contains("shadowed_input")
            && !finding.item.contains("loop_shadowed_input")
            && !finding.item.contains("if_let_shadowed_input")
    }));
    assert!(
        findings
            .iter()
            .all(|finding| !finding.item.contains("default_generator"))
    );
    assert!(
        findings
            .iter()
            .all(|finding| !finding.item.contains("Machine::apply"))
    );
    let fresh_draw = findings
        .iter()
        .find(|finding| {
            finding.rule == "hegel-input-branch"
                && finding.item.contains("loop_binding_then_fresh_draw")
        })
        .expect("fresh inner draw finding");
    assert_eq!(
        &text[fresh_draw.primary.span.start as usize..fresh_draw.primary.span.end as usize],
        "input"
    );
    assert!(findings.iter().all(|finding| {
        !finding.item.contains("match_shadowed_case")
            && !finding.item.contains("if_let_shadowed_case")
    }));
    let branch = findings
        .iter()
        .find(|finding| {
            finding.rule == "hegel-input-branch" && finding.item.contains("destructured")
        })
        .expect("destructured branch finding");
    assert_eq!(
        &text[branch.primary.span.start as usize..branch.primary.span.end as usize],
        "input"
    );
    let assume = findings
        .iter()
        .find(|finding| finding.rule == "hegel-assume")
        .expect("assume finding");
    assert_eq!(
        &text[assume.primary.span.start as usize..assume.primary.span.end as usize],
        "assume"
    );
}

fn findings_for(path: &str, text: &str) -> Vec<Finding> {
    let input = SourceInput::try_new(path, text).expect("fixture fits in a source input");
    lint(&input, &Config::default()).expect("fixture lints successfully")
}
