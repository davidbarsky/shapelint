#![feature(rustc_private)]

use shapelint::{Config, Finding, SourceInput, lint};

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum TestAttributeCase {
    Seed,
    DerandomizeTrue,
    DerandomizeFalse,
    Ordinary,
    Nested,
    StringLiteral,
}

fn findings_for(path: &str, text: &str) -> Vec<Finding> {
    let input = SourceInput::try_new(path, text).expect("fixture source fits in u32");
    lint(&input, &Config::default()).expect("fixture parses")
}

#[test]
fn hegel_policy_reports_settings_and_state_machine_advice() {
    let text = include_str!("../fixtures/feedback/hegel_policy/positive.rs");
    let findings = findings_for("fixtures/feedback/hegel_policy/positive.rs", text);
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "hegel-fixed-seed")
            .map(|finding| &text
                [finding.primary.span.start as usize..finding.primary.span.end as usize])
            .collect::<Vec<_>>(),
        ["seed", "derandomize", "derandomize"]
    );
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "hegel-health-check")
            .map(|finding| &text
                [finding.primary.span.start as usize..finding.primary.span.end as usize])
            .collect::<Vec<_>>(),
        ["suppress_health_check"]
    );
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "hegel-sampled-invariant")
            .map(|finding| &text
                [finding.primary.span.start as usize..finding.primary.span.end as usize])
            .collect::<Vec<_>>(),
        ["invariant"]
    );
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "hegel-rule-weight")
            .map(|finding| &text
                [finding.primary.span.start as usize..finding.primary.span.end as usize])
            .collect::<Vec<_>>(),
        ["weight"]
    );
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "hegel-early-exit")
            .map(|finding| &text
                [finding.primary.span.start as usize..finding.primary.span.end as usize])
            .collect::<Vec<_>>(),
        ["break", "return", "break"]
    );
}

// shapelint: allow(literal-test-cases) Cross-size controls exercise indexed nested scopes and exits.
#[test]
fn hegel_policy_scales_nested_no_hit_and_many_exit_bodies() {
    let depth = 16;
    let mut nested = String::from("#[hegel::test]\nfn nested_no_hit() {\n");
    for _ in 0..depth {
        nested.push_str("for item in values {\n");
    }
    nested.push_str("observe();\n");
    for _ in 0..depth {
        nested.push_str("}\n");
    }
    nested.push_str("}\n");
    let nested_findings = findings_for("src/nested_no_hit.rs", &nested);
    assert!(
        !nested_findings
            .iter()
            .any(|finding| finding.rule == "hegel-early-exit")
    );

    let exits = 64;
    let mut many_exits =
        String::from("#[hegel::test]\nfn many_exits() {\nfor action in history {\n");
    for _ in 0..exits {
        many_exits.push_str("if let Err(error) = apply(action) { record(error); return; }\n");
    }
    many_exits.push_str("}\n}\n");
    let many_findings = findings_for("src/many_exits.rs", &many_exits);
    assert_eq!(
        many_findings
            .iter()
            .filter(|finding| finding.rule == "hegel-early-exit")
            .count(),
        exits
    );
}

#[test]
fn hegel_policy_ignores_non_fixed_and_non_hegel_shapes() {
    let text = include_str!("../fixtures/feedback/hegel_policy/negative.rs");
    let findings = findings_for("fixtures/feedback/hegel_policy/negative.rs", text);
    let policy_rules = [
        "hegel-fixed-seed",
        "hegel-health-check",
        "hegel-sampled-invariant",
        "hegel-rule-weight",
        "hegel-early-exit",
    ];
    assert!(
        findings
            .iter()
            .all(|finding| !policy_rules.contains(&finding.rule)),
        "unexpected Hegel policy finding: {findings:?}"
    );
}

#[test]
fn hegel_policy_respects_rule_suppressions() {
    let text = include_str!("../fixtures/feedback/hegel_policy/suppressed.rs");
    let findings = findings_for("fixtures/feedback/hegel_policy/suppressed.rs", text);
    let policy_rules = [
        "hegel-fixed-seed",
        "hegel-health-check",
        "hegel-sampled-invariant",
        "hegel-rule-weight",
        "hegel-early-exit",
    ];
    assert!(
        findings
            .iter()
            .all(|finding| !policy_rules.contains(&finding.rule)),
        "suppressed Hegel policy finding: {findings:?}"
    );
}

#[hegel::test]
fn hegel_test_settings_are_classified_from_typed_cases(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<TestAttributeCase>());
    let (attribute, expected) = match case {
        TestAttributeCase::Seed => ("#[hegel::test( seed = 9 )]", Some("seed")),
        TestAttributeCase::DerandomizeTrue => {
            ("#[hegel::test(derandomize = true)]", Some("derandomize"))
        }
        TestAttributeCase::DerandomizeFalse => {
            ("#[hegel::test(derandomize = false)]", Some("derandomize"))
        }
        TestAttributeCase::Ordinary => ("#[hegel::test]", None),
        TestAttributeCase::Nested => (
            "#[hegel::test(note(test_cases = 1), note = \"seed = 7\")]",
            None,
        ),
        TestAttributeCase::StringLiteral => (
            "#[some_other::test(note = \"seed = 7\", derandomize = true)]",
            None,
        ),
    };
    let text = format!("{attribute}\nfn generated_settings_case() {{}}\n");
    let findings = findings_for("src/generated_settings_case.rs", &text);
    let policy: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "hegel-fixed-seed")
        .collect();
    match expected {
        Some(name) => {
            assert_eq!(policy.len(), 1);
            let finding = policy[0];
            assert_eq!(
                &text[finding.primary.span.start as usize..finding.primary.span.end as usize],
                name
            );
        }
        None => assert!(policy.is_empty()),
    }
}

#[test]
fn hegeltest_state_machine_paths_and_comments_are_supported() {
    let text = "#[hegeltest::/* state machine */state_machine]\nimpl Model {\n    #[rule(weight = 2.0)]\n    fn action(&mut self, tc: TestCase) {}\n    #[invariant]\n    fn safe(&self) {}\n}\n";
    let findings = findings_for("src/alternate_state_machine.rs", text);
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "hegel-rule-weight")
            .map(|finding| &text
                [finding.primary.span.start as usize..finding.primary.span.end as usize])
            .collect::<Vec<_>>(),
        ["weight"]
    );
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "hegel-sampled-invariant")
            .map(|finding| &text
                [finding.primary.span.start as usize..finding.primary.span.end as usize])
            .collect::<Vec<_>>(),
        ["invariant"]
    );
}
