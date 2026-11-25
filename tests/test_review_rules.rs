#![feature(rustc_private)]

use shapelint::{Config, Finding, Footer, SourceInput, lint};

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum BoundCase {
    Literal(u16),
    Suffixed(u16),
    Named,
    Encoding(u8),
}

#[hegel::test]
fn literal_and_symbolic_bounds_follow_the_review_policy(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<BoundCase>());
    let (bound, expected) = match case {
        BoundCase::Literal(value) => (value.to_string(), 1),
        BoundCase::Suffixed(value) => (format!("{value}usize"), 1),
        BoundCase::Named => ("Limits::MAX_PAYLOAD".to_string(), 0),
        BoundCase::Encoding(value) => (format!("0x{value:x}"), 0),
    };
    let text = format!("fn trim(data: &mut Vec<u8>) {{ data.truncate({bound}); }}");
    let findings = findings_for("src/limits.rs", &text);
    let bounds: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "arbitrary-bound")
        .collect();
    assert_eq!(bounds.len(), expected, "{text}");
    for finding in bounds {
        assert_eq!(
            &text[finding.primary.span.start as usize..finding.primary.span.end as usize],
            bound
        );
    }
}

fn findings_for(path: &str, text: &str) -> Vec<Finding> {
    let input = SourceInput::try_new(path, text).expect("fixture source fits in u32");
    lint(&input, &Config::default()).expect("fixture parses")
}

#[test]
fn literal_case_loop_reports_the_tuple_case() {
    let text = include_str!("../fixtures/feedback/tests/literal_cases.rs");
    let findings = findings_for("fixtures/feedback/tests/literal_cases.rs", text);
    let literals: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "literal-test-cases")
        .collect();
    assert_eq!(literals.len(), 5);
    let start = text.find("for (input").expect("tuple fixed case loop");
    assert!(
        literals
            .iter()
            .any(|finding| finding.primary.span.start as usize == start)
    );
    assert!(literals[0].message.contains("fixed cases"));
    assert!(literals[0].footers.iter().any(|footer| match footer {
        Footer::Help { message } => message.contains("named test"),
        _ => false,
    }));
}

#[test]
fn literal_case_loop_reports_the_named_case() {
    let text = include_str!("../fixtures/feedback/tests/literal_cases.rs");
    let findings = findings_for("fixtures/feedback/tests/literal_cases.rs", text);
    let literals: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "literal-test-cases")
        .collect();
    let start = text
        .find("for case in cases")
        .expect("named fixed case loop");
    assert!(
        literals
            .iter()
            .any(|finding| finding.primary.span.start as usize == start)
    );
}

#[test]
fn literal_case_loop_reports_the_borrowed_named_case() {
    let text = include_str!("../fixtures/feedback/tests/literal_cases.rs");
    let findings = findings_for("fixtures/feedback/tests/literal_cases.rs", text);
    let literals: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "literal-test-cases")
        .collect();
    let start = text
        .find("for case in &cases")
        .expect("borrowed fixed case loop");
    assert!(
        literals
            .iter()
            .any(|finding| finding.primary.span.start as usize == start)
    );
}

#[test]
fn literal_case_loop_reports_the_vec_case() {
    let text = include_str!("../fixtures/feedback/tests/literal_cases.rs");
    let findings = findings_for("fixtures/feedback/tests/literal_cases.rs", text);
    let literals: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "literal-test-cases")
        .collect();
    let function = text
        .find("fn vec_named_cases_are_one_test")
        .expect("vec case function");
    let start = function
        + text[function..]
            .find("for case in cases {")
            .expect("vec fixed case loop");
    assert!(
        literals
            .iter()
            .any(|finding| finding.primary.span.start as usize == start)
    );
}

#[test]
fn literal_case_loop_reports_the_state_case() {
    let text = include_str!("../fixtures/feedback/tests/literal_cases.rs");
    let findings = findings_for("fixtures/feedback/tests/literal_cases.rs", text);
    let literals: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "literal-test-cases")
        .collect();
    let start = text
        .find("for case in [\"state.step(\"")
        .expect("state fixed case loop");
    assert!(
        literals
            .iter()
            .any(|finding| finding.primary.span.start as usize == start)
    );
}

#[test]
fn literal_case_loop_skips_fixture_and_state_machine_loops() {
    let fixture = include_str!("../fixtures/feedback/tests/fixture_loop.rs");
    let fixture_findings = findings_for("fixtures/feedback/tests/fixture_loop.rs", fixture);
    assert!(
        fixture_findings
            .iter()
            .all(|finding| finding.rule != "literal-test-cases")
    );

    let text = include_str!("../fixtures/feedback/tests/literal_cases.rs");
    let findings = findings_for("fixtures/feedback/tests/literal_cases.rs", text);
    assert!(
        findings
            .iter()
            .filter(|finding| finding.rule == "literal-test-cases")
            .collect::<Vec<_>>()
            .iter()
            .all(|finding| !finding.item.contains("state_machine_history"))
    );
}

#[test]
fn primitive_draw_rule_reports_range_match() {
    let text = include_str!("../fixtures/feedback/tests/literal_cases.rs");
    let findings = findings_for("fixtures/feedback/tests/literal_cases.rs", text);
    let primitive: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "primitive-test-actions")
        .collect();
    assert_eq!(primitive.len(), 3);
    let start = text.rfind("tc.draw(0..=3)").expect("primitive draw");
    assert!(
        primitive
            .iter()
            .any(|finding| finding.primary.span.start as usize == start)
    );
    assert!(primitive[0].message.contains("primitive random choice"));
    assert!(
        findings
            .iter()
            .all(|finding| !finding.item.contains("typed_action_is_not_primitive"))
    );
}

#[test]
fn primitive_draw_rule_reports_capped_integer_match() {
    let text = include_str!("../fixtures/feedback/tests/literal_cases.rs");
    let findings = findings_for("fixtures/feedback/tests/literal_cases.rs", text);
    let primitive: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "primitive-test-actions")
        .collect();
    let start = text
        .find("tc.draw(generators::integers::<u8>().max_value(2))")
        .expect("primitive generator draw");
    assert!(
        primitive
            .iter()
            .any(|finding| finding.primary.span.start as usize == start)
    );
}

#[test]
fn primitive_draw_rule_reports_uncapped_integer_match() {
    let text = include_str!("../fixtures/feedback/tests/literal_cases.rs");
    let findings = findings_for("fixtures/feedback/tests/literal_cases.rs", text);
    let primitive: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "primitive-test-actions")
        .collect();
    let start = text
        .find("tc.draw(generators::integers::<u8>())")
        .expect("uncapped primitive draw");
    assert!(
        primitive
            .iter()
            .any(|finding| finding.primary.span.start as usize == start)
    );
}

#[test]
fn redundant_comments_report_lexical_scaffolding_only() {
    let text = include_str!("../fixtures/feedback/comments/redundant.rs");
    let findings = findings_for("fixtures/feedback/comments/redundant.rs", text);
    let redundant: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "redundant-comment")
        .collect();
    assert_eq!(redundant.len(), 4);
    assert!(
        redundant
            .iter()
            .any(|finding| finding.message.contains("TODO"))
    );
    assert!(
        redundant
            .iter()
            .any(|finding| finding.message.contains("section-divider"))
    );
    assert!(
        redundant
            .iter()
            .any(|finding| finding.message.contains("repeats"))
    );
    assert!(
        redundant
            .iter()
            .any(|finding| finding.primary.span.start as usize
                == text.find("/// documented").unwrap())
    );
    assert!(
        findings
            .iter()
            .all(|finding| !finding.item.contains("string_literals_are_not_comments"))
    );
}

#[test]
fn redundant_comment_rule_respects_suppression() {
    let text = include_str!("../fixtures/feedback/comments/suppressed.rs");
    let findings = findings_for("fixtures/feedback/comments/suppressed.rs", text);
    assert!(
        findings
            .iter()
            .all(|finding| finding.rule != "redundant-comment")
    );
}

#[test]
fn arbitrary_bound_rule_reports_named_contexts_and_skips_symbols() {
    let text = include_str!("../fixtures/feedback/bounds/arbitrary.rs");
    let findings = findings_for("fixtures/feedback/bounds/arbitrary.rs", text);
    let bounds: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "arbitrary-bound")
        .collect();
    assert_eq!(bounds.len(), 9);
    assert_bound_at(&text, &bounds, "truncate(128)", "128");
    assert_bound_at(&text, &bounds, "truncate(12usize)", "12");
    assert_bound_at(&text, &bounds, "take(16)", "16");
    assert_bound_at(&text, &bounds, "with_capacity(64)", "64");
    assert_bound_at(&text, &bounds, "retry(5)", "5");
    assert_bound_at(&text, &bounds, "generator.max(32)", "32");
    assert_bound_at(&text, &bounds, "generator.max_value(48)", "48");
    assert_bound_at(&text, &bounds, "generator.max_size(24)", "24");
    assert_bound_at(&text, &bounds, "input.len() > 256", "256");
    let ordinary = text.find("marker == 5").expect("ordinary comparison");
    assert!(
        bounds
            .iter()
            .all(|finding| (finding.primary.span.start as usize) < ordinary)
    );
    let arithmetic_length = text.find("input.len() + 3").expect("arithmetic length");
    assert!(
        bounds
            .iter()
            .all(|finding| finding.primary.span.start as usize != arithmetic_length + 14)
    );
    let ordinary_max = text.find("std::cmp::max(5").expect("ordinary max");
    assert!(
        bounds
            .iter()
            .all(|finding| finding.primary.span.start as usize != ordinary_max + 14)
    );
    assert!(text.contains("MAX_INPUT") && text.contains("0x40"));
    assert!(bounds.iter().all(|finding| {
        finding.footers.iter().any(|footer| match footer {
            Footer::Help { message } => message.contains("domain bound"),
            _ => false,
        })
    }));
}

#[test]
fn nested_numeric_bounds_report_only_the_literal_subtree() {
    let text = "fn nested(generator: &Generator) { generator.max(generator.max(17)); }";
    let findings = findings_for("fixtures/feedback/bounds/nested.rs", text);
    let bounds: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "arbitrary-bound")
        .collect();
    assert_eq!(bounds.len(), 1);
    let span = bounds[0].primary.span;
    assert_eq!(&text[span.start as usize..span.end as usize], "17");
}

#[test]
fn nested_bindings_use_the_inner_initializer() {
    let text = r#"
fn run() {
    let values = {
        let values = [1, 2, 3];
        for value in values.iter().filter(|_| true) {
            let _ = value;
        }
        values
    };
    let _ = values;
}
"#;
    let findings = findings_for("src/nested_bindings.rs", text);
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "for-chain")
            .count(),
        1,
        "{findings:?}"
    );
}

fn assert_bound_at(text: &str, bounds: &[&Finding], call: &str, literal: &str) {
    let start = text.find(call).expect("bound call") + call.find(literal).expect("bound literal");
    assert!(
        bounds
            .iter()
            .any(|finding| finding.primary.span.start as usize == start)
    );
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum BoundOwner {
    Function,
    Closure,
    Constant,
}

#[hegel::test]
fn numeric_bounds_are_checked_in_each_expression_owner(tc: hegel::TestCase) {
    let owner = tc.draw(hegel::generators::default::<BoundOwner>());
    let source = match owner {
        BoundOwner::Function => "fn limit() { values.truncate(23); }",
        BoundOwner::Closure => "fn limit() { let run = || values.truncate(23); }",
        BoundOwner::Constant => "const LIMIT: () = { values.truncate(23); };",
    };
    let findings = findings_for("src/bounds.rs", source);
    let bounds: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "arbitrary-bound")
        .collect();
    assert_eq!(bounds.len(), 1, "{owner:?}");
    let span = bounds[0].primary.span;
    assert_eq!(&source[span.start as usize..span.end as usize], "23");
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum TestContext {
    CompoundCfg,
    QualifiedAttribute,
    TestSuffix,
    WindowsPath,
    Production,
}

#[hegel::test]
fn fixed_case_rules_share_test_context_classification(tc: hegel::TestCase) {
    let context = tc.draw(hegel::generators::default::<TestContext>());
    let (path, attribute, expected) = match context {
        TestContext::CompoundCfg => ("src/check.rs", "#[cfg(all(test, unix))]", 1),
        TestContext::QualifiedAttribute => ("src/check.rs", "#[framework::test]", 1),
        TestContext::TestSuffix => ("src/check_test.rs", "", 1),
        TestContext::WindowsPath => (r"project\tests\check.rs", "", 1),
        TestContext::Production => ("src/check.rs", "", 0),
    };
    let source =
        format!("{attribute}\nfn check() {{ for value in [1, 2] {{ assert!(value > 0); }} }}");
    let findings = findings_for(path, &source);
    let cases: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "literal-test-cases")
        .collect();
    assert_eq!(cases.len(), expected, "{context:?}");
}
