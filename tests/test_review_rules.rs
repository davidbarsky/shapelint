#![feature(rustc_private)]

use shapelint::{Config, Finding, SourceInput, lint};

fn findings_for(path: &str, text: &str) -> Vec<Finding> {
    let input = SourceInput::try_new(path, text).expect("fixture source fits in u32");
    lint(&input, &Config::default()).expect("fixture parses")
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
