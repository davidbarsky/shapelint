#![feature(rustc_private)]

use std::fmt::Write;

use hegel::generators;

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Flag {
    Clear,
    Set,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Step {
    Preserve,
    Negate,
}

#[hegel::test(print_blob = true)]
fn sequential_negations_match_the_independent_parity_model(tc: hegel::TestCase) {
    let (initial, steps) = tc.draw(generators::default::<(Flag, Vec<Step>)>());
    let expected = steps.iter().fold(initial, |flag, step| match (flag, step) {
        (flag, Step::Preserve) => flag,
        (Flag::Clear, Step::Negate) => Flag::Set,
        (Flag::Set, Step::Negate) => Flag::Clear,
    });
    let mut source = String::from("fn value(input:bool)->u8{let state_0=input;");
    let sequence = steps.iter().enumerate();
    for (index, step) in sequence {
        let operator = match step {
            Step::Preserve => "",
            Step::Negate => "!",
        };
        write!(source, "let state_{}={operator}state_{index};", index + 1).expect("source text");
    }
    let input = match initial {
        Flag::Clear => "false",
        Flag::Set => "true",
    };
    write!(
        source,
        "if state_{}{{1}}else{{0}}}}pub fn probe()->u8{{value({input})-1}}",
        steps.len()
    )
    .expect("source text");
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let invalid = findings
        .iter()
        .filter(|finding| finding["item"] == "probe" && finding["rule"] == "invalid-state-use")
        .count();
    assert_eq!(
        invalid,
        match expected {
            Flag::Clear => 1,
            Flag::Set => 0,
        },
        "{source}\n{output}"
    );
    assert!(
        !findings.iter().any(|finding| finding["item"] == "probe"
            && (finding["rule"] == "unproven-precondition"
                || finding["rule"] == "analysis-incomplete")),
        "{source}\n{output}"
    );
}
