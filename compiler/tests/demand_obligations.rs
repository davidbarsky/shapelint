#![feature(rustc_private)]

mod support;

use std::fmt::Write;

#[derive(Debug, hegel::DefaultGenerator)]
struct Chain {
    wrappers: Vec<()>,
}

#[derive(Debug, serde::Deserialize)]
struct Finding {
    rule: String,
    item: String,
    line: usize,
}

#[hegel::test(print_blob = true)]
fn invalid_preconditions_follow_private_call_chains(tc: hegel::TestCase) {
    let Chain { wrappers } = tc.draw(hegel::generators::default::<Chain>());
    let mut source = String::from(
        "fn read(source: &str, start: usize, end: usize) -> &str { &source[start..end] }\n",
    );
    let line = wrappers.len() + 2;
    let mut callee = String::from("read");
    let wrappers = wrappers.into_iter().enumerate();
    for (index, ()) in wrappers {
        let name = format!("wrapper_{index}");
        writeln!(source, "fn {name}(source: &str, start: usize, end: usize) -> &str {{ {callee}(source, start, end) }}").unwrap();
        callee = name;
    }
    writeln!(
        source,
        "pub fn run() -> &'static str {{ {callee}(\"abcd\", 3, 1) }}"
    )
    .unwrap();
    let output = support::analyze(&source, &[]).unwrap();
    let findings: Vec<Finding> = output
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    let invalid: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "invalid-state-use")
        .map(|finding| (finding.item.as_str(), finding.line))
        .collect();
    assert_eq!(invalid, [("run", line)], "{source}\n{findings:?}");
}
