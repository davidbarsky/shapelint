#![feature(rustc_private)]

mod support;

use std::fmt::Write;

#[derive(Debug, hegel::DefaultGenerator)]
struct Forwarders {
    functions: Vec<()>,
}

#[hegel::test(print_blob = true)]
fn nested_substitutions_keep_requirement_guards_and_origins(tc: hegel::TestCase) {
    let Forwarders { functions } = tc.draw(hegel::generators::default::<Forwarders>());
    let mut source = String::from("fn leaf(values: &[u8], index: usize) -> u8 { values[index] }\n");
    let mut callee = String::from("leaf");
    let functions = functions.into_iter().enumerate();
    for (index, ()) in functions {
        let name = format!("forward_{index}");
        writeln!(
            source,
            "fn {name}(items: &[u8], at: usize) -> u8 {{ {callee}(items, at) }}"
        )
        .expect("write forwarding function");
        callee = name;
    }
    writeln!(
        source,
        "pub fn guarded(data: &[u8], offset: usize) -> u8 {{ if offset < data.len() {{ {callee}(data, offset) }} else {{ 0 }} }}"
    )
    .expect("write guarded caller");
    writeln!(
        source,
        "pub fn split(data: &[u8], offset: usize) -> u8 {{ if offset < data.len() {{ {callee}(data, offset) }} else {{ {callee}(data, offset) }} }}"
    )
    .expect("write caller with separate guard paths");
    writeln!(
        source,
        "pub fn unguarded(data: &[u8], offset: usize) -> u8 {{ {callee}(data, offset) }}"
    )
    .expect("write unguarded caller");

    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "unproven-precondition")
        .collect();
    let mut items: Vec<_> = findings
        .iter()
        .map(|finding| finding["item"].as_str().expect("item"))
        .collect();
    items.sort_unstable();
    assert_eq!(items, ["split", "unguarded"], "{source}\n{output}");

    for finding in &findings {
        assert!(
            finding["primary"]["message"]
                .as_str()
                .expect("requirement")
                .contains("offset < data.len()"),
            "substitution did not reach the caller diagnostic: {finding}"
        );
        assert_eq!(
            finding["related"][0]["label"]["message"], "check originates in `leaf`",
            "{finding}"
        );
        let start = finding["related"][0]["label"]["span"]["start"]
            .as_u64()
            .expect("origin start") as usize;
        let end = finding["related"][0]["label"]["span"]["end"]
            .as_u64()
            .expect("origin end") as usize;
        assert!(source[start..end].contains("values[index]"), "{finding}");
    }
}

#[test]
fn macro_origin_requirement_fanin_does_not_hide_source_written_obligations() {
    let source = r#"
macro_rules! generated {
    ($name:ident) => {
        fn $name(values: &[u8], index: usize) -> u8 { values[index] }
    };
}
generated!(first_generated);
generated!(second_generated);

fn source_written_leaf(values: &[u8], index: usize) -> u8 { values[index] }

pub fn macro_fanin(values: &[u8], index: usize, choose: bool) -> u8 {
    if choose { first_generated(values, index) } else { second_generated(values, index) }
}

pub fn source_written_control(values: &[u8], index: usize) -> u8 {
    source_written_leaf(values, index)
}
"#;
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "unproven-precondition")
        .collect();
    assert_eq!(findings.len(), 1, "{output}");
    assert_eq!(findings[0]["item"], "source_written_control", "{output}");
    assert_eq!(
        findings[0]["related"][0]["label"]["message"], "check originates in `source_written_leaf`",
        "{output}"
    );
}
