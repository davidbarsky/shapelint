#![feature(rustc_private)]

use std::fmt::Write;
use std::process::Command;

use serde::Deserialize;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum RecursiveEdge {
    Returning,
    Diverging,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Calls {
    wrappers: Vec<()>,
    edge: RecursiveEdge,
}

#[derive(Debug, Deserialize)]
struct Finding {
    rule: String,
    item: String,
}

#[hegel::test(print_blob = true)]
fn recursive_results_survive_dependency_expiry_and_repeated_callers(tc: hegel::TestCase) {
    let Calls { wrappers, edge } = tc.draw(hegel::generators::default::<Calls>());
    let recursive = match edge {
        RecursiveEdge::Returning => "bridge(true)",
        RecursiveEdge::Diverging => "bridge(false)",
    };
    let mut source = format!(
        "fn leaf(flag: bool) -> u8 {{ if flag {{ 1 }} else {{ {recursive} }} }}\nfn bridge(flag: bool) -> u8 {{ leaf(flag) }}\n"
    );
    let mut callee = String::from("leaf");
    for index in 0..wrappers.len() {
        writeln!(
            source,
            "fn node_{index}(flag: bool) -> u8 {{ {callee}(flag) }}"
        )
        .unwrap();
        callee = format!("node_{index}");
    }
    writeln!(source, "pub fn first() -> u8 {{ {callee}(false) - 2 }}").unwrap();
    writeln!(source, "pub fn second() -> u8 {{ {callee}(false) - 2 }}").unwrap();
    writeln!(
        source,
        "pub fn established() -> u8 {{ {callee}(true) - 1 }}"
    )
    .unwrap();
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("dependencies.rs");
    std::fs::write(&path, &source).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--show-analysis-gaps",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
        ])
        .arg("--out-dir")
        .arg(directory.path())
        .arg(path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{source}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{source}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut invalid = Vec::new();
    let text = String::from_utf8(output.stdout).unwrap();
    for line in text.lines() {
        let finding: Finding = serde_json::from_str(line).unwrap();
        match (finding.item.as_str(), finding.rule.as_str()) {
            ("first" | "second", "invalid-state-use") => invalid.push(finding.item),
            (
                "first" | "second" | "established",
                "unproven-precondition" | "analysis-incomplete",
            )
            | ("established", "invalid-state-use") => panic!("{finding:?}\n{source}"),
            _ => {}
        }
    }
    invalid.sort();
    match edge {
        RecursiveEdge::Returning => assert_eq!(invalid, ["first", "second"], "{source}"),
        RecursiveEdge::Diverging => assert_eq!(invalid, Vec::<String>::new(), "{source}"),
    }
}
