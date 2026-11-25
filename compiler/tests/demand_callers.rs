#![feature(rustc_private)]

use std::fmt::Write;
use std::path::Path;
use std::process::Command;

use serde::Deserialize;

#[derive(Debug, PartialEq, Eq, Deserialize)]
struct Span {
    start: usize,
    end: usize,
}

#[derive(Debug, PartialEq, Eq, Deserialize)]
struct Label {
    span: Span,
    message: String,
}

#[derive(Debug, PartialEq, Eq, Deserialize)]
struct SourceInput {
    name: String,
}

#[derive(Debug, PartialEq, Eq, Deserialize)]
struct Related {
    input: SourceInput,
    label: Label,
}

#[derive(Debug, PartialEq, Eq, Deserialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
enum Footer {
    Note {
        message: String,
    },
    Help {
        message: String,
    },
    Suggestion {
        message: String,
        span: Span,
        replacement: String,
    },
}

#[derive(Debug, PartialEq, Eq, Deserialize)]
struct Finding {
    rule: String,
    kind: String,
    path: String,
    line: usize,
    col: usize,
    item: String,
    item_span: Span,
    message: String,
    primary: Label,
    labels: Vec<Label>,
    #[serde(default)]
    related: Vec<Related>,
    footers: Vec<Footer>,
    fingerprint: String,
}

struct RustSource<'a>(&'a str);

fn analyze(directory: &Path, RustSource(source): RustSource<'_>) -> Vec<Finding> {
    let path = directory.join("callbacks.rs");
    std::fs::write(&path, source).expect("write source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--edition=2024",
            "--emit=metadata",
            "--crate-type=lib",
        ])
        .arg("--out-dir")
        .arg(directory)
        .arg(path)
        .output()
        .expect("analysis");
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
    let output = String::from_utf8(output.stdout).expect("UTF-8 diagnostics");
    output
        .lines()
        .map(|line| serde_json::from_str::<Finding>(line).expect("finding"))
        .filter(|finding| finding.rule == "unused-capability" && finding.item == "render")
        .collect()
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Callback {
    Known,
    Escaped,
}

#[hegel::test(print_blob = true)]
fn caller_demand_follows_callbacks_and_escape_paths(tc: hegel::TestCase) {
    let callback = tc.draw(hegel::generators::default::<Callback>());
    let extra = match callback {
        Callback::Known => "",
        Callback::Escaped => {
            "unsafe extern \"Rust\" { fn register(f: fn(bool) -> u32); } pub fn export() { unsafe { register(render) } }"
        }
    };
    let source = format!(
        "fn render(flag: bool) -> u32 {{ if flag {{ 1 }} else {{ 2 }} }} \
         fn invoke(f: fn(bool) -> u32) -> u32 {{ f(false) }} \
         pub fn run() -> u32 {{ invoke(render) }} {extra}"
    );
    let directory = tempfile::tempdir().expect("source directory");
    let actual = analyze(directory.path(), RustSource(&source));
    match callback {
        Callback::Known => {
            let [finding] = actual.as_slice() else {
                panic!("{callback:?}: {actual:?}")
            };
            assert_eq!(finding.item, "render");
            assert_eq!(
                finding.primary.span,
                Span {
                    start: 0,
                    end: source.find(" { ").expect("end of render signature")
                }
            );
            assert_eq!(finding.primary.message, "`flag` is always false");
            assert!(!finding.related.is_empty(), "{finding:?}");
        }
        Callback::Escaped => assert_eq!(actual, [], "{callback:?}"),
    }
}

#[test]
fn a_recursive_sibling_retains_the_unknown_callback_witness() {
    let source = "fn render(flag: bool) -> u32 { if flag { 1 } else { 2 } }
        fn invoke(f: fn(bool) -> u32) -> u32 { f(false) }
        fn cycle(f: fn(bool) -> u32, steps: usize) {
            if steps > 1 { back(f, steps / 2); }
        }
        fn back(f: fn(bool) -> u32, steps: usize) { cycle(f, steps); }
        pub fn run(steps: usize) -> u32 { cycle(render, steps); invoke(render) }";
    let directory = tempfile::tempdir().expect("source directory");
    let findings = analyze(directory.path(), RustSource(source));
    assert!(findings.is_empty(), "{findings:?}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum CallGraph {
    PureArguments,
    NestedGuard,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct UnrelatedCalls {
    nodes: Vec<()>,
    graph: CallGraph,
}

#[hegel::test(print_blob = true)]
fn unrelated_call_graph_does_not_change_candidate_diagnostics(tc: hegel::TestCase) {
    let UnrelatedCalls { nodes, graph } = tc.draw(hegel::generators::default::<UnrelatedCalls>());
    let source = "fn render(flag: bool) -> u32 { if flag { 1 } else { 2 } } \
        fn invoke(f: fn(bool) -> u32) -> u32 { f(false) } \
        pub fn run() -> u32 { invoke(render) }";
    let directory = tempfile::tempdir().expect("source directory");
    let expected = analyze(directory.path(), RustSource(source));
    assert_eq!(expected.len(), 1, "{expected:?}");
    let mut extended = source.to_owned();
    match graph {
        CallGraph::PureArguments => {}
        CallGraph::NestedGuard => {
            extended.push_str(" pub fn unrelated_guard(x: u32) -> bool { x > 0 }")
        }
    }
    for index in 0..nodes.len() {
        let value = match index {
            0 => String::from("x"),
            _ => format!("unrelated_{}(x)", index - 1),
        };
        match graph {
            CallGraph::PureArguments => writeln!(extended, " pub fn unrelated_{index}(x: u32) -> u32 {{ {value} }}").expect("source"),
            CallGraph::NestedGuard => writeln!(extended, " pub fn unrelated_{index}(x: u32) -> u32 {{ if unrelated_guard(x) {{ {value} }} else {{ x }} }}").expect("source"),
        }
    }
    let actual = analyze(directory.path(), RustSource(&extended));
    assert_eq!(actual, expected, "{extended}");
}
