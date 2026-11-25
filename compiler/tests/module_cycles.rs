#![feature(rustc_private)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use serde::Deserialize;

const FIXTURE: &str = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../fixtures/module_cycle/lib.rs"
);

#[derive(Debug, Deserialize)]
struct Finding {
    rule: String,
    kind: String,
    path: PathBuf,
    message: String,
    primary: Label,
    labels: Vec<Label>,
    footers: Vec<Footer>,
    #[serde(default)]
    related: Vec<Related>,
}

#[derive(Debug, Deserialize)]
struct Footer {
    kind: String,
    message: String,
}

#[derive(Debug, Deserialize)]
struct Label {
    message: String,
    span: std::ops::Range<usize>,
}

#[derive(Debug, Deserialize)]
struct Related {
    input: File,
    label: Label,
}

#[derive(Debug, Deserialize)]
struct File {
    name: PathBuf,
}

fn cycles(source: impl AsRef<Path>, options: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "module-cycles",
            "--crate-name=wiring",
            "--crate-type=lib",
            "--edition=2024",
            "--format=json",
        ])
        .args(options)
        .arg(source.as_ref())
        .output()
        .expect("run the cycle-only driver")
}

fn findings(output: Output, status: i32) -> Vec<Finding> {
    assert_eq!(
        output.status.code(),
        Some(status),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect()
}

fn baseline(source: impl AsRef<Path>, options: &[&str]) -> Vec<Vec<String>> {
    let mut arguments = vec!["--emit-baseline"];
    arguments.extend_from_slice(options);
    let output = cycles(source, &arguments);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    serde_json::from_slice(&output.stdout).unwrap()
}

#[test]
fn signatures_and_reexports_report_closed_witnesses_in_the_original_files() {
    let groups = baseline(FIXTURE, &[]);
    assert_eq!(
        groups,
        [
            ["wiring::queue", "wiring::wire"],
            [
                "wiring::queue::buffers::reader",
                "wiring::queue::buffers::writer"
            ]
        ]
    );
    let reports = findings(cycles(FIXTURE, &[]), 1);
    let [outer, inner] = reports.as_slice() else {
        panic!("expected two findings: {reports:?}")
    };
    assert_eq!(outer.rule, "module-cycle");
    assert_eq!(outer.kind, "lint");
    assert!(
        outer
            .footers
            .iter()
            .any(|footer| { footer.kind == "help" && footer.message.contains("baseline") })
    );
    assert_eq!(outer.primary.message, "wiring::queue uses wiring::wire");
    let original = fs::read_to_string(&outer.path).unwrap();
    assert_eq!(&original[outer.primary.span.clone()], "Packet");
    let closing = &outer.related[0];
    assert!(closing.input.name.ends_with("wire_format.rs"));
    assert_eq!(closing.label.message, "wiring::wire uses wiring::queue");
    assert_eq!(
        inner.labels[0].message,
        "wiring::queue::buffers::writer uses wiring::queue::buffers::reader"
    );
}

#[test]
fn baseline_accepts_shrinking_or_split_groups_and_flags_new_growth_and_mergers() {
    let directory = tempfile::tempdir().unwrap();
    let path = directory.path().join("groups.json");
    let accepted = ["--baseline", path.to_str().unwrap()];
    let production = baseline(FIXTURE, &[]);
    let with_tests = baseline(FIXTURE, &["--cfg=test"]);
    assert_eq!(
        with_tests[0],
        ["wiring::queue", "wiring::trace", "wiring::wire"]
    );
    fs::write(&path, serde_json::to_vec(&production).unwrap()).unwrap();
    assert!(findings(cycles(FIXTURE, &accepted), 0).is_empty());
    let grown = findings(
        cycles(FIXTURE, &[accepted[0], accepted[1], "--cfg=test"]),
        1,
    );
    assert_eq!(grown.len(), 1);
    assert!(grown[0].message.contains("wiring::trace"));

    fs::write(&path, serde_json::to_vec(&with_tests).unwrap()).unwrap();
    assert!(findings(cycles(FIXTURE, &accepted), 0).is_empty());
    let combined = production.concat();
    fs::write(&path, serde_json::to_vec(&[combined]).unwrap()).unwrap();
    assert!(findings(cycles(FIXTURE, &accepted), 0).is_empty());

    let separate = [
        vec!["wiring::queue".into(), "wiring::trace".into()],
        vec!["wiring::wire".into(), "wiring::other".into()],
        production[1].clone(),
    ];
    fs::write(&path, serde_json::to_vec(&separate).unwrap()).unwrap();
    let merged = findings(cycles(FIXTURE, &accepted), 1);
    assert_eq!(merged.len(), 1);
    assert_eq!(merged[0].primary.message, "wiring::queue uses wiring::wire");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Reference {
    Method,
    AssociatedFunction,
    Field,
    Closure,
    ChildModule,
    MacroArgument,
    MacroExpansion,
    UnusedImport,
}

#[hegel::test]
fn cycles_follow_the_definition_used_at_the_reference(tc: hegel::TestCase) {
    let reference = tc.draw(hegel::generators::default::<Reference>());
    let cycle = &[["wiring::a", "wiring::b"]][..];
    let (body, groups) = match reference {
        Reference::Method => ("pub fn read() { crate::Token.touch(); }", cycle),
        Reference::AssociatedFunction => (
            "pub fn read() { crate::Token::touch(&crate::Token); }",
            cycle,
        ),
        Reference::Field => ("pub fn read() -> i32 { crate::offer().value }", cycle),
        Reference::Closure => (
            "pub fn read() { let f = || crate::Token.touch(); f(); }",
            cycle,
        ),
        Reference::ChildModule => (
            "pub mod nested { pub fn read() { crate::b::use_a(); } }",
            cycle,
        ),
        Reference::MacroArgument => (
            "macro_rules! pass { ($e:expr) => { $e } } pub fn read() { pass!(crate::b::use_a()); }",
            cycle,
        ),
        Reference::MacroExpansion => (
            "macro_rules! call_b { () => { crate::b::use_a() } } pub fn read() { call_b!(); }",
            &[][..],
        ),
        Reference::UnusedImport => ("use crate::b::Data;", &[][..]),
    };
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("lib.rs");
    fs::write(
        &source,
        format!(
            r#"
        #![allow(unused)]
        pub struct Token;
        pub fn offer() -> b::Data {{ b::Data {{ value: 0 }} }}
        mod a {{ pub fn finish() {{}} {body} }}
        mod b {{
            pub struct Data {{ pub value: i32 }}
            impl crate::Token {{ pub fn touch(&self) {{}} }}
            pub fn use_a() {{ crate::a::finish(); }}
        }}
    "#
        ),
    )
    .unwrap();
    assert_eq!(baseline(&source, &[]), groups);
}

#[test]
fn cycle_only_stops_before_borrow_check_and_reports_resolution_errors() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("lib.rs");
    fs::write(&source, "pub fn moved(x: String) { drop(x); drop(x); }").unwrap();
    let output_dir = directory.path().to_str().unwrap();
    assert!(baseline(&source, &["--emit=metadata", "--out-dir", output_dir]).is_empty());
    assert_eq!(fs::read_dir(directory.path()).unwrap().count(), 1);
    let full = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--crate-type=lib",
            "--edition=2024",
            "--out-dir",
            output_dir,
        ])
        .arg(&source)
        .output()
        .unwrap();
    assert!(!full.status.success());
    assert!(String::from_utf8_lossy(&full.stderr).contains("use of moved value"));
    fs::write(&source, "pub fn missing() { absent::call(); }").unwrap();
    let invalid = cycles(&source, &["--emit-baseline"]);
    assert!(!invalid.status.success());
    assert!(invalid.stdout.is_empty());
    assert!(String::from_utf8_lossy(&invalid.stderr).contains("absent"));
}

#[test]
fn a_suppression_on_the_primary_item_covers_the_diagnostic() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("lib.rs");
    fs::write(
        &source,
        r#"
        pub mod a {
            // shapelint: allow(module-cycle)
            pub fn uses_b() { crate::b::uses_a(); }
        }
        pub mod b { pub fn uses_a() { crate::a::uses_b(); } }
    "#,
    )
    .unwrap();
    assert_eq!(baseline(&source, &[]), [["wiring::a", "wiring::b"]]);
    assert!(findings(cycles(&source, &[]), 0).is_empty());
}

#[test]
fn array_lengths_use_their_own_type_checking_body_in_a_three_module_cycle() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("lib.rs");
    fs::write(
        &source,
        r#"
        #![allow(dead_code)]
        struct Token;
        mod a { pub struct Stack([u8; crate::Token.size()]); }
        mod b { impl crate::Token { pub const fn size(self) -> usize { crate::c::SIZE } } }
        mod c { pub const SIZE: usize = 0; pub fn read(_: crate::a::Stack) {} }
    "#,
    )
    .unwrap();
    let reports = findings(cycles(&source, &[]), 1);
    let [cycle] = reports.as_slice() else {
        panic!("expected one cycle: {reports:?}")
    };
    assert_eq!(cycle.primary.message, "wiring::a uses wiring::b");
    let edges: Vec<_> = cycle
        .labels
        .iter()
        .map(|label| label.message.as_str())
        .collect();
    assert_eq!(
        edges,
        ["wiring::b uses wiring::c", "wiring::c uses wiring::a"]
    );
}
