#![feature(rustc_private)]

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Boundary {
    Expression,
    Nested,
    Function,
    DerivedClosure,
    Assertion,
    Argument,
    Mutation,
    ReturnValue,
    Representation,
    Loops,
}

#[hegel::test]
fn macro_expansions_are_analyzed_without_reporting_generated_checks(tc: hegel::TestCase) {
    let boundary = tc.draw(hegel::generators::default::<Boundary>());
    let (source, expected) = match boundary {
        Boundary::Expression => (
            "macro_rules! invalid { () => { &\"é\"[0..1] }; } pub fn run() -> &'static str { invalid!() }",
            0,
        ),
        Boundary::Nested => (
            "macro_rules! invalid { () => { &\"é\"[0..1] }; } macro_rules! outer { () => { invalid!() }; } pub fn run() -> &'static str { outer!() }",
            0,
        ),
        Boundary::Function => (
            "macro_rules! generate { () => { pub fn generated() -> &'static str { &\"é\"[0..1] } }; } generate!(); pub fn run() -> &'static str { generated() }",
            0,
        ),
        Boundary::DerivedClosure => (
            "pub trait Read { fn read() -> &'static str; } pub struct Input; #[automatically_derived] impl Read for Input { fn read() -> &'static str { let read = || &\"é\"[0..1]; read() } } pub fn run() -> &'static str { Input::read() }",
            0,
        ),
        Boundary::Assertion => ("pub fn run(ready: bool) { assert!(ready); }", 0),
        Boundary::Loops => (
            "macro_rules! repeat { ($n:expr, $effect:expr) => { for value in 0..$n { $effect(value); } }; } pub fn first(n: u32, effect: fn(u32)) { repeat!(n, effect); } pub fn second(n: u32, effect: fn(u32)) { repeat!(n, effect); }",
            0,
        ),
        Boundary::Argument => (
            "macro_rules! pass { ($value:expr) => { $value }; } pub fn run() -> &'static str { pass!(&\"é\"[0..1]) }",
            1,
        ),
        Boundary::Mutation => (
            "macro_rules! clear { ($value:expr) => { $value = None }; } pub fn run() -> u32 { let mut value = Some(3); let _ = value; clear!(value); value.unwrap() }",
            1,
        ),
        Boundary::ReturnValue => (
            "macro_rules! generate { () => { fn generated() -> Option<u32> { None } }; } generate!(); pub fn run() -> u32 { generated().unwrap() }",
            1,
        ),
        Boundary::Representation => (
            "pub struct Span { pub start: usize, pub end: usize } macro_rules! generate { () => { pub fn read(span: Span) -> usize { span.end - span.start } }; } generate!(); pub fn run(span: Span) -> usize { read(span) }",
            0,
        ),
    };
    let directory = tempfile::tempdir().expect("source directory");
    let path = directory.path().join("input.rs");
    std::fs::write(&path, source).expect("write source");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--show-analysis-gaps",
            "--deny-invalid-states",
            "--crate-type=lib",
        ])
        .arg(&path)
        .output()
        .expect("driver analysis");
    assert!(output.stderr.is_empty(), "{output:?}");
    match boundary {
        Boundary::Argument | Boundary::Mutation | Boundary::ReturnValue => {
            assert_eq!(output.status.code(), Some(1), "{output:?}")
        }
        Boundary::Expression
        | Boundary::Nested
        | Boundary::Function
        | Boundary::DerivedClosure
        | Boundary::Assertion
        | Boundary::Representation
        | Boundary::Loops => assert!(output.status.success(), "{output:?}"),
    }
    let stdout = String::from_utf8(output.stdout).expect("UTF-8");
    let findings: Vec<serde_json::Value> = stdout
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(
            |finding: &serde_json::Value| match finding["rule"].as_str() {
                Some(
                    "invalid-state-use"
                    | "invalid-variant-access"
                    | "unproven-precondition"
                    | "analysis-incomplete"
                    | "unencoded-precondition"
                    | "duplicate-control-flow",
                ) => true,
                _ => false,
            },
        )
        .collect();
    assert_eq!(findings.len(), expected, "{boundary:?}: {stdout}");
}

#[test]
fn procedural_derive_with_call_site_spans_does_not_report_generated_checks() {
    let directory = tempfile::tempdir().expect("source directory");
    let macros = directory.path().join("generated.rs");
    std::fs::write(&macros, r##"
        extern crate proc_macro;
        #[proc_macro_derive(Generated)]
        pub fn generated(_: proc_macro::TokenStream) -> proc_macro::TokenStream {
            "#[automatically_derived] impl Read for Input { fn read() -> &'static str { let read = || &\"é\"[0..1]; read() } }".parse().unwrap()
        }
    "##).expect("macro fixture");
    let compiler = match std::env::var_os("RUSTC") {
        Some(compiler) => compiler,
        None => "rustc".into(),
    };
    let built = std::process::Command::new(compiler)
        .args(["--crate-type=proc-macro", "--out-dir"])
        .arg(directory.path())
        .arg(&macros)
        .output()
        .expect("compile procedural macro");
    assert!(built.status.success(), "{built:?}");
    assert!(built.stderr.is_empty(), "{built:?}");
    let source = directory.path().join("input.rs");
    std::fs::write(&source, "extern crate generated; pub trait Read { fn read() -> &'static str; } #[derive(generated::Generated)] pub struct Input; pub fn run() -> &'static str { Input::read() }").expect("source fixture");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--show-analysis-gaps",
            "--deny-invalid-states",
            "--crate-type=lib",
            "--extern",
            "generated",
            "-L",
        ])
        .arg(directory.path())
        .arg(&source)
        .output()
        .expect("driver analysis");
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).expect("UTF-8");
    let findings: Vec<serde_json::Value> = stdout
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    assert_eq!(findings.len(), 1, "{stdout}");
    assert_eq!(findings[0]["rule"], "shallow-helper");
    assert_eq!(findings[0]["item"], "fn run");
}
