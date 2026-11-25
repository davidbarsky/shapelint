#![feature(rustc_private)]

mod support;

use std::error::Error;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Access {
    Reversed,
    OutOfBounds,
    Utf8,
    Valid,
    Guarded,
    BoundaryGuarded,
    Helper,
    Constructor,
    Assert,
    Unknown,
    Mutated,
    Snapshot,
    WrongSource,
    CustomIndex,
    ArrayIndex,
    Transitive,
    Narrowing,
    ReturnedProof,
    BooleanHelper,
    ThroughExtract,
    VecGuarded,
    StringGuarded,
    OpenRange,
    Suppressed,
    ConditionalConstant,
    Recursive,
}

#[hegel::test]
fn consumer_contracts_follow_values_through_calls(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let access = tc.draw(hegel::generators::default::<Access>());
        let (source, invalid, unknown) = match access {
            Access::ReturnedProof => (
                "fn checked(a: usize, b: usize) -> std::ops::Range<usize> { assert!(a <= b); a..b } pub fn run(source: &[u8], a: usize, b: usize) -> &[u8] { let range = checked(a, b); if b <= source.len() { &source[range] } else { &[] } }",
                0,
                0,
            ),
            Access::BooleanHelper => (
                "fn ordered(a: usize, b: usize) -> bool { a <= b } pub fn run(source: &[u8], a: usize, b: usize) -> &[u8] { if ordered(a, b) && b <= source.len() { &source[a..b] } else { &[] } }",
                0,
                0,
            ),
            Access::ThroughExtract => (
                "fn extract(value: Option<u8>) -> u8 { value.unwrap() } pub fn run() -> u8 { extract(None) }",
                1,
                0,
            ),
            Access::VecGuarded => (
                "pub fn run(source: &Vec<u8>, index: usize) -> u8 { if index < source.len() { source[index] } else { 0 } }",
                0,
                0,
            ),
            Access::StringGuarded => (
                r#"pub fn run(source: &String, end: usize) -> &str { if end <= source.len() && source.is_char_boundary(end) { &source[..end] } else { "" } }"#,
                0,
                0,
            ),
            Access::OpenRange => (r#"pub fn run() -> &'static str { &"é"[1..] }"#, 1, 0),
            Access::Suppressed => (
                "// shapelint: allow(invalid-state-use)\n pub fn run() -> &'static str { &\"é\"[0..1] }",
                0,
                0,
            ),
            Access::ConditionalConstant => (
                "pub fn run(flag: bool) -> &'static str { if flag { &\"é\"[0..1] } else { \"\" } }",
                0,
                1,
            ),
            Access::Recursive => (
                "pub fn run(source: &[u8], index: usize) -> u8 { if source.is_empty() { run(source, index) } else { source[index] } }",
                0,
                1,
            ),
            Access::ArrayIndex => (
                "fn at(i: usize) -> u8 { [1, 2, 3][i] } pub fn run() -> u8 { at(3) }",
                1,
                0,
            ),
            Access::Transitive => (
                "pub fn run(source: &[u8], start: usize, middle: usize, end: usize) -> &[u8] { if start <= middle && middle <= end && end <= source.len() { &source[start..end] } else { &[] } }",
                0,
                0,
            ),
            Access::Narrowing => (
                r#"pub fn run(value: u64) -> &'static str { let end = value as u8 as usize; &"abcd"[0..end] }"#,
                0,
                2,
            ),
            Access::Reversed => (
                "pub fn run() -> &'static str { let start = 3; let end = 1; &\"abcd\"[start..end] }",
                1,
                0,
            ),
            Access::OutOfBounds => ("pub fn run() -> &'static str { &\"abcd\"[0..5] }", 2, 0),
            Access::Utf8 => ("pub fn run() -> &'static str { &\"é\"[0..1] }", 1, 0),
            Access::Valid => ("pub fn run() -> &'static str { &\"é\"[0..2] }", 0, 0),
            Access::Guarded => (
                "pub fn run(source: &[u8], start: usize, end: usize) -> &[u8] { if start <= end && end <= source.len() { &source[start..end] } else { &[] } }",
                0,
                0,
            ),
            Access::BoundaryGuarded => (
                "pub fn run(source: &str, start: usize, end: usize) -> &str { if start <= end && end <= source.len() && source.is_char_boundary(start) && source.is_char_boundary(end) { &source[start..end] } else { \"\" } }",
                0,
                0,
            ),
            Access::Helper => (
                "fn read(source: &str, start: usize, end: usize) -> &str { &source[start..end] } pub fn run() -> &'static str { read(\"abcd\", 3, 1) }",
                1,
                0,
            ),
            Access::Constructor => (
                "struct Span { start: usize, end: usize } fn make() -> Span { Span { start: 3, end: 1 } } fn read(source: &str, span: Span) -> &str { &source[span.start..span.end] } pub fn run() -> &'static str { read(\"abcd\", make()) }",
                1,
                0,
            ),
            Access::Assert => (
                "fn read(start: usize, end: usize) { assert!(start <= end); } pub fn run() { read(3, 1); }",
                0,
                0,
            ),
            Access::Unknown => (
                "pub fn run(source: &str, start: usize, end: usize) -> &str { &source[start..end] }",
                0,
                4,
            ),
            Access::Mutated => (
                "pub fn run<'a>(source: &'a [u8], start: &mut usize, end: usize, change: fn(&mut usize)) -> &'a [u8] { if *start <= end && end <= source.len() { change(start); &source[*start..end] } else { &[] } }",
                0,
                1,
            ),
            Access::Snapshot => (
                "pub fn run() -> &'static str { let mut end = 2; let old = end; end = 0; let _ = end; &\"é\"[0..old] }",
                0,
                0,
            ),
            Access::WrongSource => (
                "pub fn run<'a>(source: &'a str, other: &str, end: usize) -> &'a str { if end <= source.len() && other.is_char_boundary(end) { &source[0..end] } else { \"\" } }",
                0,
                1,
            ),
            Access::CustomIndex => (
                "pub struct Any; impl std::ops::Index<std::ops::Range<usize>> for Any { type Output = str; fn index(&self, _: std::ops::Range<usize>) -> &str { \"\" } } pub fn run(source: &Any) -> &str { &source[3..1] }",
                0,
                0,
            ),
        };
        let output = support::analyze(source, &["--show-analysis-gaps"])?;
        let findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        assert_eq!(
            findings
                .iter()
                .filter(|finding| finding["rule"] == "invalid-state-use")
                .count(),
            invalid,
            "{access:?}: {findings:?}"
        );
        let unresolved_rule = match access {
            Access::Mutated => "invalidated-validation",
            _ => "unproven-precondition",
        };
        assert_eq!(
            findings
                .iter()
                .filter(|finding| finding["rule"] == unresolved_rule)
                .count(),
            unknown,
            "{access:?}: {findings:?}"
        );
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[test]
fn public_span_fields_expose_the_consumer_precondition() -> Result<(), Box<dyn Error>> {
    let source = "pub struct Span { pub start: u32, pub end: u32 }
        impl From<Span> for std::ops::Range<usize> {
            fn from(span: Span) -> Self { span.start as usize..span.end as usize }
        }
        pub fn read(source: &str, span: Span) -> &str { &source[std::ops::Range::<usize>::from(span)] }";
    let output = support::analyze(source, &["--show-analysis-gaps"])?;
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()?;
    let gaps: Vec<_> = findings
        .iter()
        .filter(|finding| finding["rule"] == "unencoded-precondition")
        .collect();
    assert_eq!(gaps.len(), 1, "{findings:?}");
    assert!(
        gaps[0]["footers"][0]["message"]
            .as_str()
            .ok_or("missing witness")?
            .contains("start: 1, end: 0")
    );
    Ok(())
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Owner {
    Private,
    Public,
    Mutable,
    UncheckedConstructor,
    RawMutation,
    UnknownProducer,
}

#[hegel::test]
fn constructors_own_relations_only_when_mutation_cannot_bypass_them(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let owner = tc.draw(hegel::generators::default::<Owner>());
        let source = "pub struct Span { start: usize, end: usize }
            impl Span {
                pub fn try_new(start: usize, end: usize) -> Option<Self> {
                    if start <= end { Some(Self { start, end }) } else { None }
                }
                pub fn read(&self) -> usize { self.end - self.start }
            }";
        let (source, expected) = match owner {
            Owner::RawMutation => (
                format!(
                    "{source} impl Span {{ pub fn change(&mut self, value: usize) {{ let pointer = &raw mut self.start; unsafe {{ *pointer = value; }} }} }}"
                ),
                1,
            ),
            Owner::UnknownProducer => (
                format!("{source} pub fn receive(make: fn() -> Span) {{ make().read(); }}"),
                1,
            ),
            Owner::Private => (source.to_owned(), 0),
            Owner::Public => (
                source.replace(
                    "{ start: usize, end: usize }",
                    "{ pub start: usize, pub end: usize }",
                ),
                1,
            ),
            Owner::Mutable => (
                format!(
                    "{source} impl Span {{ pub fn change(&mut self, value: usize) {{ self.start = value; }} }}"
                ),
                1,
            ),
            Owner::UncheckedConstructor => (
                format!(
                    "{source} impl Span {{ pub fn unchecked(start: usize, end: usize) -> Self {{ Self {{ start, end }} }} }}"
                ),
                1,
            ),
        };
        let output = support::analyze(&source, &["--show-analysis-gaps"])?;
        let findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        let read: Vec<_> = findings
            .iter()
            .filter(|finding| match owner {
                Owner::Public => finding["rule"] == "unencoded-precondition",
                _ => match finding["item"].as_str() {
                    Some(item) => {
                        item.ends_with("::read") && finding["rule"] == "unproven-precondition"
                    }
                    None => false,
                },
            })
            .collect();
        assert_eq!(read.len(), expected, "{owner:?}: {findings:?}");
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum EnforcementCase {
    Violation,
    Unknown,
    Suppressed,
    Representation,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Output {
    Default,
    Text,
    Json,
}

#[hegel::test]
fn denial_applies_only_to_unsuppressed_proven_violations(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let (case, format) = tc.draw(hegel::generators::default::<(EnforcementCase, Output)>());
        let source = match case {
            EnforcementCase::Violation => r#"pub fn run() -> &'static str { &"é"[0..1] }"#,
            EnforcementCase::Unknown => {
                "pub fn run(value: &str, end: usize) -> &str { &value[..end] }"
            }
            EnforcementCase::Suppressed => {
                "// shapelint: allow(invalid-state-use)\n pub fn run() -> &'static str { &\"é\"[0..1] }"
            }
            EnforcementCase::Representation => {
                "pub struct Span { pub start: usize, pub end: usize } pub fn run(value: Span) { assert!(value.start <= value.end); }"
            }
        };
        let arguments: &[&str] = match format {
            Output::Default => &[],
            Output::Text => &["--format", "text"],
            Output::Json => &["--format=json"],
        };
        let directory = tempfile::tempdir()?;
        let path = directory.path().join("invalid.rs");
        std::fs::write(&path, source)?;
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .args(arguments)
            .args([
                "--deny-invalid-states",
                "--crate-type=lib",
                "--edition=2024",
            ])
            .arg(&path)
            .output()?;
        assert!(
            output.stderr.is_empty(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout)?;
        match case {
            EnforcementCase::Violation => {
                assert!(!output.status.success());
                match format {
                    Output::Default | Output::Text => {
                        assert!(stdout.contains("lint[invalid-state-use]"), "{stdout}");
                        assert!(stdout.contains(source), "{stdout}");
                        assert!(stdout.contains("invalid.rs:1:"), "{stdout}");
                        assert_eq!(
                            stdout.matches("lint[invalid-state-use]").count(),
                            1,
                            "{stdout}"
                        );
                    }
                    Output::Json => {
                        let findings: Vec<serde_json::Value> = stdout
                            .lines()
                            .map(serde_json::from_str)
                            .collect::<Result<_, _>>()?;
                        assert_eq!(
                            findings
                                .iter()
                                .filter(|finding| finding["rule"] == "invalid-state-use")
                                .count(),
                            1,
                            "{findings:?}"
                        );
                    }
                }
            }
            EnforcementCase::Unknown
            | EnforcementCase::Suppressed
            | EnforcementCase::Representation => {
                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8_lossy(&output.stderr)
                );
            }
        }
        if let EnforcementCase::Suppressed = case {
            assert!(!stdout.contains("invalid-state-use"), "{stdout}");
        }
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[test]
fn returned_fields_are_compared_with_relational_consumers() -> Result<(), Box<dyn Error>> {
    let output = support::analyze(
        "pub struct Span { start: usize, end: usize } impl Span { pub fn make() -> Self { Self { start: 3, end: 1 } } pub fn read(&self) -> usize { self.end - self.start } }",
        &[],
    )?;
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()?;
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding["rule"] == "inconsistent-state-construction")
            .count(),
        1,
        "{findings:?}"
    );
    Ok(())
}
