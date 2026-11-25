#![feature(rustc_private)]

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Subtraction {
    Parameter,
    Guarded,
    NonzeroGuarded,
    NonzeroTooSmall,
    SafeCaller,
    InvalidCaller,
    Forwarded,
    UnknownCaller,
    LoopLocal,
}

#[hegel::test]
fn subtraction_diagnostics_explain_the_requirement_and_evidence(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Subtraction>());
    let (source, rule, expected) = match case {
        Subtraction::Parameter => (
            "pub fn run(position: u32) -> u32 { position - 1 }",
            "unproven-precondition",
            Some("requires position >= 1"),
        ),
        Subtraction::Guarded => (
            "pub fn run(position: u32) -> u32 { if position >= 1 { position - 1 } else { 0 } }",
            "unproven-precondition",
            None,
        ),
        Subtraction::NonzeroGuarded => (
            "pub fn run(position:u32)->u32 {match position {0=>0,_=>position-1}}",
            "unproven-precondition",
            None,
        ),
        Subtraction::NonzeroTooSmall => (
            "pub fn run(position:u32)->u32 {match position {0=>0,_=>position-2}}",
            "unproven-precondition",
            Some("requires position >= 2"),
        ),
        Subtraction::SafeCaller => (
            "fn decrement(position: u32) -> u32 { position - 1 } pub fn run() -> u32 { decrement(1) }",
            "unproven-precondition",
            None,
        ),
        Subtraction::InvalidCaller => (
            "fn decrement(position: u32) -> u32 { position - 1 } pub fn run() -> u32 { decrement(0) }",
            "invalid-state-use",
            Some("requires 0 >= 1"),
        ),
        Subtraction::Forwarded => (
            "fn decrement(position: u32) -> u32 { position - 1 } pub fn run(input: u32) -> u32 { decrement(input) }",
            "unproven-precondition",
            Some("requires input >= 1"),
        ),
        Subtraction::UnknownCaller => (
            "fn decrement(position: u32) -> u32 { position - 1 } pub fn run(make: fn() -> u32) -> u32 { decrement(make()) }",
            "unproven-precondition",
            Some("requires make() >= 1"),
        ),
        Subtraction::LoopLocal => (
            "pub fn run(values: &[u32]) -> usize { let mut output = 0; for &position in values { output = position as usize - 1; } output }",
            "unproven-precondition",
            Some("requires position as usize >= 1"),
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
    match case {
        Subtraction::InvalidCaller => assert_eq!(output.status.code(), Some(1), "{output:?}"),
        Subtraction::Parameter
        | Subtraction::Guarded
        | Subtraction::NonzeroGuarded
        | Subtraction::NonzeroTooSmall
        | Subtraction::SafeCaller
        | Subtraction::Forwarded
        | Subtraction::UnknownCaller
        | Subtraction::LoopLocal => assert!(output.status.success(), "{output:?}"),
    }
    assert!(output.stderr.is_empty(), "{output:?}");
    let output = String::from_utf8(output.stdout).expect("UTF-8");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["message"]
                .as_str()
                .expect("message")
                .contains("subtraction")
        })
        .collect();
    match expected {
        Some(expected) => {
            assert_eq!(findings.len(), 1, "{case:?}: {output}");
            assert_eq!(findings[0]["rule"], rule);
            assert_eq!(findings[0]["primary"]["message"], expected);
            let title = match case {
                Subtraction::InvalidCaller => "subtraction will underflow",
                Subtraction::NonzeroTooSmall
                | Subtraction::Parameter
                | Subtraction::Forwarded
                | Subtraction::UnknownCaller
                | Subtraction::LoopLocal => "could not prove subtraction cannot underflow",
                Subtraction::Guarded | Subtraction::NonzeroGuarded | Subtraction::SafeCaller => {
                    unreachable!("no subtraction finding expected")
                }
            };
            assert_eq!(findings[0]["message"], title);
        }
        None => assert!(findings.is_empty(), "{case:?}: {output}"),
    }
    assert!(
        !output.contains("could not determine the required condition"),
        "{output}"
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Unsupported {
    SignedSubtraction,
    Multiplication,
    RecursiveCall,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Visibility {
    Default,
    Explicit,
}

#[hegel::test]
fn unsupported_checks_are_separate_and_opt_in(tc: hegel::TestCase) {
    let (operation, visibility) =
        tc.draw(hegel::generators::default::<(Unsupported, Visibility)>());
    let (source, reason) = match operation {
        Unsupported::SignedSubtraction => (
            "pub fn run(value: i32) -> i32 { value - 1 }",
            "signed subtraction overflow checking is not supported",
        ),
        Unsupported::Multiplication => (
            "pub fn run(value: u32) -> u32 { value * 2 }",
            "multiplication overflow checking is not supported",
        ),
        Unsupported::RecursiveCall => (
            "pub fn run(value: u32) -> u32 { if value == 0 { 0 } else { run(value) } }",
            "recursive call requirements",
        ),
    };
    let directory = tempfile::tempdir().expect("source directory");
    let path = directory.path().join("input.rs");
    std::fs::write(&path, source).expect("write source");
    let mut command = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"));
    command.args(["--format=json", "--deny-invalid-states", "--crate-type=lib"]);
    match visibility {
        Visibility::Default => {}
        Visibility::Explicit => {
            command.arg("--show-analysis-gaps");
        }
    }
    let output = command.arg(&path).output().expect("driver analysis");
    assert!(output.status.success(), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).expect("UTF-8");
    let findings: Vec<serde_json::Value> = stdout
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "analysis-incomplete" || finding["rule"] == "unproven-precondition"
        })
        .collect();
    match visibility {
        Visibility::Default => assert!(findings.is_empty(), "{stdout}"),
        Visibility::Explicit => {
            assert_eq!(findings.len(), 1, "{stdout}");
            assert_eq!(findings[0]["rule"], "analysis-incomplete");
            assert_eq!(findings[0]["primary"]["message"], reason);
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Division {
    Quotient,
    Remainder,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Operands {
    ZeroNumerator,
    ZeroDenominator,
    BothZero,
    NeitherZero,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Integer {
    Unsigned,
    Signed,
}

#[hegel::test]
fn zero_divisor_checks_use_the_denominator(tc: hegel::TestCase) {
    let (operation, operands, integer) =
        tc.draw(hegel::generators::default::<(Division, Operands, Integer)>());
    let integer = match integer {
        Integer::Unsigned => "usize",
        Integer::Signed => "isize",
    };
    let operator = match operation {
        Division::Quotient => "/",
        Division::Remainder => "%",
    };
    let (numerator, denominator, exit) = match operands {
        Operands::ZeroNumerator => (0, 3, 0),
        Operands::ZeroDenominator => (3, 0, 1),
        Operands::BothZero => (0, 0, 1),
        Operands::NeitherZero => (3, 3, 0),
    };
    let source = format!(
        "fn divide(n: {integer}, d: {integer}) -> {integer} {{ n {operator} d }} pub fn run() -> {integer} {{ divide({numerator}, {denominator}) }}"
    );
    let directory = tempfile::tempdir().expect("source directory");
    let path = directory.path().join("input.rs");
    std::fs::write(&path, source).expect("write source");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args(["--format=json", "--deny-invalid-states", "--crate-type=lib"])
        .arg(&path)
        .output()
        .expect("driver analysis");
    assert_eq!(output.status.code(), Some(exit), "{output:?}");
    assert!(output.stderr.is_empty(), "{output:?}");
    let stdout = String::from_utf8(output.stdout).expect("UTF-8");
    let findings: Vec<serde_json::Value> = stdout
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "invalid-state-use" || finding["rule"] == "unproven-precondition"
        })
        .collect();
    match operands {
        Operands::ZeroNumerator | Operands::NeitherZero => assert!(findings.is_empty(), "{stdout}"),
        Operands::ZeroDenominator | Operands::BothZero => {
            assert_eq!(findings.len(), 1, "{stdout}");
            assert_eq!(findings[0]["primary"]["message"], "0 != 0");
        }
    }
}
