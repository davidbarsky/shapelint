mod support;

#[test]
fn protocol_names_cover_helpers_and_const_evaluated_signatures() {
    let source = r#"
#![feature(register_tool)]
#![register_tool(shapelint)]
pub struct Database;
pub const fn width() -> usize { 1 }
#[shapelint::protocol(durability, invalidate)]
pub fn write(_: &Database) {}
#[shapelint::protocol(durability, establish)]
pub fn barrier(_: &Database, _: [(); width()]) {}
#[shapelint::protocol(durability, require)]
pub fn publish(_: &Database) {}
#[shapelint::protocol(visibility, invalidate)]
pub fn obscure(_: &Database) {}
#[shapelint::protocol(visibility, require)]
pub fn observe(_: &Database) {}
pub fn prepare(db: &Database) { write(db); obscure(db); }
pub fn flush(db: &Database) { barrier(db, [(); width()]); }
pub fn run(db: &Database) { prepare(db); flush(db); publish(db); observe(db); }
"#;
    let output = support::analyze(source, &[]).expect("protocol catalog analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "protocol-bypass" && finding["item"] == "run"
        })
        .collect();
    assert_eq!(findings.len(), 1, "{output}");
}

#[test]
fn invalid_unused_declaration_is_reported_once_before_capture() {
    let directory = tempfile::tempdir().expect("compiler output directory");
    let path = directory.path().join("catalog.rs");
    std::fs::write(
        &path,
        r#"
#![feature(register_tool)]
#![register_tool(shapelint)]
pub struct Database;
#[shapelint::protocol(durability, establish)]
pub fn invalid(_: Database) {}
pub fn first() {}
pub fn second() {}
pub fn third() {}
"#,
    )
    .expect("compiler input");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
        ])
        .arg("--out-dir")
        .arg(directory.path())
        .arg(path)
        .output()
        .expect("compiler execution");
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let errors = String::from_utf8(output.stderr).expect("compiler diagnostics");
    assert_eq!(
        errors
            .matches("a protocol operation takes its resource by reference first")
            .count(),
        1,
        "{errors}"
    );
}

#[test]
fn body_capture_without_protocols_accepts_const_evaluated_signatures() {
    let output = support::analyze(
        "pub const fn width()->usize{1} pub fn first(_: [();width()]){} pub fn second(){first([();width()])}",
        &[],
    )
    .expect("analysis without protocols");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "protocol-bypass")
        .collect();
    assert!(findings.is_empty(), "{output}");
}
