#![feature(rustc_private)]

use std::process::Command;

#[test]
fn executable_check_writes_cargo_outputs() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("main.rs");
    let metadata = directory.path().join("libmain.rmeta");
    std::fs::write(&source, "fn main() {}\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--cargo-check-only",
            "--crate-name",
            "main",
            "--emit=dep-info,metadata",
        ])
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&source)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(metadata.exists());
    assert!(directory.path().join("main.d").exists());
    let oracle = tempfile::tempdir().unwrap();
    let rustc = std::path::Path::new(env!("SHAPELINT_SYSROOT")).join("bin/rustc");
    let output = Command::new(rustc)
        .args(["--crate-name", "main", "--emit=dep-info,metadata"])
        .arg("--out-dir")
        .arg(oracle.path())
        .arg(&source)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        std::fs::read(&metadata).unwrap(),
        std::fs::read(oracle.path().join("libmain.rmeta")).unwrap()
    );
    assert!(oracle.path().join("main.d").exists());
}

#[test]
fn check_only_rejects_link_output() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("main.rs");
    std::fs::write(&source, "fn main() {}\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args(["--cargo-check-only", "--crate-name", "main", "--emit=link"])
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&source)
        .output()
        .unwrap();
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("--cargo-check-only requires dep-info and metadata output")
    );
}

#[test]
fn check_metadata_and_summary_are_importable_together() {
    let directory = tempfile::tempdir().unwrap();
    let producer = directory.path().join("producer.rs");
    let consumer = directory.path().join("consumer.rs");
    let metadata = directory.path().join("libproducer.rmeta");
    let summary = directory.path().join("producer.json");
    std::fs::write(&producer, "pub fn value() -> u32 { 42 }\n").unwrap();
    std::fs::write(&consumer, "pub fn value() -> u32 { producer::value() }\n").unwrap();
    let produced = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--cargo-check-only",
            "--crate-name",
            "producer",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=dep-info,metadata",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("-o")
        .arg(&metadata)
        .arg(&producer)
        .output()
        .unwrap();
    assert!(
        produced.status.success(),
        "{}",
        String::from_utf8_lossy(&produced.stderr)
    );
    let consumed = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--cargo-check-only",
            "--crate-name",
            "consumer",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=dep-info,metadata",
            "--summary-input",
        ])
        .arg(&summary)
        .arg("--extern")
        .arg(format!("producer={}", metadata.display()))
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&consumer)
        .output()
        .unwrap();
    assert!(
        consumed.status.success(),
        "{}",
        String::from_utf8_lossy(&consumed.stderr)
    );
    assert!(directory.path().join("libconsumer.rmeta").exists());
}

#[test]
fn metadata_stdout_is_separate_from_findings() {
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("producer.rs");
    let summary = directory.path().join("producer.json");
    let findings = directory.path().join("findings.jsonl");
    std::fs::write(&source, "pub fn value() -> u32 { 42 }\n").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-name",
            "producer",
            "--crate-type=lib",
            "--emit=metadata=-",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("--diagnostics-output")
        .arg(&findings)
        .arg(&source)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(output.stdout.starts_with(b"rust"));
    let text = std::fs::read_to_string(findings).unwrap();
    let _: Vec<serde_json::Value> = text
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()
        .unwrap();
    assert!(summary.exists());
}
