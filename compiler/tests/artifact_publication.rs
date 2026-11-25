#![feature(rustc_private)]

use std::path::PathBuf;
use std::process::Command;

use serde::Deserialize;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Rejection {
    Syntax,
    IncompatibleSummary,
    DeniedState,
}

#[derive(Deserialize, PartialEq, Eq)]
struct Definition(u64, u64);

#[derive(Deserialize)]
struct Dependency {
    definition: Definition,
    metadata: PathBuf,
}

#[derive(Deserialize)]
struct Artifact {
    producer: Definition,
    dependencies: Vec<Dependency>,
}

#[hegel::test(print_blob = true)]
fn rejected_compilations_preserve_a_usable_summary(tc: hegel::TestCase) {
    let rejection = tc.draw(hegel::generators::default::<Rejection>());
    let directory = tempfile::tempdir().expect("source directory");
    let producer = directory.path().join("dependency.rs");
    let metadata = directory.path().join("libdependency.rmeta");
    let summary = directory.path().join("dependency.summary.json");
    std::fs::write(&producer, "pub fn value()->u32 {1}").expect("producer source");
    let built = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-name=dependency",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("-o")
        .arg(&metadata)
        .arg(&producer)
        .output()
        .expect("initial compilation");
    assert!(
        built.status.success(),
        "{}",
        String::from_utf8_lossy(&built.stderr)
    );
    let original = std::fs::read(&summary).expect("initial summary");
    let artifact: Artifact = serde_json::from_slice(&original).expect("summary identity");
    let companion = artifact
        .dependencies
        .iter()
        .find(|dependency| dependency.definition == artifact.producer)
        .expect("summary retains its producer metadata");
    let original_metadata = std::fs::read(&companion.metadata).expect("retained producer metadata");

    let mut command = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"));
    command
        .args([
            "--format=json",
            "--crate-name=dependency",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("-o")
        .arg(&metadata)
        .arg(&producer);
    match rejection {
        Rejection::Syntax => {
            std::fs::write(&producer, "pub fn value( -> u32 {").expect("broken source");
        }
        Rejection::IncompatibleSummary => {
            std::fs::write(&producer, "pub fn value()->u32 {2}").expect("changed source");
            let mut incompatible: serde_json::Value =
                serde_json::from_slice(&original).expect("summary");
            incompatible["format"] = "not-a-supported-summary".into();
            incompatible["dependencies"] = serde_json::Value::Array(Vec::new());
            let input = directory.path().join("incompatible.json");
            std::fs::write(
                &input,
                serde_json::to_vec(&incompatible).expect("incompatible summary"),
            )
            .expect("summary input");
            command.arg("--summary-input").arg(input);
        }
        Rejection::DeniedState => {
            std::fs::write(
                &producer,
                "fn decrement(value:u32)->u32 {value-1} pub fn value()->u32 {decrement(0)}",
            )
            .expect("invalid-state source");
            command.arg("--deny-invalid-states");
        }
    }
    let rejected = command.output().expect("rejected compilation");
    assert!(
        !rejected.status.success(),
        "{rejection:?}: {}",
        String::from_utf8_lossy(&rejected.stdout)
    );
    match rejection {
        Rejection::Syntax => assert!(!rejected.stderr.is_empty()),
        Rejection::IncompatibleSummary => assert!(
            String::from_utf8_lossy(&rejected.stderr).contains("different format"),
            "{}",
            String::from_utf8_lossy(&rejected.stderr)
        ),
        Rejection::DeniedState => assert!(
            String::from_utf8_lossy(&rejected.stdout).contains("invalid-state-use"),
            "{}",
            String::from_utf8_lossy(&rejected.stderr)
        ),
    }
    assert_eq!(
        std::fs::read(&summary).expect("preserved summary"),
        original
    );
    assert_eq!(
        std::fs::read(&companion.metadata).expect("preserved companion"),
        original_metadata
    );

    let consumer = directory.path().join("consumer.rs");
    std::fs::write(&consumer, "pub fn run()->u32 {dependency::value()-1}")
        .expect("consumer source");
    let consumed = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-input",
        ])
        .arg(&summary)
        .arg("--extern")
        .arg(format!("dependency={}", companion.metadata.display()))
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&consumer)
        .output()
        .expect("consumer compilation");
    assert!(
        consumed.status.success(),
        "{}",
        String::from_utf8_lossy(&consumed.stderr)
    );
    let output = String::from_utf8(consumed.stdout).expect("diagnostics");
    assert!(!output.contains("invalid-state-use"), "{output}");
    assert!(!output.contains("unproven-precondition"), "{output}");
}

#[test]
fn summary_replacement_keeps_prior_metadata_available() {
    let directory = tempfile::tempdir().expect("source directory");
    let producer = directory.path().join("dependency.rs");
    let metadata = directory.path().join("libdependency.rmeta");
    let summary = directory.path().join("dependency.summary.json");
    std::fs::write(&producer, "pub fn value()->u32 {1}").expect("producer source");
    let first = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-name=dependency",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("-o")
        .arg(&metadata)
        .arg(&producer)
        .output()
        .expect("first compilation");
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let original = std::fs::read(&summary).expect("first summary");
    let artifact: Artifact = serde_json::from_slice(&original).expect("summary identity");
    let companion = artifact
        .dependencies
        .iter()
        .find(|dependency| dependency.definition == artifact.producer)
        .expect("producer metadata");
    let original_metadata = std::fs::read(&companion.metadata).expect("first metadata");

    std::fs::write(&producer, "pub fn value()->u32 {2}").expect("new producer");
    let second = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-name=dependency",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("-o")
        .arg(&metadata)
        .arg(&producer)
        .output()
        .expect("second compilation");
    assert!(
        second.status.success(),
        "{}",
        String::from_utf8_lossy(&second.stderr)
    );
    let replacement = std::fs::read(&summary).expect("replacement summary");
    assert_ne!(original, replacement);
    let replacement: Artifact = serde_json::from_slice(&replacement).expect("replacement identity");
    let replacement_companion = replacement
        .dependencies
        .iter()
        .find(|dependency| dependency.definition == replacement.producer)
        .expect("replacement producer metadata");
    assert_ne!(replacement_companion.metadata, companion.metadata);
    assert_eq!(
        std::fs::read(&companion.metadata).expect("prior metadata"),
        original_metadata
    );
}

#[hegel::test(print_blob = true)]
fn summary_bytes_do_not_depend_on_import_order(tc: hegel::TestCase) {
    let values = tc.draw(hegel::generators::default::<[u8; 2]>());
    let directory = tempfile::tempdir().expect("source directory");
    let mut summaries = Vec::new();
    let producers = ["first", "second"].into_iter().zip(values);
    for (name, value) in producers {
        let source = directory.path().join(format!("{name}.rs"));
        let metadata = directory.path().join(format!("lib{name}.rmeta"));
        let summary = directory.path().join(format!("{name}.summary.json"));
        std::fs::write(&source, format!("pub fn value()->u32 {{{value}}}"))
            .expect("dependency source");
        let built = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .args([
                "--format=json",
                "--crate-type=lib",
                "--edition=2024",
                "--emit=metadata",
                "--crate-name",
            ])
            .arg(name)
            .arg("--summary-output")
            .arg(&summary)
            .arg("-o")
            .arg(&metadata)
            .arg(&source)
            .output()
            .expect("dependency compilation");
        assert!(
            built.status.success(),
            "{}",
            String::from_utf8_lossy(&built.stderr)
        );
        summaries.push((summary, format!("{name}={}", metadata.display())));
    }
    let consumer = directory.path().join("consumer.rs");
    let metadata = directory.path().join("libconsumer.rmeta");
    let summary = directory.path().join("consumer.summary.json");
    std::fs::write(
        &consumer,
        "pub fn run()->u32 {first::value()+second::value()}",
    )
    .expect("consumer source");
    let mut first = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"));
    first
        .args([
            "--format=json",
            "--crate-name=consumer",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("-o")
        .arg(&metadata)
        .arg(&consumer);
    for (summary, metadata) in &summaries {
        first
            .arg("--summary-input")
            .arg(summary)
            .arg("--extern")
            .arg(metadata);
    }
    let first = first.output().expect("first consumer compilation");
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let original = std::fs::read(&summary).expect("consumer summary");

    let mut reversed = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"));
    reversed
        .args([
            "--format=json",
            "--crate-name=consumer",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("-o")
        .arg(&metadata)
        .arg(&consumer);
    let summaries = summaries.iter().rev();
    for (summary, metadata) in summaries {
        reversed
            .arg("--summary-input")
            .arg(summary)
            .arg("--extern")
            .arg(metadata);
    }
    let reversed = reversed.output().expect("reversed consumer compilation");
    assert!(
        reversed.status.success(),
        "{}",
        String::from_utf8_lossy(&reversed.stderr)
    );
    assert_eq!(
        std::fs::read(&summary).expect("reordered summary"),
        original
    );
}
