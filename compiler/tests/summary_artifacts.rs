#![feature(rustc_private)]

use std::process::Command;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Contract {
    ReturnValue,
    Requirement,
    WidenedAddition,
    AdditionAtMaximum,
    PrivateHelper,
    MacroRequirement,
    SourceOffsets,
    Mutation,
    MissingSummary,
    UnusedDependency,
}

#[hegel::test]
fn dependency_contracts_are_reused_without_assuming_unknown_effects(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Contract>());
    struct Fixture {
        producer: &'static str,
        consumer: &'static str,
        rule: &'static str,
        expected: usize,
    }
    let fixture = match case {
        Contract::ReturnValue => Fixture {
            producer: "pub fn value()->u32 {4}",
            consumer: "pub fn run()->u32 {dependency::value()-1}",
            rule: "unproven-precondition",
            expected: 0,
        },
        Contract::Requirement => Fixture {
            producer: "pub fn decrement(value:u32)->u32 {value-1}",
            consumer: "pub fn run()->u32 {dependency::decrement(0)}",
            rule: "invalid-state-use",
            expected: 1,
        },
        Contract::WidenedAddition => Fixture {
            producer: "pub fn next(x:u32)->u128 {u128::from(x)+1}",
            consumer: "pub fn run(x:u32)->u128 {dependency::next(x)}",
            rule: "unproven-precondition",
            expected: 0,
        },
        Contract::AdditionAtMaximum => Fixture {
            producer: "pub fn next(x:u128)->u128 {x+1}",
            consumer: "pub fn run()->u128 {dependency::next(u128::MAX)}",
            rule: "invalid-state-use",
            expected: 1,
        },
        Contract::PrivateHelper => Fixture {
            producer: "fn decrement(value:u32)->u32 {value-1} pub fn run(value:u32)->u32 {decrement(value)}",
            consumer: "pub fn run()->u32 {dependency::run(0)}",
            rule: "invalid-state-use",
            expected: 1,
        },
        Contract::MacroRequirement => Fixture {
            producer: "macro_rules! subtract {($value:expr)=>{$value-1}} pub fn run(value:u32)->u32 {subtract!(value)}",
            consumer: "pub fn run()->u32 {dependency::run(0)}",
            rule: "invalid-state-use",
            expected: 0,
        },
        Contract::SourceOffsets => Fixture {
            producer: "\u{feff}// λ\r\npub fn decrement(value:u32)->u32 {value-1}\r\n",
            consumer: "pub fn run()->u32 {dependency::decrement(0)}",
            rule: "invalid-state-use",
            expected: 1,
        },
        Contract::Mutation => Fixture {
            producer: "pub fn change(value:&mut u32) {*value=0;}",
            consumer: "pub fn run(mut value:u32)->u32 {if value>=1 {dependency::change(&mut value);value-1}else{0}}",
            rule: "invalidated-validation",
            expected: 1,
        },
        Contract::UnusedDependency => Fixture {
            producer: "pub fn value()->Option<u32> {Some(4)}",
            consumer: "pub fn run()->u32 {0}",
            rule: "unproven-precondition",
            expected: 0,
        },
        Contract::MissingSummary => Fixture {
            producer: "pub fn value()->u32 {4}",
            consumer: "pub fn run()->u32 {dependency::value()-1}",
            rule: "unproven-precondition",
            expected: 1,
        },
    };
    let Fixture {
        producer,
        consumer,
        rule,
        expected,
    } = fixture;
    let directory = tempfile::tempdir().expect("directory");
    let producer_path = directory.path().join("dependency.rs");
    let consumer_path = directory.path().join("consumer.rs");
    let metadata = directory.path().join("libdependency.rmeta");
    let summary = directory.path().join("dependency.shapelint.json");
    std::fs::write(&producer_path, producer).expect("producer source");
    std::fs::write(&consumer_path, consumer).expect("consumer source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-type=lib",
            "--crate-name=dependency",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("-o")
        .arg(&metadata)
        .arg(&producer_path)
        .output()
        .expect("producer analysis");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut command = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"));
    command
        .args([
            "--format=json",
            "--show-analysis-gaps",
            "--crate-type=lib",
            "--crate-name=consumer",
            "--edition=2024",
            "--emit=metadata",
        ])
        .arg("--extern")
        .arg(format!("dependency={}", metadata.display()))
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&consumer_path);
    match case {
        Contract::MissingSummary => {}
        Contract::ReturnValue
        | Contract::Requirement
        | Contract::WidenedAddition
        | Contract::AdditionAtMaximum
        | Contract::PrivateHelper
        | Contract::MacroRequirement
        | Contract::SourceOffsets
        | Contract::Mutation
        | Contract::UnusedDependency => {
            command.arg("--summary-input").arg(&summary);
        }
    }
    let output = command.output().expect("consumer analysis");
    assert!(
        output.status.success(),
        "{case:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).expect("diagnostics");
    let findings: Vec<_> = text
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("finding"))
        .filter(|finding| finding["rule"] == rule)
        .collect();
    assert_eq!(findings.len(), expected, "{case:?}: {text}");
    match case {
        Contract::WidenedAddition | Contract::AdditionAtMaximum => {
            let artifact: serde_json::Value =
                serde_json::from_reader(std::fs::File::open(summary).expect("exported summary"))
                    .expect("summary JSON");
            let exported = artifact["summaries"]
                .as_array()
                .expect("summaries")
                .iter()
                .map(|entry| {
                    entry[1]["requirements"]
                        .as_array()
                        .expect("requirements")
                        .len()
                })
                .sum::<usize>();
            assert_eq!(exported, expected, "{case:?}: exported caller requirements");
        }
        Contract::SourceOffsets => {
            let [finding] = findings.as_slice() else {
                panic!("one imported check: {text}")
            };
            let origin = &finding["related"][0];
            let source = origin["input"]["text"].as_str().expect("original source");
            let start = origin["label"]["span"]["start"].as_u64().expect("start") as usize;
            let end = origin["label"]["span"]["end"].as_u64().expect("end") as usize;
            assert_eq!(source, producer, "original source bytes");
            assert_eq!(
                source.get(start..end),
                Some("value-1"),
                "imported source span"
            );
        }
        Contract::Mutation => {
            let [finding] = findings.as_slice() else {
                panic!("one invalidated validation: {text}")
            };
            let mutation = &finding["related"][0];
            let source = mutation["input"]["text"].as_str().expect("mutation source");
            let start = mutation["label"]["span"]["start"].as_u64().expect("start") as usize;
            let end = mutation["label"]["span"]["end"].as_u64().expect("end") as usize;
            assert_eq!(source, consumer, "mutation occurs at the consumer call");
            assert_eq!(
                source.get(start..end),
                Some("dependency::change(&mut value)"),
                "mutation source span"
            );
        }
        Contract::ReturnValue
        | Contract::Requirement
        | Contract::PrivateHelper
        | Contract::MacroRequirement
        | Contract::MissingSummary
        | Contract::UnusedDependency => {}
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum InvalidArtifact {
    Malformed,
    Compiler,
    Identity,
    MissingReferencedIdentity,
    ReferencedHash,
    UnknownDependencyField,
    UnknownLocationField,
}

#[hegel::test]
fn requested_artifacts_must_match_the_compilation(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<InvalidArtifact>());
    let directory = tempfile::tempdir().expect("directory");
    let source = directory.path().join("dependency.rs");
    let summary = directory.path().join("dependency.shapelint.json");
    let metadata = directory.path().join("libdependency.rmeta");
    std::fs::write(
        &source,
        "pub fn value()->Option<u32> {Some(4)} pub fn decrement(value:u32)->u32 {value-1}",
    )
    .expect("source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-type=lib",
            "--crate-name=dependency",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("-o")
        .arg(&metadata)
        .arg(&source)
        .output()
        .expect("producer");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&summary).expect("summary")).expect("artifact");
    let mut check = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"));
    match case {
        InvalidArtifact::Malformed => {
            std::fs::write(&summary, "not json").expect("malformed artifact")
        }
        InvalidArtifact::Compiler => {
            artifact["compiler"] = "another compiler".into();
            std::fs::write(&summary, serde_json::to_vec(&artifact).expect("encode"))
                .expect("compiler artifact");
        }
        InvalidArtifact::MissingReferencedIdentity => {
            let complete = directory.path().join("complete.json");
            std::fs::copy(&summary, &complete).expect("complete summary");
            check.arg("--summary-input").arg(complete);
            let producer = artifact["producer"].clone();
            let dependencies = artifact["dependencies"]
                .as_array_mut()
                .expect("dependencies");
            assert!(
                dependencies
                    .iter()
                    .any(|dependency| dependency["definition"] != producer),
                "fixture references the Option definition in core"
            );
            dependencies.retain(|dependency| dependency["definition"] == producer);
            std::fs::write(&summary, serde_json::to_vec(&artifact).expect("encode"))
                .expect("missing dependency identity");
        }
        InvalidArtifact::ReferencedHash => {
            let producer = artifact["producer"].clone();
            let dependency = artifact["dependencies"]
                .as_array_mut()
                .expect("dependencies")
                .iter_mut()
                .find(|dependency| dependency["definition"] != producer)
                .expect("referenced core crate");
            dependency["hash"] = "00000000000000000000000000000000".into();
            std::fs::write(&summary, serde_json::to_vec(&artifact).expect("encode"))
                .expect("dependency hash");
        }
        InvalidArtifact::UnknownDependencyField => {
            artifact["dependencies"][0]["unexpected"] = 1.into();
            std::fs::write(&summary, serde_json::to_vec(&artifact).expect("encode"))
                .expect("unknown dependency field");
        }
        InvalidArtifact::UnknownLocationField => {
            let requirement = artifact["summaries"]
                .as_array_mut()
                .expect("summaries")
                .iter_mut()
                .find_map(|entry| entry[1]["requirements"].as_array_mut()?.first_mut())
                .expect("subtraction requirement");
            requirement["consumer"]["location"]["unexpected"] = 1.into();
            std::fs::write(&summary, serde_json::to_vec(&artifact).expect("encode"))
                .expect("unknown location field");
        }
        InvalidArtifact::Identity => {
            artifact["producer"] =
                serde_json::to_value([0u64; 2]).expect("invalid definition identity");
            std::fs::write(&summary, serde_json::to_vec(&artifact).expect("encode"))
                .expect("identity artifact");
        }
    }
    let consumer = directory.path().join("consumer.rs");
    std::fs::write(&consumer, "pub fn run()->Option<u32> {dependency::value()}").expect("consumer");
    let output = check
        .args([
            "--format=json",
            "--crate-type=lib",
            "--emit=metadata",
            "--summary-input",
        ])
        .arg(&summary)
        .arg("--extern")
        .arg(format!("dependency={}", metadata.display()))
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&consumer)
        .output()
        .expect("consumer");
    assert!(
        !output.status.success(),
        "{case:?}: accepted invalid artifact"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("summary"),
        "{case:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    match case {
        InvalidArtifact::UnknownDependencyField | InvalidArtifact::UnknownLocationField => {
            assert!(
                String::from_utf8_lossy(&output.stderr).contains("unknown field"),
                "{case:?}: {}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        InvalidArtifact::MissingReferencedIdentity => {
            assert!(
                String::from_utf8_lossy(&output.stderr).contains("has no validated crate identity"),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
        InvalidArtifact::Malformed
        | InvalidArtifact::Compiler
        | InvalidArtifact::Identity
        | InvalidArtifact::ReferencedHash => {}
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Executable {
    Binary,
    TestHarness,
}

#[hegel::test]
fn executables_do_not_export_reusable_dependency_summaries(tc: hegel::TestCase) {
    let output_kind = tc.draw(hegel::generators::default::<Executable>());
    let (source_text, arguments): (&str, &[&str]) = match output_kind {
        Executable::Binary => ("fn main() {}", &["--crate-type=bin"]),
        Executable::TestHarness => ("pub fn run() {}", &["--crate-type=lib", "--test"]),
    };
    let directory = tempfile::tempdir().expect("directory");
    let source = directory.path().join("program.rs");
    std::fs::write(&source, source_text).expect("source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args(arguments)
        .args(["--format=json", "--emit=metadata", "--summary-output"])
        .arg(directory.path().join("program.summary.json"))
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&source)
        .output()
        .expect("driver");
    assert!(
        !output.status.success(),
        "executable summary must be rejected"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("summary output requires an importable library crate"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum DependencyUse {
    Call,
    SummaryOnly,
}

#[hegel::test]
fn summaries_load_private_transitive_dependency_metadata(tc: hegel::TestCase) {
    let usage = tc.draw(hegel::generators::default::<DependencyUse>());
    let directory = tempfile::tempdir().expect("directory");
    let third = directory.path().join("third.rs");
    let third_metadata = directory.path().join("libthird.rmeta");
    let third_summary = directory.path().join("third.summary.json");
    std::fs::write(&third, "pub fn decrement(value:u32)->u32 {value-1}")
        .expect("third-party source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-type=lib",
            "--crate-name=third",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&third_summary)
        .arg("-o")
        .arg(&third_metadata)
        .arg(&third)
        .output()
        .expect("third-party analysis");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let middle = directory.path().join("middle.rs");
    let middle_metadata = directory.path().join("libmiddle.rmeta");
    let middle_summary = directory.path().join("middle.summary.json");
    std::fs::write(
        &middle,
        "pub fn run(value:u32)->u32 {third::decrement(value)}",
    )
    .expect("middle source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-type=lib",
            "--crate-name=middle",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&middle_summary)
        .arg("--summary-input")
        .arg(&third_summary)
        .arg("--extern")
        .arg(format!("third={}", third_metadata.display()))
        .arg("-o")
        .arg(&middle_metadata)
        .arg(&middle)
        .output()
        .expect("middle analysis");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let (source, expected) = match usage {
        DependencyUse::Call => ("pub fn run()->u32 {middle::run(0)}", 1),
        DependencyUse::SummaryOnly => ("pub fn run()->u32 {0}", 0),
    };
    let consumer = directory.path().join("consumer.rs");
    std::fs::write(&consumer, source).expect("consumer source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-type=lib",
            "--crate-name=consumer",
            "--edition=2024",
            "--emit=metadata",
            "--summary-input",
        ])
        .arg(&middle_summary)
        .arg("--extern")
        .arg(format!("middle={}", middle_metadata.display()))
        .arg("-L")
        .arg(format!("dependency={}", directory.path().display()))
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&consumer)
        .output()
        .expect("consumer analysis");
    assert!(
        output.status.success(),
        "{usage:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let text = String::from_utf8(output.stdout).expect("diagnostics");
    let findings: Vec<_> = text
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("finding"))
        .filter(|finding| finding["rule"] == "invalid-state-use")
        .collect();
    assert_eq!(findings.len(), expected, "{usage:?}: {text}");
    match usage {
        DependencyUse::Call => {
            let [finding] = findings.as_slice() else {
                panic!("one transitive requirement: {text}")
            };
            assert_eq!(
                finding["related"][0]["input"]["text"],
                "pub fn decrement(value:u32)->u32 {value-1}"
            );
        }
        DependencyUse::SummaryOnly => {}
    }
}
