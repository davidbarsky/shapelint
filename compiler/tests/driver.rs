#![feature(rustc_private)]

mod support;

use crate::support::analyze;
use std::error::Error;
use std::fs;
use std::process::Command;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Mutation {
    RenamedLocals,
    ChangedError,
    ChangedResult,
    ChangedCallee,
    ExtraEffect,
    SharedImplementation,
    Suppressed,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Suspension {
    Renamed,
    DropBeforeAwait,
    ExtraAwait,
    Suppressed,
}

#[hegel::test]
fn suspension_and_cancellation_remain_in_the_graph(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let suspension = tc.draw(hegel::generators::default::<Suspension>());
        let source = include_str!("fixtures/async_completion.rs");
        let (_, function) = source
            .split_once("pub async fn ")
            .ok_or("missing fixture function")?;
        let function = format!("pub async fn {function}").replace("complete(", "renamed(");
        let (function, expected) = match suspension {
            Suspension::Renamed => (function, 1),
            Suspension::Suppressed => (
                format!("// shapelint: allow(duplicate-control-flow)\n{function}"),
                0,
            ),
            Suspension::DropBeforeAwait => (
                function.replace(
                    "wait(completions).await?;\n                drop(guard);",
                    "drop(guard);\n                wait(completions).await?;",
                ),
                0,
            ),
            Suspension::ExtraAwait => (
                function.replace(
                    "wait(completions).await?;",
                    "wait(completions).await?; wait(completions).await?;",
                ),
                0,
            ),
        };
        let output = analyze(&format!("{source}\n{function}"), &[])?;
        let mut findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        findings.retain(|finding| finding["rule"] == "duplicate-control-flow");
        assert_eq!(findings.len(), expected, "{suspension:?}: {findings:?}");
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[hegel::test]
fn completion_protocol_preserves_effects_and_errors(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let mutation = tc.draw(hegel::generators::default::<Mutation>());
        let source = include_str!("fixtures/completion.rs");
        let (_, function) = source
            .split_once("pub fn complete(")
            .ok_or("missing fixture function")?;
        let function = format!("pub fn complete({function}")
            .replace("complete(", "renamed(")
            .replace("operation", "request")
            .replace("completions", "pending")
            .replace("value", "result");
        let (function, expected) = match mutation {
            Mutation::RenamedLocals => (function, 1),
            Mutation::ChangedCallee => (
                function.replace("observe(request()?)", "observe_other(request()?)"),
                0,
            ),
            Mutation::ChangedError => (
                function.replace("wait(pending)?", "wait(pending).map_err(|_| 42)?"),
                0,
            ),
            Mutation::ChangedResult => (
                function
                    .replace("Step::Done(result)", "Step::Done(_)")
                    .replace("Ok(result)", "Ok(42)"),
                0,
            ),
            Mutation::ExtraEffect => (
                function.replace("wait(pending)?", "{ wait(pending)?; wait(pending)?; }"),
                0,
            ),
            Mutation::SharedImplementation => (
                "pub fn renamed(
                    operation: fn() -> Result<Step, u8>,
                    wait: fn(u32) -> Result<(), u8>,
                ) -> Result<u32, u8> {
                    complete(operation, wait)
                }"
                .into(),
                0,
            ),
            Mutation::Suppressed => (
                format!("// shapelint: allow(duplicate-control-flow)\n{function}"),
                0,
            ),
        };
        let output = analyze(&format!("{source}\n{function}"), &[])?;
        let mut findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        findings.retain(|finding| finding["rule"] == "duplicate-control-flow");
        assert_eq!(findings.len(), expected, "{mutation:?}: {findings:?}");
        for finding in findings {
            assert_eq!(finding["rule"], "duplicate-control-flow");
            assert_eq!(finding["item"], "renamed");
            assert_eq!(finding["kind"], "lint");
            assert_eq!(
                finding["related"][0]["label"]["message"],
                "implementation in `complete`"
            );
        }
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[test]
fn compiler_errors_fail_the_driver() -> Result<(), Box<dyn Error>> {
    let directory = tempfile::tempdir()?;
    let path = directory.path().join("invalid.rs");
    fs::write(&path, "pub fn invalid() { unknown(); }")?;
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .arg("--crate-type=lib")
        .arg(&path)
        .output()?;
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("cannot find function"));
    Ok(())
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum InvalidFormat {
    Missing,
    Empty,
    Unsupported,
}

#[hegel::test]
fn invalid_output_formats_fail_before_compilation(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let format = tc.draw(hegel::generators::default::<InvalidFormat>());
        let arguments: &[&str] = match format {
            InvalidFormat::Missing => &["--format"],
            InvalidFormat::Empty => &["--format="],
            InvalidFormat::Unsupported => &["--format", "xml"],
        };
        let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .args(arguments)
            .output()?;
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
        assert_eq!(
            String::from_utf8(output.stderr)?,
            "shapelint-driver: --format requires text, json, record, or record-json\n"
        );
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}
