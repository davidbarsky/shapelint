#![feature(rustc_private)]

use std::error::Error;
use std::fs;
use std::process::Command;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Color {
    Automatic,
    Always,
    Never,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Format {
    Text,
    Json,
    Record,
}

#[hegel::test]
fn caller_color_survives_captured_stdout(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let (color, format) = tc.draw(hegel::generators::default::<(Color, Format)>());
        let directory = tempfile::tempdir()?;
        let path = directory.path().join("invalid.rs");
        fs::write(&path, r#"pub fn run() -> &'static str { &"é"[0..1] }"#)?;
        let mut command = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"));
        command.env_remove("SHAPELINT_CARGO_COLOR");
        match color {
            Color::Automatic => {}
            Color::Always => {
                command.env("SHAPELINT_CARGO_COLOR", "always");
            }
            Color::Never => {
                command.env("SHAPELINT_CARGO_COLOR", "never");
            }
        }
        match format {
            Format::Text => {
                command.arg("--format=text");
            }
            Format::Json => {
                command.arg("--format=json");
            }
            Format::Record => {
                command.arg("--format=record");
            }
        }
        let output = command.arg("--crate-type=lib").arg(&path).output()?;
        assert!(output.status.success(), "{:?}", output);
        assert!(output.stderr.is_empty(), "{:?}", output);
        let stdout = String::from_utf8(output.stdout)?;
        assert!(stdout.contains("invalid-state-use"), "{stdout}");
        let rendered = match format {
            Format::Text | Format::Json => stdout.clone(),
            Format::Record => {
                let records: Vec<serde_json::Value> = stdout
                    .lines()
                    .map(serde_json::from_str)
                    .collect::<Result<_, _>>()?;
                let record = records
                    .iter()
                    .find(|record| record["finding"]["rule"] == "invalid-state-use")
                    .ok_or("missing recorded finding")?;
                record["rendered"]
                    .as_str()
                    .ok_or("missing rendered diagnostic")?
                    .to_owned()
            }
        };
        match (color, format) {
            (Color::Always, Format::Text | Format::Record) => {
                assert!(rendered.contains('\u{1b}'), "{rendered}")
            }
            (Color::Automatic | Color::Never, Format::Text | Format::Record)
            | (_, Format::Json) => {
                assert!(!rendered.contains('\u{1b}'), "{rendered}");
            }
        }
        if let Format::Json = format {
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
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}
