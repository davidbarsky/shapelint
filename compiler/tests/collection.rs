#![feature(rustc_private)]

use std::error::Error;
use std::fs;
use std::process::Command;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Difference {
    Fingerprint,
    Evidence,
    Location,
    RelatedLocation,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Output {
    Plain,
    Ansi,
    Json,
}

#[hegel::test]
fn cargo_collection_merges_only_repeated_findings(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let (difference, output) = tc.draw(hegel::generators::default::<(Difference, Output)>());
        let directory = tempfile::tempdir()?;
        let path = directory.path().join("duplicate.rs");
        fs::write(&path, "pub fn first(flag: bool, a: fn(), b: fn(), setup: fn()) { setup(); if flag { a(); } else { b(); } }\n
            pub fn second(flag: bool, a: fn(), b: fn(), setup: fn()) { setup(); setup(); if flag { a(); } else { b(); } }")?;
        let color = match output {
            Output::Plain | Output::Json => "never",
            Output::Ansi => "always",
        };
        let result = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .env("SHAPELINT_CARGO_COLOR", color)
            .args(["--format=record", "--crate-type=lib"])
            .arg(&path)
            .output()?;
        assert!(result.status.success(), "{result:?}");
        let mut records: Vec<serde_json::Value> = String::from_utf8(result.stdout)?
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        let sources: std::collections::HashMap<_, _> = records
            .iter()
            .filter(|record| record["record"] == "source")
            .map(|record| {
                (
                    record["id"].as_u64().expect("source ID"),
                    record["input"].clone(),
                )
            })
            .collect();
        for record in &mut records {
            if record["record"] != "finding" {
                continue;
            }
            let related = record["related"].as_array().ok_or("related references")?;
            let related: Vec<_> = related
                .iter()
                .map(|reference| {
                    let mut location = reference.clone();
                    location
                        .as_object_mut()
                        .expect("related location")
                        .remove("source");
                    location["input"] =
                        sources[&reference["source"].as_u64().expect("source reference")].clone();
                    location
                })
                .collect();
            record["finding"]["related"] = related.into();
            record
                .as_object_mut()
                .expect("finding record")
                .remove("record");
            record
                .as_object_mut()
                .expect("finding record")
                .remove("related");
        }

        let record = records
            .into_iter()
            .find(|record| record["finding"]["rule"] == "duplicate-control-flow")
            .ok_or("missing duplicate-control-flow")?;
        let mut other = record.clone();
        other["finding"]["fingerprint"] = "another-target-fingerprint".into();
        other["finding"]["path"] = "./duplicate.rs".into();
        other["finding"]["related"][0]["input"]["name"] = "./duplicate.rs".into();
        let expected = match difference {
            Difference::Fingerprint => 1,
            Difference::Evidence => {
                other["finding"]["primary"]["message"] = "a different obligation".into();
                2
            }
            Difference::Location => {
                other["finding"]["path"] = "other.rs".into();
                2
            }
            Difference::RelatedLocation => {
                other["finding"]["related"][0]["input"]["name"] = "other.rs".into();
                2
            }
        };
        fs::write(
            directory.path().join("records.jsonl"),
            format!(
                "{}\n{}\n{}\n",
                serde_json::to_string(&record)?,
                serde_json::to_string(&other)?,
                serde_json::to_string(&record)?
            ),
        )?;
        let format = match output {
            Output::Plain | Output::Ansi => "text",
            Output::Json => "json",
        };
        let result = Command::new("python3")
            .args(["-c", "import sys; from pathlib import Path; sys.path.insert(0, sys.argv[1]); import check; directory = Path(sys.argv[2]); check.report([(directory, directory / 'records.jsonl')], sys.argv[3])"])
            .arg(env!("CARGO_MANIFEST_DIR"))
            .arg(directory.path())
            .arg(format)
            .output()?;
        assert!(result.status.success(), "{result:?}");
        assert!(result.stderr.is_empty(), "{result:?}");
        let stdout = String::from_utf8(result.stdout)?;
        match output {
            Output::Plain | Output::Ansi => {
                let rendered = record["rendered"].as_str().ok_or("rendered diagnostic")?;
                assert_eq!(stdout, rendered.repeat(expected));
            }
            Output::Json => {
                assert_eq!(stdout.lines().count(), expected, "{stdout}");
                let findings: Vec<serde_json::Value> = stdout
                    .lines()
                    .map(serde_json::from_str)
                    .collect::<Result<_, _>>()?;
                assert!(findings.contains(&record["finding"]), "{findings:?}");
                match difference {
                    Difference::Fingerprint => {}
                    Difference::Evidence | Difference::Location | Difference::RelatedLocation => {
                        assert!(findings.contains(&other["finding"]), "{findings:?}")
                    }
                }
            }
        }
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}
