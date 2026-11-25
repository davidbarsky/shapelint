#![feature(rustc_private)]

use std::error::Error;
use std::fs;
use std::process::Command;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Encoding {
    Lf,
    CrLf,
    BomLf,
    BomCrLf,
}

#[hegel::test]
fn duplicate_regions_show_both_sources_in_one_diagnostic(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let encoding = tc.draw(hegel::generators::default::<Encoding>());
        let directory = tempfile::tempdir()?;
        let first = directory.path().join("first.rs");
        let second = directory.path().join("second.rs");
        let entry = directory.path().join("lib.rs");
        let text = "// λ precedes the region\npub fn run(flag: bool, a: fn(), b: fn(), setup: fn()) {\n    setup();\n    if flag { a(); } else { b(); }\n}\n";
        let source = match encoding {
            Encoding::Lf => text.to_owned(),
            Encoding::CrLf => text.replace('\n', "\r\n"),
            Encoding::BomLf => format!("\u{feff}{text}"),
            Encoding::BomCrLf => format!("\u{feff}{}", text.replace('\n', "\r\n")),
        };
        fs::write(&first, &source)?;
        fs::write(&second, source.replace("setup();", "setup(); setup();"))?;
        fs::write(&entry, "pub mod first; pub mod second;")?;
        let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .env("SHAPELINT_CARGO_COLOR", "never")
            .args(["--format=record", "--crate-type=lib"])
            .arg(&entry)
            .output()?;
        assert!(output.status.success(), "{output:?}");
        assert!(output.stderr.is_empty(), "{output:?}");
        let mut records: Vec<serde_json::Value> = String::from_utf8(output.stdout)?
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

        let records: Vec<_> = records
            .iter()
            .filter(|record| record["finding"]["rule"] == "duplicate-control-flow")
            .collect();
        assert_eq!(records.len(), 1, "{records:?}");
        let record = records[0];
        let related = record["finding"]["related"]
            .as_array()
            .ok_or("missing related snippets")?;
        assert_eq!(related.len(), 1);
        let related = &related[0];
        assert_eq!(related["input"]["name"], first.to_str().ok_or("path")?);
        assert_eq!(related["input"]["text"], source);
        let start = related["label"]["span"]["start"].as_u64().ok_or("start")? as usize;
        let end = related["label"]["span"]["end"].as_u64().ok_or("end")? as usize;
        assert_eq!(&source[start..end], "if flag { a(); } else { b(); }");
        let rendered = record["rendered"].as_str().ok_or("rendered diagnostic")?;
        assert_eq!(
            rendered.matches("lint[duplicate-control-flow]").count(),
            1,
            "{rendered}"
        );
        assert_eq!(
            rendered.matches("if flag { a(); } else { b(); }").count(),
            2,
            "{rendered}"
        );
        assert!(
            rendered.find("first.rs").ok_or("first snippet")?
                < rendered.find("second.rs").ok_or("second snippet")?,
            "{rendered}"
        );
        assert!(
            rendered.contains("implementation in `first::run`"),
            "{rendered}"
        );
        assert!(
            rendered.contains("appears to duplicate the implementation above"),
            "{rendered}"
        );
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}
