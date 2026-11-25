#![feature(rustc_private)]

use std::error::Error;
use std::fs;
use std::process::Command;

use shapelint::{Config, SourceInput, lint_sources};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Source {
    Struct,
    Function,
    Macro,
    Suppressed,
}

#[hegel::test]
fn syntax_rules_share_the_library_implementation_across_modules(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let source = tc.draw(hegel::generators::default::<Source>());
        let model = match source {
            Source::Struct => "pub struct State { pub ready: bool }",
            Source::Function => "pub fn identity(value: u8) -> u8 { value }",
            Source::Macro => {
                "pub fn present(value: Option<u8>) -> bool { matches!(value, Some(_)) }"
            }
            Source::Suppressed => {
                "// shapelint: allow(boolean-state)\npub struct State { pub ready: bool }"
            }
        };
        let directory = tempfile::tempdir()?;
        let source_directory = directory.path().join("src");
        fs::create_dir(&source_directory)?;
        let files = [
            (
                "lib.rs",
                "pub mod model; pub mod declarations; pub mod implementation; include!(\"included.rs\"); pub const FIXTURE: &str = include_str!(\"fixture.rs\");",
            ),
            ("model.rs", model),
            ("included.rs", "pub struct Included { pub ready: bool }"),
            (
                "declarations.rs",
                "pub trait Read { fn read(&self) -> u8; } pub struct Value;",
            ),
            (
                "implementation.rs",
                "impl crate::declarations::Read for crate::declarations::Value { fn read(&self) -> u8 { 1 } }",
            ),
        ];
        let mut inputs = Vec::new();
        for (name, text) in files {
            let path = source_directory.join(name);
            fs::write(&path, text)?;
            inputs.push(SourceInput::try_new(path.display().to_string(), text)?);
        }
        fs::write(
            source_directory.join("fixture.rs"),
            "pub struct Ignored { pub ready: bool }",
        )?;
        let mut expected: Vec<_> = lint_sources(&inputs, &Config::default())?
            .into_iter()
            .flatten()
            .map(|finding| serde_json::to_string(&finding))
            .collect::<Result<_, _>>()?;
        assert!(
            expected
                .iter()
                .any(|finding| finding.contains("single-impl-trait")),
            "{expected:?}"
        );
        let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .args(["--format=json", "--crate-type=lib", "--edition=2024"])
            .arg(source_directory.join("lib.rs"))
            .output()?;
        assert!(output.status.success(), "{:?}", output);
        assert!(output.stderr.is_empty(), "{:?}", output);
        let mut actual: Vec<_> = String::from_utf8(output.stdout)?
            .lines()
            .map(str::to_owned)
            .collect();
        expected.sort();
        actual.sort();
        assert_eq!(actual, expected, "{source:?}");
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}
