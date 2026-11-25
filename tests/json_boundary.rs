#![feature(rustc_private)]

use std::process::Command;

use shapelint::{Config, ConfigParse, SourceInput};

#[derive(Debug, hegel::DefaultGenerator)]
enum PatternCase {
    RecursiveDirectory,
    SingleDirectory,
    Filename,
    QuestionMark,
    CharacterClass,
    Substring,
    CaseSensitive,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct PatternInput {
    directories: Vec<u16>,
    pattern: PatternCase,
}

#[hegel::test]
fn path_patterns_exempt_only_matching_files_from_json_in_domain(tc: hegel::TestCase) {
    let PatternInput {
        directories,
        pattern,
    } = tc.draw(hegel::generators::default::<PatternInput>());
    let prefix: String = directories
        .iter()
        .map(|directory| format!("dir{directory}/"))
        .collect();
    let (pattern, matching, other) = match pattern {
        PatternCase::RecursiveDirectory => ("**/tests/**", "tests/nested/file.rs", "src/file.rs"),
        PatternCase::SingleDirectory => ("**/tests/*.rs", "tests/file.rs", "tests/nested/file.rs"),
        PatternCase::Filename => ("**/*tests*.rs", "client_tests.rs", "client.rs"),
        PatternCase::QuestionMark => ("**/test?.rs", "test1.rs", "test12.rs"),
        PatternCase::CharacterClass => ("**/test[0-9].rs", "test7.rs", "testa.rs"),
        PatternCase::Substring => ("tests", "client_tests.rs", "client.rs"),
        PatternCase::CaseSensitive => ("**/tests/**", "tests/file.rs", "TESTS/file.rs"),
    };
    let ConfigParse { config, warnings } = Config::parse(&format!("json-boundary = {pattern}\n"));
    assert_eq!(warnings, []);
    let text = r#"
use serde_json::{Map, Value};
struct Payload { value: Value, fields: Map<String, Value> }
fn build() -> Value {
    let _ = matches!(Some(1), Some(_));
    assert_eq!(serde_json::json!({}), serde_json::json!({}));
    serde_json::json!({})
}
"#;
    let inputs = [
        SourceInput::try_new(format!("{prefix}{matching}"), text).expect("source fits"),
        SourceInput::try_new(format!("{prefix}{other}"), text).expect("source fits"),
    ];
    let findings = shapelint::lint_sources(&inputs, &config).expect("sources lint");
    let [matching, other] = findings.as_slice() else {
        panic!("expected findings for both files");
    };
    let matching_rules: Vec<_> = matching.iter().map(|finding| finding.rule).collect();
    assert_eq!(matching_rules, ["matches-macro"]);
    let json_spans: Vec<_> = other
        .iter()
        .filter(|finding| finding.rule == "json-in-domain")
        .map(|finding| {
            &text[finding.primary.span.start as usize..finding.primary.span.end as usize]
        })
        .collect();
    assert_eq!(
        json_spans,
        [
            "use serde_json::{Map, Value};",
            "Value",
            "Map<String, Value>",
            "Value",
            "serde_json::json",
            "serde_json::json",
            "serde_json::json",
        ]
    );
}

#[derive(serde::Deserialize)]
struct Finding {
    path: String,
    rule: String,
}

#[test]
fn cli_applies_globs_to_absolute_source_paths_from_a_subdirectory() {
    let project = tempfile::tempdir().expect("create project");
    std::fs::create_dir(project.path().join("tests")).expect("create tests directory");
    std::fs::create_dir(project.path().join("src")).expect("create source directory");
    std::fs::write(
        project.path().join(".shapelint"),
        "json-boundary = **/tests/**\n",
    )
    .expect("write config");
    let source = "use serde_json::Value;\nfn build() { let value = serde_json::json!({}); assert!(matches!(value, Value::Null)); }\n";
    std::fs::write(project.path().join("tests/api.rs"), source).expect("write test source");
    std::fs::write(project.path().join("src/domain.rs"), source).expect("write domain source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(project.path().join("src"))
        .args(["--format", "json", "--exit-zero", ".."])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stderr, b"");
    let findings: Vec<Finding> = serde_json::Deserializer::from_slice(&output.stdout)
        .into_iter::<Finding>()
        .collect::<Result<_, _>>()
        .expect("JSON findings");
    let json_paths: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "json-in-domain")
        .map(|finding| finding.path.as_str())
        .collect();
    assert_eq!(json_paths, ["../src/domain.rs", "../src/domain.rs"]);
    let matches_paths: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "matches-macro")
        .map(|finding| finding.path.as_str())
        .collect();
    assert_eq!(matches_paths, ["../src/domain.rs", "../tests/api.rs"]);
}
