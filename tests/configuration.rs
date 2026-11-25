#![feature(rustc_private)]

use shapelint::{Config, ConfigWarning};

#[hegel::test]
fn exclusions_accumulate_as_literal_paths(tc: hegel::TestCase) {
    let names = tc.draw(hegel::generators::vecs(hegel::generators::integers::<u16>()));
    let paths: Vec<_> = names
        .iter()
        .map(|name| std::path::PathBuf::from(format!("directory {name}/nested")))
        .collect();
    let mut text = String::from("exclude = , fixtures, , # empty entries are ignored\n");
    for path in &paths {
        text.push_str(&format!("exclude = {}\n", path.display()));
    }
    let shapelint::ConfigParse { config, warnings } = Config::parse(&text);
    let expected: Vec<_> = std::iter::once(std::path::PathBuf::from("fixtures"))
        .chain(paths)
        .collect();
    assert_eq!(warnings, []);
    assert_eq!(config.exclude, expected);
}

#[test]
fn thresholds_parse() {
    let shapelint::ConfigParse { config, warnings } =
        Config::parse("shallow-max-nodes = 12\njson-boundary = src/wire, src/bin/ # wire DTOs\n");
    assert_eq!(warnings, []);
    assert_eq!(config.t.shallow_max_nodes, 12);
    assert_eq!(
        config.json_boundary,
        [
            shapelint::PathPattern::Substring("src/wire".into()),
            shapelint::PathPattern::Substring("src/bin/".into()),
        ]
    );
}

#[test]
fn invalid_globs_warn_without_discarding_other_patterns() {
    let shapelint::ConfigParse { config, warnings } = Config::parse(
        "json-boundary = **/tests/**, **/[broken\njson-boundary = , **/*tests*.rs, wire,\n",
    );
    assert_eq!(config.json_boundary.len(), 3);
    let [warning] = warnings.as_slice() else {
        panic!("expected one invalid-pattern warning: {warnings:?}");
    };
    assert_eq!(warning.line, 1);
    assert!(
        warning
            .message
            .contains("invalid `json-boundary` pattern `**/[broken`")
    );
    let input = shapelint::SourceInput::try_new(
        "src/tests/helper.rs",
        "struct Packet { value: serde_json::Value }",
    )
    .expect("fixture");
    assert!(
        shapelint::lint(&input, &config)
            .expect("lint")
            .iter()
            .all(|finding| finding.rule != "json-in-domain")
    );
}

#[test]
fn warnings_name_the_line_and_suggest() {
    let shapelint::ConfigParse { config, warnings } = Config::parse(
        "shallow-max-node = 3\nsource-lines = lots\ndisable = glob-import\njust words\n",
    );
    assert_eq!(config.t.source_lines, 60, "a bad value keeps the default");
    let messages: Vec<String> = warnings
        .iter()
        .map(|ConfigWarning { line, message }| format!("{line}: {message}"))
        .collect();
    insta::assert_snapshot!(messages.join("\n"), @"
    1: unknown key `shallow-max-node`; did you mean `shallow-max-nodes`?
    2: `source-lines` needs a whole number, found `lots`
    3: `disable` is not supported: every rule runs; change a threshold, or add `// shapelint: allow(<rule>)` at the site
    4: expected `key = value`, found `just words`
    ");
}
