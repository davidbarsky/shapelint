#![feature(rustc_private)]

mod support;

// shapelint: allow(literal-test-cases) Geometric sizes exercise repeated guard exclusion through the production driver.
#[test]
fn other_returned_guards_preserve_the_validation() {
    for count in [8, 16, 32] {
        let mut source = String::from(
            "fn validate_0(index: usize, len: usize) { if index >= len { panic!() } }\n",
        );
        for index in 1..count {
            source.push_str(&format!(
                "fn validate_{index}(index: usize, len: usize) {{ if index >= len {{ panic!() }} }}\n"
            ));
        }
        source.push_str("pub fn read(values: &[u8], index: usize) -> u8 {\n");
        for index in 0..count {
            source.push_str(&format!("    validate_{index}(index, values.len());\n"));
        }
        source.push_str("    if index < values.len() { values[index] } else { 0 }\n}\n");

        let output = support::analyze(&source, &[]).expect("analysis");
        let discarded = output
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("finding"))
            .filter(|finding| finding["rule"] == "discarded-validation")
            .count();
        assert_eq!(
            discarded, 0,
            "a remaining returned guard proves the validation for {count} guards: {output}"
        );
    }
}

#[test]
fn repeated_validation_retains_the_other_occurrence() {
    let output = support::analyze(
        "fn validate(index: usize, len: usize) { if index >= len { panic!() } }\n\
         pub fn read(values: &[u8], index: usize) -> u8 {\n\
             validate(index, values.len());\n\
             validate(index, values.len());\n\
             if index < values.len() { values[index] } else { 0 }\n\
         }",
        &[],
    )
    .expect("analysis");
    #[derive(serde::Deserialize)]
    struct Finding {
        rule: String,
    }
    let findings: Vec<Finding> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    assert!(
        findings
            .iter()
            .all(|finding| finding.rule != "discarded-validation"),
        "{output}"
    );
}
