#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Source {
    Selection,
    Test,
    NegatedTest,
    DoubleNegatedTest,
    Returned,
    Indirect,
    CallerArgument,
    MutualRecursion,
}

#[hegel::test(print_blob = true)]
fn resolved_values_keep_the_incoming_fact_that_selected_them(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Source>());
    let (helpers, expression, check) = match case {
        Source::Selection => (
            "",
            "if choose { 1u8 } else { 2u8 }",
            "if result == 1 { 3 } else { 4 }",
        ),
        Source::Test => ("", "choose", "if result { 3 } else { 4 }"),
        Source::NegatedTest => ("", "!choose", "if !result { 3 } else { 4 }"),
        Source::DoubleNegatedTest => ("", "!!choose", "if !!result { 3 } else { 4 }"),
        Source::Returned => (
            "fn helper(choose:bool)->u8 { if choose { 1 } else { 2 } }",
            "helper(choose)",
            "if result == 1 { 3 } else { 4 }",
        ),
        Source::Indirect => (
            "fn first()->u8 { 1 } fn second()->u8 { 2 }",
            "{ let callback:fn()->u8=if choose { first } else { second }; callback() }",
            "if result == 1 { 3 } else { 4 }",
        ),
        Source::CallerArgument => (
            "fn helper(value:bool)->u8 { if value { 3 } else { 4 } }",
            "if choose { true } else { false }",
            "helper(result)",
        ),
        Source::MutualRecursion => (
            "fn helper(done:bool)->u8 { if done { 1 } else { other(done) } } fn other(done:bool)->u8 { if done { 1 } else { helper(done) } }",
            "helper(choose)",
            "if result == 1 { 3 } else { 4 }",
        ),
    };
    let source = format!(
        "{helpers}\npub fn run(choose:bool)->u8 {{\n    if !choose {{ return 0; }}\n    let result = {expression};\n    {check}\n}}\n"
    );
    let output = support::analyze(&source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "redundant-check" && finding["item"] == "run" && finding["line"] == 5
        })
        .collect();
    let [finding] = findings.as_slice() else {
        panic!("one final check with incoming evidence for {case:?}: {output}");
    };
    assert!(
        finding["primary"]["message"]
            .as_str()
            .expect("outcome")
            .contains("always true"),
        "{output}"
    );
    let notes = finding["footers"].as_array().expect("evidence");
    let evidence = notes
        .iter()
        .find_map(|footer| {
            let message = footer["message"].as_str().expect("footer");
            match message.strip_prefix("Established before this check: ") {
                Some(facts) => Some(facts),
                None => message
                    .strip_prefix("Recursive return and control-flow analysis, together with ")
                    .or_else(|| {
                        message
                            .split_once("Earlier control flow selected values using ")
                            .map(|(_, facts)| facts)
                    }),
            }
        })
        .expect("the decision uses incoming facts, not only known values");
    assert!(evidence.contains("choose"), "{case:?}: {output}");
}

#[test]
fn internal_return_path_assumptions_do_not_escape_as_caller_evidence() {
    let source = r#"
fn helper(a:usize,b:usize)->u8 {
    if a < b { 1 } else { 1 }
}
pub fn run(a:usize,b:usize)->u8 {
    let result = helper(a,b);
    if result == 1 { 3 } else { 4 }
}
"#;
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "redundant-check" && finding["item"] == "run" && finding["line"] == 7
        })
        .collect();
    let [finding] = findings.as_slice() else {
        panic!("one unconditional return-value proof: {output}");
    };
    let evidence = finding["footers"]
        .as_array()
        .expect("evidence")
        .iter()
        .find(|footer| {
            footer["message"]
                .as_str()
                .expect("footer")
                .starts_with("Known values imply")
        });
    let Some(_) = evidence else {
        panic!("{output}");
    };
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum SelectedEdge {
    True,
    False,
}

#[hegel::test(print_blob = true)]
fn earlier_selection_facts_survive_mutation_without_becoming_current_facts(tc: hegel::TestCase) {
    let edge = tc.draw(hegel::generators::default::<SelectedEdge>());
    let (exit, selection, replacement) = match edge {
        SelectedEdge::True => ("!choose", "choose", "false"),
        SelectedEdge::False => ("choose", "!choose", "true"),
    };
    let source = format!(
        "pub fn run(mut choose:bool, unrelated:bool)->u8 {{\n    if {exit} {{ return 0; }}\n    if !unrelated {{ return 0; }}\n    let result = if {selection} {{ 1u8 }} else {{ 2u8 }};\n    choose = {replacement};\n    std::hint::black_box(choose);\n    if result == 1 {{ 3 }} else {{ 4 }}\n}}\n"
    );
    let output = support::analyze(&source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "redundant-check" && finding["item"] == "run" && finding["line"] == 7
        })
        .collect();
    let [finding] = findings.as_slice() else {
        panic!("one final selected-value check for {edge:?}: {output}");
    };
    assert!(
        finding["primary"]["message"]
            .as_str()
            .expect("outcome")
            .contains("always true"),
        "{output}"
    );
    let historical = finding["footers"]
        .as_array()
        .expect("evidence")
        .iter()
        .find_map(|footer| {
            footer["message"]
                .as_str()
                .expect("footer")
                .split_once("Earlier control flow selected values using ")
                .map(|(_, facts)| facts)
        })
        .expect("selection evidence remains explicitly historical after mutation");
    assert!(historical.contains("choose"), "{output}");
    assert!(
        !historical.contains("unrelated"),
        "unused incoming guard escaped into evidence: {output}"
    );
    let footers = finding["footers"].as_array().expect("evidence");
    for footer in footers {
        let message = footer["message"].as_str().expect("footer");
        if let Some(current) = message.strip_prefix("Established before this check: ") {
            let current = current
                .split("Earlier control flow")
                .next()
                .expect("current evidence");
            assert!(
                !current.contains("choose"),
                "historical fact claimed as current: {output}"
            );
        }
    }
}

#[test]
fn joined_selected_edges_do_not_claim_opposite_facts_together() {
    let source = "pub fn run(choose:bool)->u8 {\n    let result;\n    if choose {\n        result = if choose { 1u8 } else { 2u8 };\n    } else {\n        result = if choose { 2u8 } else { 1u8 };\n    }\n    if result == 1 { 3 } else { 4 }\n}\n";
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "redundant-check" && finding["item"] == "run" && finding["line"] == 8
        })
        .collect();
    let [finding] = findings.as_slice() else {
        panic!("one final check after both selected paths: {output}");
    };
    assert!(
        finding["primary"]["message"]
            .as_str()
            .expect("outcome")
            .contains("always true"),
        "{output}"
    );
    let footers = finding["footers"].as_array().expect("evidence");
    for footer in footers {
        let message = footer["message"].as_str().expect("footer");
        assert!(
            !message.contains("choose"),
            "path-specific fact escaped the join: {output}"
        );
    }
}

#[test]
fn imported_selections_keep_historical_evidence_in_caller_names() {
    let directory = tempfile::tempdir().expect("source directory");
    let producer = directory.path().join("dependency.rs");
    let metadata = directory.path().join("libdependency.rmeta");
    let summary = directory.path().join("dependency.summary.json");
    std::fs::write(&producer, "macro_rules! selected { ($flag:expr) => { if $flag { 1u8 } else { 2u8 } }; }\npub fn select(flag:bool, expected:u8)->u8 { assert!(flag); let value = selected!(flag); if value == expected { 3 } else { 4 } }\n").expect("producer source");
    let produced = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
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
        .arg(&producer)
        .output()
        .expect("producer analysis");
    assert!(
        produced.status.success(),
        "{}",
        String::from_utf8_lossy(&produced.stderr)
    );
    let producer_output = String::from_utf8(produced.stdout).expect("producer diagnostics");
    let producer_check = producer_output
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("producer finding"))
        .find(|finding| finding["rule"] == "redundant-check");
    assert_eq!(
        producer_check, None,
        "the caller's expected value is required to prove the check: {producer_output}"
    );
    let consumer = directory.path().join("consumer.rs");
    std::fs::write(
        &consumer,
        "pub fn run(choose:bool)->u8 { if !choose { return 0; } dependency::select(choose, 1) }\n",
    )
    .expect("consumer source");
    let consumed = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-type=lib",
            "--crate-name=consumer",
            "--edition=2024",
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
        .expect("consumer analysis");
    assert!(
        consumed.status.success(),
        "{}",
        String::from_utf8_lossy(&consumed.stderr)
    );
    let output = String::from_utf8(consumed.stdout).expect("diagnostics");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "redundant-check" && finding["item"] == "run"
        })
        .collect();
    let [finding] = findings.as_slice() else {
        panic!("one imported selected-value check in the consumer: {output}");
    };
    assert!(
        finding["primary"]["message"]
            .as_str()
            .expect("outcome")
            .contains("always true"),
        "{output}"
    );
    let historical = finding["footers"]
        .as_array()
        .expect("evidence")
        .iter()
        .find_map(|footer| {
            footer["message"]
                .as_str()
                .expect("footer")
                .split_once("Earlier control flow selected values using ")
                .map(|(_, facts)| facts)
        })
        .expect("imported selected value retains its historical evidence");
    assert!(historical.contains("choose"), "{output}");
    assert!(
        !historical.contains("flag"),
        "producer names escaped caller substitution: {output}"
    );
}
