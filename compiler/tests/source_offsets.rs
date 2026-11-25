#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Encoding {
    Lf,
    CrLf,
    BomLf,
    BomCrLf,
}

#[hegel::test]
fn ast_and_hir_labels_use_original_source_bytes(tc: hegel::TestCase) {
    let encoding = tc.draw(hegel::generators::default::<Encoding>());
    let text = "// λ: source offsets include Unicode\npub struct State { pub ready: bool }\npub fn present(value: Option<u8>) -> u8 { if value.is_some() { value.unwrap() } else { 0 } }\n";
    let source = match encoding {
        Encoding::Lf => text.to_owned(),
        Encoding::CrLf => text.replace('\n', "\r\n"),
        Encoding::BomLf => format!("\u{feff}{text}"),
        Encoding::BomCrLf => format!("\u{feff}{}", text.replace('\n', "\r\n")),
    };
    let findings: Vec<serde_json::Value> = support::analyze(&source, &[])
        .expect("driver analysis")
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let hir = findings
        .iter()
        .find(|finding| finding["rule"] == "option-result-predicate")
        .expect("HIR finding");
    let start = hir["primary"]["span"]["start"].as_u64().expect("start") as usize;
    let end = hir["primary"]["span"]["end"].as_u64().expect("end") as usize;
    assert_eq!(&source[start..end], "is_some");
    let ast = findings
        .iter()
        .find(|finding| finding["rule"] == "boolean-state")
        .expect("AST finding");
    let start = ast["primary"]["span"]["start"].as_u64().expect("start") as usize;
    let end = ast["primary"]["span"]["end"].as_u64().expect("end") as usize;
    assert_eq!(&source[start..end], "bool");
    let input = shapelint::SourceInput::try_new("src/lib.rs", source).expect("fixture");
    let findings = shapelint::lint(&input, &shapelint::Config::default()).expect("source lint");
    let expected = findings
        .iter()
        .find(|finding| finding.rule == "boolean-state")
        .expect("AST finding");
    assert_eq!(
        ast["primary"],
        serde_json::to_value(&expected.primary).expect("label")
    );
}
