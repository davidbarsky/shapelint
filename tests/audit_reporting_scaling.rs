#![feature(rustc_private)]

use shapelint::{Config, SourceInput, lint};

// shapelint: allow(literal-test-cases) This fixed geometric family is the measured scaling gate.
#[test]
fn adjacent_suppression_comments_cover_the_following_item() {
    for size in [8, 16, 32] {
        let source = format!(
            "{}fn run(xs: &[u8]) {{ xs.iter().for_each(|_| ()); }}\n",
            "// shapelint: allow(for-chain)\n".repeat(size),
        );
        let input = SourceInput::try_new(format!("comment-block-{size}.rs"), source).unwrap();
        let findings = lint(&input, &Config::default()).unwrap();
        assert!(findings.iter().all(|finding| finding.rule != "for-chain"));
    }
}

// shapelint: allow(literal-test-cases) This fixed geometric family is the measured scaling gate.
#[test]
fn enclosing_items_keep_findings_in_their_own_functions() {
    for size in [8, 16, 32] {
        let source: String = (0..size)
            .map(|index| format!("fn f{index}(xs: &[u8]) {{ xs.iter().for_each(|_| ()); }}\n"))
            .collect();
        let input = SourceInput::try_new(format!("enclosing-{size}.rs"), source).unwrap();
        let findings = lint(&input, &Config::default()).unwrap();
        let findings: Vec<_> = findings
            .iter()
            .filter(|finding| finding.rule == "for-chain")
            .collect();
        assert_eq!(findings.len(), size);
        for index in 0..findings.len() {
            assert_eq!(findings[index].item, format!("fn f{index}"));
        }
        eprintln!("AUDIT enclosing size={size} findings={}", findings.len());
    }
}

// shapelint: allow(literal-test-cases) This fixed geometric family is the measured scaling gate.
#[test]
fn repeated_findings_keep_distinct_fingerprints_within_one_item() {
    for size in [8, 16, 32] {
        let mut source = String::from("fn run(xs: &[u8]) {\n");
        source.push_str(&"xs.iter().for_each(|_| ());\n".repeat(size));
        source.push_str("}\n");
        let input = SourceInput::try_new(format!("fingerprints-{size}.rs"), source).unwrap();
        let findings = lint(&input, &Config::default()).unwrap();
        let findings: Vec<_> = findings
            .iter()
            .filter(|finding| finding.rule == "for-chain")
            .collect();
        assert_eq!(findings.len(), size);
        let fingerprints: std::collections::HashSet<_> = findings
            .iter()
            .map(|finding| &finding.fingerprint)
            .collect();
        assert_eq!(fingerprints.len(), size);
        assert!(
            findings
                .iter()
                .all(|finding| finding.fingerprint.starts_with("v2:"))
        );
        eprintln!("AUDIT fingerprints size={size} findings={}", findings.len());
    }
}

#[test]
fn v2_fingerprint_ignores_item_relocation() {
    let plain = SourceInput::try_new(
        "relocation.rs",
        "fn run(xs: &[u8]) { xs.iter().for_each(|_| ()); }\n",
    )
    .unwrap();
    let moved = SourceInput::try_new(
        "relocation.rs",
        "// moved\nfn run(xs: &[u8]) { xs.iter().for_each(|_| ()); }\n",
    )
    .unwrap();
    let first = lint(&plain, &Config::default())
        .unwrap()
        .into_iter()
        .find(|finding| finding.rule == "for-chain")
        .expect("plain finding");
    let second = lint(&moved, &Config::default())
        .unwrap()
        .into_iter()
        .find(|finding| finding.rule == "for-chain")
        .expect("relocated finding");
    assert_eq!(first.fingerprint, second.fingerprint);
    assert_ne!(first.line, second.line);
}

// shapelint: allow(literal-test-cases) This fixed geometric family is the measured scaling gate.
#[test]
fn unrelated_suppressions_do_not_hide_findings() {
    for size in [8, 16, 32] {
        let mut source = String::new();
        for index in 0..size {
            source.push_str(&format!(
                "// shapelint: allow(for-chain)\nconst C{index}: u8 = 0;\n"
            ));
        }
        for index in 0..size {
            source.push_str(&format!(
                "fn f{index}(xs: &[u8]) {{ xs.iter().for_each(|_| ()); }}\n"
            ));
        }
        let input = SourceInput::try_new(format!("suppressions-{size}.rs"), source).unwrap();
        let findings = lint(&input, &Config::default()).unwrap();
        let count = findings
            .iter()
            .filter(|finding| finding.rule == "for-chain")
            .count();
        assert_eq!(count, size);
        eprintln!("AUDIT suppressions size={size} findings={count}");
    }
}

#[test]
fn suppression_index_matches_the_directive_oracle() {
    let mut source = String::new();
    for index in 0..32 {
        if index % 2 == 0 {
            source.push_str("// shapelint: allow(for-chain)\n");
        }
        source.push_str(&format!(
            "fn f{index}(xs: &[u8]) {{ xs.iter().for_each(|_| ()); }}\n"
        ));
    }
    let input = SourceInput::try_new("suppression-oracle.rs", source).unwrap();
    let findings = lint(&input, &Config::default()).unwrap();
    let names: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "for-chain")
        .map(|finding| finding.item.as_str())
        .collect();
    let expected: Vec<_> = (0..32)
        .filter(|index| index % 2 == 1)
        .map(|index| format!("fn f{index}"))
        .collect();
    assert_eq!(
        names,
        expected.iter().map(String::as_str).collect::<Vec<_>>()
    );
}
