#![feature(rustc_private)]

use shapelint::{Config, Finding, Footer, Kind, SourceInput};

fn findings(text: &str, rule: &str) -> Vec<Finding> {
    let input = SourceInput::try_new("src/api.rs", text).expect("fixture fits in u32");
    shapelint::lint(&input, &Config::default())
        .expect("fixture lints")
        .into_iter()
        .filter(|finding| finding.rule == rule)
        .collect()
}

#[test]
fn conversion_traits_cover_free_and_inherent_conversions_but_not_trait_impls() {
    let text = include_str!("../fixtures/feedback/api/conversions.rs");
    let findings = findings(text, "conversion-trait");
    let highlights: Vec<_> = findings
        .iter()
        .map(|finding| {
            &text[finding.primary.span.start as usize..finding.primary.span.end as usize]
        })
        .collect();
    assert_eq!(
        highlights,
        [
            "from_row",
            "packet_to_frame",
            "as_str",
            "into_message",
            "from_iter"
        ]
    );
    for finding in findings {
        assert_eq!(finding.kind, Kind::Lint);
        assert!(finding.footers.iter().any(|footer| match footer {
            Footer::Help { message } => message.contains("orphan rules"),
            Footer::Note { .. } | Footer::Suggestion { .. } => false,
        }));
    }
}

#[test]
fn parallel_apis_require_a_sibling_in_the_same_module_and_owner() {
    let text = include_str!("../fixtures/feedback/api/parallel.rs");
    let findings = findings(text, "parallel-api");
    let highlights: Vec<_> = findings
        .iter()
        .map(|finding| {
            &text[finding.primary.span.start as usize..finding.primary.span.end as usize]
        })
        .collect();
    assert_eq!(highlights, ["send_one", "send_many", "open_with_options"]);
    for finding in findings {
        assert_eq!(finding.labels.len(), 1);
    }
}

#[test]
fn collection_choice_reports_uses_and_respects_ordering_rationale() {
    let text = include_str!("../fixtures/feedback/api/collections.rs");
    let findings = findings(text, "collection-choice");
    let highlights: Vec<_> = findings
        .iter()
        .map(|finding| {
            &text[finding.primary.span.start as usize..finding.primary.span.end as usize]
        })
        .collect();
    assert_eq!(highlights, ["BTreeMap", "BTreeSet", "BTreeMap"]);
}

#[test]
fn compatibility_lint_labels_the_marked_api_and_what_its_body_calls() {
    let text = include_str!("../fixtures/feedback/api/compatibility.rs");
    let findings = findings(text, "compatibility-scaffolding");
    let highlights: Vec<_> = findings
        .iter()
        .map(|finding| {
            &text[finding.primary.span.start as usize..finding.primary.span.end as usize]
        })
        .collect();
    assert_eq!(
        highlights,
        [
            "old_send",
            "send_compat",
            "old_notify",
            "legacy_checksum",
            "LegacyMessage",
            "alias"
        ]
    );
    let checksum = findings
        .iter()
        .find(|finding| finding.message.contains("legacy_checksum"))
        .unwrap();
    let call = checksum.labels[0].span;
    assert_eq!(
        &text[call.start as usize..call.end as usize],
        "bytes.iter().fold(0, |acc, byte| acc ^ byte)"
    );
    assert!(checksum.footers.iter().any(|footer| match footer {
        Footer::Help { message } => message.contains("distinct behavior"),
        _ => false,
    }));
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum WrittenType {
    Direct,
    Qualified,
    OtherModule,
    Nested,
    SimilarName,
    CommentOnly,
}

#[hegel::test]
fn option_plumbing_matches_written_option_types(tc: hegel::TestCase) {
    let shape = tc.draw(hegel::generators::default::<WrittenType>());
    let (output, expected) = match shape {
        WrittenType::Direct => ("Option < u8 >", 1),
        WrittenType::Qualified => ("std::option::Option<u8>", 1),
        WrittenType::OtherModule => ("wire::Option<u8>", 1),
        WrittenType::Nested => ("Vec<Option<u8>>", 1),
        WrittenType::SimilarName => ("NonOption<u8>", 0),
        WrittenType::CommentOnly => ("Vec</* Option<u8> */ u8>", 0),
    };
    let source = format!("fn encode(value: Option<u8>) -> {output} {{ todo!() }}");
    assert_eq!(findings(&source, "option-plumbing").len(), expected);
}

#[test]
fn shallow_helpers_include_void_forwarders_getters_and_plain_record_factories() {
    let text = include_str!("../fixtures/feedback/api/shallow.rs");
    let findings = findings(text, "shallow-helper");
    let highlights: Vec<_> = findings
        .iter()
        .map(|finding| {
            &text[finding.primary.span.start as usize..finding.primary.span.end as usize]
        })
        .collect();
    assert_eq!(highlights, ["forward", "make", "value"]);
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum ApiOwner {
    SameModule,
    DifferentModule,
    SameType,
    DifferentType,
}

#[hegel::test]
fn parallel_api_pairing_tracks_ownership(tc: hegel::TestCase) {
    let owner = tc.draw(hegel::generators::default::<ApiOwner>());
    let (text, expected) = match owner {
        ApiOwner::SameModule => ("fn send() {} fn send_one() {}", 1),
        ApiOwner::DifferentModule => ("mod a { fn send() {} } mod b { fn send_one() {} }", 0),
        ApiOwner::SameType => ("impl A { fn send() {} } impl A { fn send_one() {} }", 1),
        ApiOwner::DifferentType => ("impl A { fn send() {} } impl B { fn send_one() {} }", 0),
    };
    assert_eq!(findings(text, "parallel-api").len(), expected);
}
