#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Relation {
    SearchPrefix,
    SearchMatch,
    TrimLength,
    DifferentSource,
    ChangedValue,
    LocalIdentity,
    Matches,
    UnrelatedMatchLength,
    DistinctMatches,
    PartitionRange,
    PartitionElement,
    CharacterSearch,
    PartitionPredicate,
    ProjectedPartitionPredicate,
    ProjectedDifferentPredicate,
    DifferentPredicate,
    MutablePredicate,
}

#[hegel::test]
fn string_relations_belong_to_the_value_that_produced_them(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Relation>());
    let source = match case {
        Relation::PartitionPredicate => {
            "pub fn run(values: &[u32], offset: u32) -> u32 { let at = values.partition_point(|&value| value <= offset); if at >= 1 { offset - values[at - 1] } else { offset } }"
        }
        Relation::ProjectedPartitionPredicate => {
            "pub fn run(values: &[u32], offset: u32) -> u32 { let at = values.partition_point(|&value| value <= offset); if at >= 1 { let wrapped = (values[at - 1],); offset - wrapped.0 } else { offset } }"
        }
        Relation::ProjectedDifferentPredicate => {
            "pub fn run(values: &[u32], offset: u32, other: u32) -> u32 { let at = values.partition_point(|&value| value <= other); if at >= 1 { let wrapped = (values[at - 1],); offset - wrapped.0 } else { offset } }"
        }
        Relation::DifferentPredicate => {
            "pub fn run(values: &[u32], offset: u32, other: u32) -> u32 { let at = values.partition_point(|&value| value <= other); if at >= 1 { offset - values[at - 1] } else { offset } }"
        }
        Relation::MutablePredicate => {
            "pub fn run(values: &[u32], offset: u32) -> u32 { let mut limit = offset; let at = values.partition_point(|&value| { limit = limit.wrapping_add(1); value <= limit }); if at >= 1 { offset - values[at - 1] } else { offset } }"
        }
        Relation::Matches => {
            "pub fn run(text: &str, pattern: &str) -> usize { let mut last_len = 0; for (at, matched) in text.match_indices(pattern) { last_len = text[at..at + matched.len()].len(); } last_len }"
        }
        Relation::UnrelatedMatchLength => {
            "pub fn run(text: &str, pattern: &str, other: &str) -> usize { match text.find(pattern) { Some(at) => text[at..at + other.len()].len(), None => 0 } }"
        }
        Relation::DistinctMatches => {
            "pub fn run(text: &str, pattern: &str) -> usize { let mut matches = text.match_indices(pattern); if let (Some((a, _)), Some((b, _))) = (matches.next(), matches.next()) { text[b..a].len() } else { 0 } }"
        }
        Relation::PartitionRange => {
            "pub fn run(values: &[u32], end: u32) -> usize { let at = values.partition_point(|&value| value <= end); values[..at].len() }"
        }
        Relation::PartitionElement => {
            "pub fn run(values: &[u32], end: u32) -> u32 { let at = values.partition_point(|&value| value <= end); values[at] }"
        }
        Relation::CharacterSearch => {
            "pub fn run(text: &str) -> usize { match text.find(')') { Some(at) => text[..at].len(), None => 0 } }"
        }
        Relation::SearchPrefix => {
            "pub fn run(text: &str, pattern: &str) -> usize { match text.find(pattern) { Some(at) => text[..at].len(), None => 0 } }"
        }
        Relation::SearchMatch => {
            "pub fn run(text: &str, pattern: &str) -> usize { match text.find(pattern) { Some(at) => text[at..at + pattern.len()].len(), None => 0 } }"
        }
        Relation::TrimLength => {
            "pub fn run(text: &str) -> usize { text.len() - text.trim_start().len() }"
        }
        Relation::DifferentSource => {
            "pub fn run(text: &str, other: &str, pattern: &str) -> usize { match text.find(pattern) { Some(at) => other[..at].len(), None => 0 } }"
        }
        Relation::ChangedValue => {
            "pub fn run(make: fn() -> String) -> usize { let mut text = make(); let end = text.len(); text.clear(); text[..end].len() }"
        }
        Relation::LocalIdentity => {
            "pub fn run(make: fn() -> String) -> usize { let text = make(); text[..text.len()].len() }"
        }
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    match case {
        Relation::PartitionPredicate
        | Relation::ProjectedPartitionPredicate
        | Relation::Matches
        | Relation::PartitionRange
        | Relation::CharacterSearch
        | Relation::SearchPrefix
        | Relation::SearchMatch
        | Relation::TrimLength
        | Relation::LocalIdentity => assert!(findings.is_empty(), "{case:?}: {output}"),
        Relation::DifferentPredicate
        | Relation::ProjectedDifferentPredicate
        | Relation::MutablePredicate
        | Relation::DistinctMatches
        | Relation::UnrelatedMatchLength
        | Relation::PartitionElement
        | Relation::DifferentSource
        | Relation::ChangedValue => {
            assert!(!findings.is_empty(), "{case:?}: {output}")
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum LexerOffset {
    Exact,
    SkipsByte,
    OtherSource,
    ResetOffset,
    WrongInitialOffset,
}

#[hegel::test]
fn lexer_progress_tracks_the_partition_and_rejects_incorrect_offsets(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<LexerOffset>());
    struct Offset {
        update: &'static str,
        source: &'static str,
        initial: u32,
        advance: &'static str,
    }
    let Offset {
        update,
        source,
        initial,
        advance,
    } = match case {
        LexerOffset::Exact => Offset {
            update: "token.len",
            source: "text",
            initial: 0,
            advance: "end",
        },
        LexerOffset::SkipsByte => Offset {
            update: "token.len + 1",
            source: "text",
            initial: 0,
            advance: "end",
        },
        LexerOffset::OtherSource => Offset {
            update: "token.len",
            source: "other",
            initial: 0,
            advance: "end",
        },
        LexerOffset::ResetOffset => Offset {
            update: "token.len",
            source: "text",
            initial: 0,
            advance: "0",
        },
        LexerOffset::WrongInitialOffset => Offset {
            update: "token.len",
            source: "text",
            initial: 1,
            advance: "end",
        },
    };
    let source = format!(
        "#![feature(rustc_private)] extern crate rustc_lexer; pub fn run(text: &str, other: &str) -> usize {{ let _ = other; if text.len() > u32::MAX as usize {{ return 0; }} let mut offset = {initial}u32; let mut last_len = 0; for token in rustc_lexer::tokenize(text, rustc_lexer::FrontmatterAllowed::No) {{ let end = offset + {update}; last_len = {source}[offset as usize..end as usize].len(); offset = {advance}; }} last_len }}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    match case {
        LexerOffset::Exact => assert!(findings.is_empty(), "{output}"),
        LexerOffset::SkipsByte
        | LexerOffset::OtherSource
        | LexerOffset::ResetOffset
        | LexerOffset::WrongInitialOffset => {
            assert!(!findings.is_empty(), "{output}")
        }
    }
}
