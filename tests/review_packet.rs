#![feature(rustc_private)]

//! Each annotated review comment (C01–C27) that a syntax rule can reach must fire on
//! fixtures rebuilt from the packet's excerpts; C01, C02 and C08 are out of reach.

use std::process::Command;

#[derive(serde::Deserialize)]
struct Finding {
    rule: String,
    path: String,
    item: String,
}

const EXPECTED: &[(&str, &str, &str, &str)] = &[
    (
        "C03",
        "code/kafka/src/bin/topics.rs",
        "config-bag",
        "ConnectorConfig::topics",
    ),
    (
        "C04",
        "code/kafka/src/bin/topics.rs",
        "config-bag",
        "ConnectorConfig::property",
    ),
    (
        "C05",
        "code/kafka/src/bin/topics.rs",
        "check-passthrough",
        "validate_connector_topics",
    ),
    (
        "C06",
        "schema/topics.toml",
        "duration-comment",
        "retention.ms",
    ),
    ("C07", "code/cdc-worker/BUCK", "mapped-srcs", "mapped_srcs"),
    (
        "C09",
        "code/cdc-worker/src/assembly.rs",
        "identity-string",
        "handle_batch",
    ),
    (
        "C10",
        "code/cdc-worker/src/assembly.rs",
        "blocking-rationale",
        "fn open",
    ),
    (
        "C11",
        "code/cdc-worker/src/audit.rs",
        "json-in-domain",
        "use serde_json",
    ),
    (
        "C12",
        "code/cdc-worker/src/audit.rs",
        "json-in-domain",
        "Stamp.provenance",
    ),
    (
        "C13",
        "code/cdc-worker/src/audit.rs",
        "optional-state",
        "impl Assembler",
    ),
    (
        "C14",
        "code/cdc-worker/src/audit.rs",
        "unit-fields",
        "LogicalTime",
    ),
    (
        "C15",
        "code/cdc-worker/src/audit.rs",
        "shallow-helper",
        "low_xid",
    ),
    (
        "C16",
        "code/cdc-worker/src/audit.rs",
        "check-passthrough",
        "row_images",
    ),
    (
        "C17",
        "code/cdc-worker/src/audit.rs",
        "option-plumbing",
        "keyed_images",
    ),
    (
        "C18",
        "code/cdc-worker/src/audit.rs",
        "option-plumbing",
        "fn project",
    ),
    (
        "C19",
        "code/cdc-worker/src/audit.rs",
        "option-plumbing",
        "changed_fields",
    ),
    (
        "C20",
        "code/cdc-worker/src/audit.rs",
        "json-in-domain",
        "normalize_value",
    ),
    (
        "C21",
        "code/cdc-worker/src/audit.rs",
        "shallow-helper",
        "value_at",
    ),
    (
        "C22",
        "code/cdc-worker/src/messages/audit_events/tests.rs",
        "shallow-helper",
        "fn id",
    ),
    (
        "C23",
        "code/cdc-worker/src/messages/audit_events/tests.rs",
        "json-in-domain",
        "fn provenance",
    ),
    (
        "C24",
        "code/cdc-worker/src/messages/audit_events/tests.rs",
        "json-in-domain",
        "row_message",
    ),
    (
        "C25",
        "code/cdc-worker/src/messages/audit_events.rs",
        "check-passthrough",
        "validate_provenance",
    ),
    (
        "C26",
        "code/cdc-worker/src/messages/audit_events.rs",
        "check-passthrough",
        "validate_row_shape",
    ),
    (
        "C27",
        "code/core/tests/src/audit_recovery.rs",
        "byte-format",
        "assert_trusted_issuer_event",
    ),
];

/// Negatives from the packet: things a rule must not flag.
const MUST_NOT: &[(&str, &str, &str)] = &[
    (
        "code/cdc-worker/src/audit.rs",
        "shallow-helper",
        "serialize_xid8",
    ), // named in a serde attribute
    (
        "code/cdc-worker/src/audit.rs",
        "shallow-helper",
        "operation_name",
    ), // has a match
    (
        "code/core/tests/src/audit_recovery.rs",
        "check-passthrough",
        "assert_trusted_issuer_event",
    ), // test assertion
    ("third-party/rust/Cargo.toml", "duration-comment", ""), // C01: nothing syntactic to say
];

#[test]
fn review_packet() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/fixtures/review-packet");
    let cwd = tempfile::tempdir().expect("create isolated configuration directory");
    std::fs::write(cwd.path().join(".shapelint"), "").expect("write test configuration");
    let out = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(cwd.path())
        .args(["--format", "json", dir])
        .output()
        .unwrap();
    let findings: Vec<Finding> = String::from_utf8(out.stdout)
        .unwrap()
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    let hit = |path: &str, rule: &str, item: &str| {
        findings
            .iter()
            .any(|f| f.path == format!("{dir}/{path}") && f.rule == rule && f.item.contains(item))
    };
    let missing: Vec<_> = EXPECTED
        .iter()
        .filter(|(_, p, r, i)| !hit(p, r, i))
        .map(|(c, ..)| *c)
        .collect();
    assert!(missing.is_empty(), "cases not flagged: {missing:?}");
    let wrong: Vec<_> = MUST_NOT.iter().filter(|(p, r, i)| hit(p, r, i)).collect();
    assert!(wrong.is_empty(), "negatives flagged: {wrong:?}");
}
