use std::{
    collections::{BTreeSet, HashMap},
    sync::Arc,
};

use base64::Engine as _;
use jiff::Timestamp;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use uuid::Uuid;

use crate::{
    messages::audit_events::{self, Operation, RowChange, TransactionMetadata},
    protos::ersc::{audit::v1::AuditEvent, cdc::v1 as cdc_pb},
    tables,
    translate::TranslateError,
};

const COVERAGE: &str = include_str!("../../../schema/audit-policy.json");
const PROVENANCE_PREFIX: &str = "ersc.audit.provenance";
const MARKER_PREFIX: &str = "ersc.audit.marker";

#[derive(Clone, Debug, Deserialize, Serialize)] // [reconstructed]
pub struct Stamp {
    pub id: Uuid,
    #[serde(
        deserialize_with = "deserialize_xid8",
        serialize_with = "serialize_xid8"
    )]
    pub xid8: u64,
    pub lsn: u64,
    pub provenance: Map<String, Value>,
}

/// Returns one assembled audit mutation and the raw product table to republish.
#[derive(Debug)]
pub struct Assembled {
    pub mutation: Option<cdc_pb::Mutation>,
    pub product_table: Option<&'static str>,
}

/// Assembles rows and audit logical messages from one ordered source partition.
#[derive(Clone)]
pub struct Assembler {
    pub stamp: Option<Stamp>,
    coverage: Arc<Coverage>,
}

impl Assembler {
    /// Uses the capture policy derived from the SQL schema.
    pub fn new(stamp: Option<Stamp>) -> Result<Self, AuditError> {
        let mut coverage: Coverage = serde_json::from_str(COVERAGE)?;
        for (name, policy) in &mut coverage.tables {
            if policy.target_kind.is_empty() {
                policy.target_kind = name.clone();
            }
        }
        if coverage.version != 1 || coverage.message_prefix != audit_events::PREFIX {
            return Err(AuditError::Invalid("unsupported audit capture policy"));
        }
        Ok(Assembler { stamp, coverage: Arc::new(coverage) }) // [reconstructed]
    }

    // [reconstructed] from the packet's description: "require_stamp() dynamically proves
    // stamp presence and transaction/LSN compatibility".
    fn require_stamp(&self, xid: u64, lsn: u64) -> Result<&Stamp, AuditError> {
        let Some(stamp) = self.stamp.as_ref() else {
            return Err(AuditError::Invalid("row has no stamp"));
        };
        if low_xid(stamp.xid8) != low_xid(xid) || stamp.lsn > lsn {
            return Err(AuditError::Invalid("stamp does not cover row"));
        }
        Ok(stamp)
    }
}

#[derive(Debug, Deserialize)]
struct LogicalTime {
    ts_ms: i64,
    ts_us: Option<i64>,
    ts_ns: Option<i64>,
}

impl LogicalTime {
    fn nanoseconds(&self) -> Result<i64, AuditError> {
        self.ts_ns
            .or_else(|| self.ts_us.and_then(|value| value.checked_mul(1_000)))
            .or_else(|| self.ts_ms.checked_mul(1_000_000))
            .ok_or(AuditError::Invalid("logical timestamp overflow"))
    }
}

fn serialize_xid8<S>(value: &u64, serializer: S) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    serializer.serialize_str(&value.to_string())
}

fn low_xid(value: u64) -> u64 {
    value & u64::from(u32::MAX)
}

fn parse_operation(operation: &str) -> Result<Operation, AuditError> {
    match operation {
        "c" => Ok(Operation::Insert),
        "u" => Ok(Operation::Update),
        "d" => Ok(Operation::Delete),
        _ => Err(AuditError::Invalid("ordinary row has unknown operation")),
    }
}

fn operation_name(operation: Operation) -> &'static str {
    match operation {
        Operation::Insert => "insert",
        Operation::Update => "update",
        Operation::Delete => "delete",
    }
}

fn row_images(
    operation: Operation,
    before: Option<Map<String, Value>>,
    after: Option<Map<String, Value>>,
) -> Result<(Option<Map<String, Value>>, Option<Map<String, Value>>), AuditError> {
    match (operation, &before, &after) {
        (Operation::Insert, None, Some(_))
        | (Operation::Update, Some(_), Some(_))
        | (Operation::Delete, Some(_), None) => Ok((before, after)),
        _ => Err(AuditError::Invalid("ordinary row has invalid images")),
    }
}

fn keyed_images(
    table: &str,
    policy: &TablePolicy,
    key: &Map<String, Value>,
    before: Option<Map<String, Value>>,
    after: Option<Map<String, Value>>,
) -> Result<(Option<Map<String, Value>>, Option<Map<String, Value>>), AuditError> {
    let Some(image) = after.as_ref().or(before.as_ref()) else {
        return Err(AuditError::Invalid("ordinary row has no key image"));
    };
    if key.len() != policy.key_fields.len() {
        return Err(AuditError::Invalid(
            "record key differs from the configured key fields",
        ));
    }
    for field in &policy.key_fields {
        let value = key.get(field).ok_or(AuditError::Invalid(
            "record key is missing a configured field",
        ))?;
        if image.get(field) != Some(value) { // [reconstructed]
            return Err(AuditError::Invalid("record key disagrees with row image"));
        }
    }
    Ok((before, after))
}

fn changed_fields(
    policy: &TablePolicy,
    before: Option<&Map<String, Value>>,
    after: Option<&Map<String, Value>>,
) -> Vec<String> {
    let mut changed = BTreeSet::new();
    for field in before.into_iter().chain(after).flat_map(Map::keys) {
        if !policy.secret_fields.contains(field)
            && !policy.ignored_fields.contains(field)
            && value_at(before, field) != value_at(after, field)
        {
            changed.insert(field.clone());
        }
    }
    changed.into_iter().collect()
}

fn project(
    table: &str,
    policy: &TablePolicy,
    image: Option<Map<String, Value>>,
) -> Result<Option<Map<String, Value>>, AuditError> {
    let Some(image) = image else {
        return Ok(None);
    };
    let mut projected = Map::new();
    for field in policy
        .allowed_fields
        .iter()
        .cloned()
        .collect::<BTreeSet<_>>()
    {
        if let Some(value) = image.get(&field) {
            projected.insert(field.clone(), normalize_value(table, &field, value)?); // [reconstructed]
        }
    }
    Ok(Some(projected))
}

fn normalize_value(table: &str, field: &str, value: &Value) -> Result<Value, AuditError> {
    match (table, field) {
        ("bookmarks" | "tags", "target")
        | ("change_states", "change_id")
        | ("check_runs", "changeset_id") => {}
        _ => return Ok(value.clone()),
    }
    // [reconstructed] hex/base64 normalization elided.
    Ok(value.clone())
}

fn value_at(image: Option<&Map<String, Value>>, field: &str) -> Value {
    image
        .and_then(|image| image.get(field))
        .cloned()
        .unwrap_or(Value::Null)
}
