use serde_json::Value;
use uuid::Uuid;

use crate::translate::TranslateError;

#[cfg(test)]
mod tests;

pub(crate) fn validate_provenance(value: &Value) -> Result<(), TranslateError> {
    let Some(object) = value.as_object() else {
        return Err(TranslateError::Audit("audit provenance must be an object"));
    };
    if object.get("version").and_then(Value::as_u64) != Some(1) {
        return Err(TranslateError::Audit("unsupported provenance version"));
    }
    let Some(initiator) = object.get("initiator").and_then(Value::as_object) else {
        return Err(TranslateError::Audit("missing provenance initiator"));
    };
    let Some(kind) = initiator.get("kind").and_then(Value::as_str) else {
        return Err(TranslateError::Audit("unsupported provenance initiator"));
    };
    if !matches!(kind, "actor" | "pre_authenticated" | "system") { // [reconstructed]
        return Err(TranslateError::Audit("unsupported provenance initiator"));
    }
    Ok(())
}

// [reconstructed] signature; body tail from the C26 excerpt.
pub(crate) fn provenance_actor_id(value: &Value) -> Result<Option<Uuid>, TranslateError> {
    validate_provenance(value)?;
    let initiator = value.get("initiator");
    match initiator.and_then(|i| i.get("kind")).and_then(Value::as_str) {
        Some("actor") => initiator
            .and_then(|i| i.get("id"))
            .and_then(Value::as_str)
            .map(|id| Uuid::parse_str(id).map_err(|_| TranslateError::Audit("invalid actor id")))
            .transpose(),
        Some("pre_authenticated" | "system") => Ok(None),
        _ => Err(TranslateError::Audit("unsupported provenance initiator")),
    }
}

fn validate_row_shape(row: &RowChange) -> Result<(), TranslateError> {
    match (row.operation, &row.before, &row.after) {
        (Operation::Insert, None, Some(_))
        | (Operation::Update, Some(_), Some(_))
        | (Operation::Delete, Some(_), None) => Ok(()),
        _ => Err(TranslateError::Audit("invalid row-change images")),
    }
}

impl RowChange {
    pub(crate) fn kind(&self) -> String {
        let verb = match self.operation {
            Operation::Insert => "create",
            Operation::Update => "update",
            Operation::Delete => "delete",
        };
        format!("{}.{verb}", self.table) // [reconstructed]
    }
}
