use serde_json::{json, Value};
use uuid::Uuid;

enum RowCapture {
    LoginCreate,
    RefreshFamilyCreate,
}

fn id(seed: u64) -> Uuid {
    Uuid::from_u128(u128::from(seed))
}

fn provenance(actor: Option<Uuid>) -> Value {
    let initiator = match actor {
        Some(actor) => json!({
            "kind": "actor",
            "id": actor,
            "actor_type": "user"
        }),
        None => json!({
            "kind": "pre_authenticated",
            "protocol": "oauth2",
            "client_reference": "test-client"
        }),
    };
    json!({
        "version": 1,
        "initiator": initiator,
        "authentication": {"method": "dpop"},
        "origin": {"transport": "http", "protocol": "oauth2"},
        "service": {"name": "cdc-worker-tests", "deployment": "test"},
        "correlation": {"operation_id": id(42), "trace_id": Value::Null}
    })
}

fn row_message(id: Uuid, capture: RowCapture) -> (Value, &'static str) {
    let (table, operation, before, after, changed_fields, kind) = match capture {
        RowCapture::LoginCreate => (
            "logins",
            "insert",
            None,
            Some(json!({"id": id, "actor_id": id, "kind": "cli_dpop"})),
            vec!["id".to_string()],
            "login.create",
        ),
        RowCapture::RefreshFamilyCreate => (
            "refresh_tokens",
            "insert",
            None,
            Some(json!({"id": id})), // [reconstructed]
            vec!["id".to_string()],
            "refresh_family.create",
        ),
    };
    // [reconstructed] envelope
    (json!({"table": table, "op": operation, "before": before, "after": after, "changed": changed_fields}), kind)
}
