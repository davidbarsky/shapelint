fn build_payload(id: u64) {
    let _ = json!({ "id": id });
    let _ = serde_json::json!({ "id": id });
    assert!(serde_json::json!({ "id": id }).is_object());
}
