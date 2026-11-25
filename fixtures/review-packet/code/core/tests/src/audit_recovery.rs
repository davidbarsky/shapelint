fn assert_trusted_issuer_event(
    event: &AuditEvent,
    stamp_id: Uuid,
    provenance: &Value,
    issuer: &TrustedIssuer,
    total_order: u64,
) -> Result<(), anyhow::Error> {
    let identity = [
        16_u64.to_be_bytes().as_slice(),
        stamp_id.as_bytes(),
        15_u64.to_be_bytes().as_slice(),
        b"trusted_issuers",
        6_u64.to_be_bytes().as_slice(),
        b"insert",
        8_u64.to_be_bytes().as_slice(),
        &11_u64.to_be_bytes(),
        8_u64.to_be_bytes().as_slice(),
        &total_order.to_be_bytes(),
    ]
    .concat();
    let expected_id = blake3::derive_key("ersc.audit.row-id.v1", &identity);
    if event.id != expected_id {
        return Err(anyhow::anyhow!("assembled event has an unexpected id"));
    }
    if event.target_kind != "trusted-issuer" || event.target_id != issuer.id.to_string() {
        return Err(anyhow::anyhow!("assembled event has the wrong target"));
    }
    let actual_provenance: Value = serde_json::from_str(&event.provenance)?;
    if &actual_provenance != provenance {
        return Err(anyhow::anyhow!("assembled event lost provenance"));
    }
    Ok(()) // [reconstructed]
}
