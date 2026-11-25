// shapelint: allow(matches-macro)
fn suppressed(value: Option<u8>) -> bool {
    matches!(value, Some(_))
}

fn visible(value: Option<u8>) -> bool {
    matches!(value, Some(_))
}
