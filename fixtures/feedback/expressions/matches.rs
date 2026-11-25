fn variant_is_present(value: Option<u8>) -> bool {
    matches!(value, Some(_))
}

fn qualified_variant_is_present(value: Option<u8>) -> bool {
    core::matches!(value, Some(_))
}

fn nested_variant_is_present(value: Option<u8>) -> bool {
    assert!(std::matches!(value, Some(_)));
}

fn text_only() {
    let _ = "matches!(value, Some(_))";
    // matches!(value, Some(_)) in a comment is not an invocation.
}
