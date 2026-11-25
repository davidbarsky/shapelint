fn predicates(value: Option<u8>, result: Result<u8, ()>) {
    if value.is_some() {}
    let _ = result.is_ok_and(|value| value > 0);
    assert!(value.is_some());
    let _ = value.unwrap();
}
