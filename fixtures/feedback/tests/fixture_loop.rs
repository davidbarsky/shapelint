#[test]
fn builds_fixtures() {
    let mut fixtures = Vec::new();
    for item in [1, 2, 3] {
        fixtures.push(make_fixture(item));
    }
    assert_eq!(fixtures.len(), 3);
}
