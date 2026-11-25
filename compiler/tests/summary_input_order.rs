#![feature(rustc_private)]

use shapelint_driver::artifacts::{Error, Inputs};

#[test]
fn incompatible_dependencies_are_reported_before_a_later_missing_summary() {
    let directory = tempfile::tempdir().unwrap();
    let mut paths = Vec::new();
    for hash in ["first", "second"] {
        let path = directory.path().join(hash);
        let mut artifact: serde_json::Value =
            serde_json::from_str(include_str!("fixtures/summary_input.json")).unwrap();
        artifact["dependencies"][0]["hash"] = hash.into();
        std::fs::write(&path, serde_json::to_vec(&artifact).unwrap()).unwrap();
        paths.push(path);
    }
    paths.push(directory.path().join("missing"));
    match Inputs::try_from(paths.as_slice()) {
        Err(Error::Incompatible(message)) => assert_eq!(
            message,
            "summary inputs disagree about a dependency crate hash"
        ),
        Err(error) => panic!("unexpected error: {error}"),
        Ok(_) => panic!("inconsistent inputs were accepted"),
    }
}
