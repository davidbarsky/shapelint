#![feature(rustc_private)]

use std::process::Command;

#[test]
fn shapelint_lints_itself_without_findings() {
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(env!("CARGO_MANIFEST_DIR"))
        .args(["--format", "short", "--fail-on", "mechanical"])
        .output()
        .expect("run shapelint on its own sources");
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
    assert_eq!(output.stderr, b"");
    assert!(
        output.stdout.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stdout)
    );
}
