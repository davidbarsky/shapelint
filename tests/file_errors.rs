#![feature(rustc_private)]

use std::process::Command;

#[test]
fn unreadable_source_is_an_error_even_with_exit_zero() {
    let directory = tempfile::tempdir().expect("create project");
    std::fs::write(directory.path().join("invalid.rs"), [0xff]).expect("write invalid UTF-8");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(directory.path())
        .args(["--exit-zero", "invalid.rs"])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(64));
    assert!(String::from_utf8_lossy(&output.stderr).contains("could not read invalid.rs"));
}

#[test]
fn broken_links_found_during_traversal_are_errors() {
    let directory = tempfile::tempdir().expect("create project");
    std::os::unix::fs::symlink("missing", directory.path().join("broken.rs"))
        .expect("create broken link");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(directory.path())
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(64));
    assert!(String::from_utf8_lossy(&output.stderr).contains("could not inspect ./broken.rs"));
}

#[test]
fn assert_message_is_not_a_rule() {
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .args(["rules", "assert-message"])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(2));
}
