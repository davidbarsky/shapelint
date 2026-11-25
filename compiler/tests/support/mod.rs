use std::error::Error;
use std::fs;
use std::process::Command;

pub fn analyze(text: &str, flags: &[&str]) -> Result<String, Box<dyn Error>> {
    let directory = tempfile::tempdir()?;
    let path = directory.path().join("completion.rs");
    fs::write(&path, text)?;
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
        ])
        .args(flags)
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&path)
        .output()?;
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    Ok(String::from_utf8(output.stdout)?)
}
