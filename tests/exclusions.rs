#![feature(rustc_private)]

use std::path::Path;
use std::process::{Command, Stdio};

#[derive(serde::Deserialize)]
struct Finding {
    path: String,
}

fn project() -> tempfile::TempDir {
    let project = tempfile::tempdir().expect("create project");
    std::fs::write(project.path().join(".shapelint"), "exclude = generated\n")
        .expect("write configuration");
    for directory in ["src", "generated/nested", "generated-extra"] {
        let directory = project.path().join(directory);
        std::fs::create_dir_all(&directory).expect("create source directory");
        std::fs::write(directory.join("file.rs"), "use example::*;\n").expect("write source");
    }
    project
}

#[test]
fn config_exclusions_are_relative_to_config_from_a_subdirectory() {
    let project = project();
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(project.path().join("src"))
        .args(["--format", "json", ".."])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(output.stderr, b"");
    let findings: Vec<Finding> = String::from_utf8(output.stdout)
        .expect("UTF-8 output")
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let paths: Vec<_> = findings
        .iter()
        .map(|finding| finding.path.as_str())
        .collect();
    assert_eq!(paths, ["../generated-extra/file.rs", "../src/file.rs"]);
}

#[test]
fn flags_add_to_config_exclusions_and_skip_explicit_files() {
    let project = project();
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(project.path())
        .args([
            "--exclude",
            "generated-extra",
            "check",
            "--exclude",
            "./src",
            "generated/nested/file.rs",
            "generated-extra/file.rs",
            "src/file.rs",
        ])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"");
    assert_eq!(output.stderr, b"");
}

#[test]
fn excluded_missing_directory_is_allowed() {
    let project = project();
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(project.path())
        .args(["--exclude", "missing", "missing"])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"");
    assert_eq!(output.stderr, b"");
}

#[test]
fn excluded_directory_is_pruned_before_reading_files() {
    let project = project();
    std::fs::write(project.path().join("generated/nested/file.rs"), [0xff])
        .expect("write invalid UTF-8");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(project.path())
        .args(["--exit-zero"])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stderr, b"");
}

#[test]
fn changed_files_respect_exclusions() {
    let project = project();
    let output = Command::new("jj")
        .current_dir(project.path())
        .env("JJ_CONFIG", "")
        .args(["git", "init", "--no-colocate"])
        .output()
        .expect("initialize jj repository");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(project.path())
        .env("JJ_CONFIG", "")
        .args([
            "changed",
            "--exclude",
            "generated-extra",
            "--format",
            "json",
        ])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(output.stderr, b"");
    let findings: Vec<Finding> = String::from_utf8(output.stdout)
        .expect("UTF-8 output")
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let paths: Vec<_> = findings
        .iter()
        .map(|finding| finding.path.as_str())
        .collect();
    assert_eq!(paths, ["src/file.rs"]);
}

#[derive(serde::Serialize)]
struct HookEvent<'a> {
    cwd: &'a Path,
    tool_input: ToolInput<'a>,
}

#[derive(serde::Serialize)]
struct ToolInput<'a> {
    file_path: &'a Path,
}

fn run_hook(event: &HookEvent<'_>, directory: &Path) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(directory)
        .args(["hook", "claude"])
        .env("SHAPELINT_STATE_DIR", directory.join("state"))
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("run hook");
    serde_json::to_writer(child.stdin.take().expect("hook stdin"), event).expect("write event");
    child.wait_with_output().expect("wait for hook")
}

#[test]
fn hook_excludes_paths_relative_to_the_event_project() {
    let project = project();
    let process = tempfile::tempdir().expect("create hook working directory");
    std::fs::write(process.path().join(".shapelint"), "unknown-key = 0\n")
        .expect("write unrelated configuration");
    let event = HookEvent {
        cwd: project.path(),
        tool_input: ToolInput {
            file_path: Path::new("generated/nested/file.rs"),
        },
    };
    let output = run_hook(&event, process.path());
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"");
    assert_eq!(output.stderr, b"");
    assert!(
        !process.path().join("state").exists(),
        "excluded files must not update hook state"
    );
}

#[test]
fn hook_gives_the_model_the_decision_for_an_intentionally_ordered_map() {
    let project = tempfile::tempdir().expect("create hook project");
    std::fs::write(
        project.path().join("index.rs"),
        "fn predecessor(entries: &std::collections::BTreeMap<u32, u32>, key: u32) -> Option<&u32> {
    entries.range(..=key).next_back().map(|(_, value)| value)
}
",
    )
    .expect("write ordered lookup");
    let event = HookEvent {
        cwd: project.path(),
        tool_input: ToolInput {
            file_path: Path::new("index.rs"),
        },
    };
    let output = run_hook(&event, project.path());
    let feedback = std::str::from_utf8(&output.stderr).expect("UTF-8 hook feedback");
    assert_eq!(output.status.code(), Some(2), "{feedback}");
    assert!(feedback.contains("lint[collection-choice]"));
    assert!(feedback.contains("key ranges"));
    assert!(feedback.contains("keep it and explain why"));
    assert!(!feedback.contains("shapelint: allow"));
    let repeat = run_hook(&event, project.path());
    assert_eq!(repeat.status.code(), Some(0));
    assert_eq!(repeat.stderr, b"");
}
