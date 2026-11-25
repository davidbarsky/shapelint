#![feature(rustc_private)]

use std::path::Path;
use std::process::Command;

#[derive(Debug, PartialEq, Eq, serde::Deserialize)]
struct Finding {
    path: String,
    rule: String,
}

fn jj(directory: &Path, args: &[&str]) -> String {
    let output = Command::new("jj")
        .current_dir(directory)
        .env("JJ_CONFIG", "")
        .args([
            "--config",
            "user.name=Shapelint",
            "--config",
            "user.email=shapelint@example.com",
        ])
        .args(args)
        .output()
        .expect("run jj; CLI integration tests require jj on PATH");
    assert!(
        output.status.success(),
        "jj {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).expect("UTF-8 jj output")
}

fn project() -> tempfile::TempDir {
    let project = tempfile::tempdir().expect("create project");
    jj(project.path(), &["git", "init", "--no-colocate"]);
    project
}

fn lint(directory: &Path, args: &[&str]) -> Vec<Finding> {
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(directory)
        .env("JJ_CONFIG", "")
        .args(["--format", "json", "--exit-zero"])
        .args(args)
        .output()
        .expect("run shapelint");
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stderr, b"");
    serde_json::Deserializer::from_slice(&output.stdout)
        .into_iter::<Finding>()
        .collect::<Result<_, _>>()
        .expect("JSON findings")
}

#[test]
fn change_id_selects_files_but_lints_current_contents() {
    let project = project();
    std::fs::write(project.path().join("unrelated.rs"), "use unrelated::*;\n")
        .expect("write source");
    jj(project.path(), &["new"]);
    std::fs::write(project.path().join("selected.rs"), "struct Selected;\n").expect("write source");
    jj(project.path(), &["new"]);
    let change = jj(
        project.path(),
        &["log", "-r", "@-", "--no-graph", "-T", "change_id.short()"],
    );
    std::fs::write(project.path().join("selected.rs"), "use selected::*;\n")
        .expect("update source");
    std::fs::write(project.path().join("current.rs"), "use current::*;\n").expect("write source");

    assert_eq!(
        lint(project.path(), &["-r", &change]),
        vec![Finding {
            path: "selected.rs".into(),
            rule: "glob-import".into(),
        }]
    );
}

#[test]
fn revset_selects_the_net_changes_across_a_stack() {
    let project = project();
    std::fs::write(project.path().join("deleted.rs"), "use deleted::*;\n").expect("write source");
    jj(project.path(), &["new"]);
    std::fs::remove_file(project.path().join("deleted.rs")).expect("delete source");
    std::fs::write(project.path().join("first.rs"), "use first::*;\n").expect("write source");
    jj(project.path(), &["new"]);
    std::fs::write(project.path().join("second.rs"), "use second::*;\n").expect("write source");
    jj(project.path(), &["new"]);
    std::fs::write(project.path().join("current.rs"), "use current::*;\n").expect("write source");

    assert_eq!(
        lint(project.path(), &["changed", "-r", "@--::@-"]),
        vec![
            Finding {
                path: "first.rs".into(),
                rule: "glob-import".into()
            },
            Finding {
                path: "second.rs".into(),
                rule: "glob-import".into()
            },
        ]
    );
}

#[test]
fn revision_selection_from_a_subdirectory_includes_sibling_paths() {
    let project = project();
    std::fs::create_dir(project.path().join("src")).expect("create source directory");
    std::fs::write(project.path().join("src/inside.rs"), "use inside::*;\n").expect("write source");
    std::fs::write(project.path().join("outside.rs"), "use outside::*;\n").expect("write source");
    jj(project.path(), &["new"]);
    let root = project.path().canonicalize().expect("resolve project");

    assert_eq!(
        lint(&root.join("src"), &["check", "--revision", "@-"]),
        vec![
            Finding {
                path: root.join("outside.rs").to_string_lossy().into(),
                rule: "glob-import".into()
            },
            Finding {
                path: "inside.rs".into(),
                rule: "glob-import".into()
            },
        ]
    );
}

#[test]
fn changed_defaults_to_the_working_copy_and_respects_exclusions() {
    let project = project();
    std::fs::create_dir(project.path().join("generated")).expect("create source directory");
    std::fs::write(project.path().join(".shapelint"), "exclude = generated\n")
        .expect("write config");
    std::fs::write(
        project.path().join("generated/file.rs"),
        "use generated::*;\n",
    )
    .expect("write source");
    std::fs::write(project.path().join("file.rs"), "use source::*;\n").expect("write source");
    std::fs::write(project.path().join("notes.txt"), "use notes::*;\n").expect("write text");

    assert_eq!(
        lint(project.path(), &["changed"]),
        vec![Finding {
            path: "file.rs".into(),
            rule: "glob-import".into(),
        }]
    );
}

#[test]
fn renamed_paths_preserve_spaces_quotes_and_newlines() {
    let project = project();
    std::fs::write(project.path().join("old.rs"), "use renamed::*;\n").expect("write source");
    jj(project.path(), &["new"]);
    let name = " renamed\"\nfile.rs";
    std::fs::rename(project.path().join("old.rs"), project.path().join(name))
        .expect("rename source");
    std::fs::write(project.path().join(name), "use changed::*;\n").expect("update source");

    assert_eq!(
        lint(project.path(), &["changed"]),
        vec![Finding {
            path: name.into(),
            rule: "glob-import".into(),
        }]
    );
}

#[test]
fn current_revision_reports_only_changed_lines() {
    let project = project();
    std::fs::write(
        project.path().join("file.rs"),
        "use std::fmt as fmt;\n\nstruct Before;\n",
    )
    .expect("write source");
    jj(project.path(), &["new"]);
    std::fs::write(
        project.path().join("file.rs"),
        "use std::fmt as fmt;\n\nuse changed::*;\n",
    )
    .expect("update source");

    assert_eq!(
        lint(project.path(), &["-r", "@"]),
        vec![Finding {
            path: "file.rs".into(),
            rule: "glob-import".into(),
        }]
    );
    assert_eq!(lint(project.path(), &["check", "file.rs"]).len(), 2);
}

#[test]
fn deletions_do_not_report_findings_on_adjacent_lines() {
    let project = project();
    std::fs::write(
        project.path().join("file.rs"),
        "struct Removed;\nuse untouched::*;\n",
    )
    .expect("write source");
    jj(project.path(), &["new"]);
    std::fs::write(project.path().join("file.rs"), "use untouched::*;\n").expect("update source");

    assert_eq!(lint(project.path(), &["changed"]), Vec::new());
}

#[test]
fn pure_renames_do_not_report_unchanged_lines() {
    let project = project();
    std::fs::write(project.path().join("old.rs"), "use untouched::*;\n").expect("write source");
    jj(project.path(), &["new"]);
    std::fs::rename(project.path().join("old.rs"), project.path().join("new.rs"))
        .expect("rename source");

    assert_eq!(lint(project.path(), &["-r", "@"]), Vec::new());
}

#[test]
fn multiline_primary_labels_overlap_changed_lines() {
    let project = project();
    std::fs::write(
        project.path().join("file.rs"),
        "struct State {\n    value: Option<\n        u8\n    >,\n}\n",
    )
    .expect("write source");
    jj(project.path(), &["new"]);
    std::fs::write(
        project.path().join("file.rs"),
        "struct State {\n    value: Option<\n        bool\n    >,\n}\n",
    )
    .expect("update source");

    assert_eq!(
        lint(project.path(), &["-r", "@"]),
        vec![Finding {
            path: "file.rs".into(),
            rule: "boolean-state".into(),
        }]
    );
}

#[test]
fn current_diff_from_a_subdirectory_includes_sibling_paths() {
    let project = project();
    std::fs::create_dir(project.path().join("src")).expect("create source directory");
    std::fs::write(project.path().join("outside.rs"), "use untouched::*;\n").expect("write source");
    jj(project.path(), &["new"]);
    std::fs::write(
        project.path().join("outside.rs"),
        "use untouched::*;\nuse added::*;\n",
    )
    .expect("update source");
    let root = project.path().canonicalize().expect("resolve project");

    assert_eq!(
        lint(&root.join("src"), &["-r", "@"]),
        vec![Finding {
            path: root.join("outside.rs").to_string_lossy().into(),
            rule: "glob-import".into(),
        }]
    );
}

#[test]
fn unchanged_findings_do_not_fail_the_command() {
    let project = project();
    std::fs::write(project.path().join("file.rs"), "use untouched::*;\n").expect("write source");
    jj(project.path(), &["new"]);
    std::fs::write(
        project.path().join("file.rs"),
        "use untouched::*;\n\nstruct Added;\n",
    )
    .expect("update source");

    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(project.path())
        .env("JJ_CONFIG", "")
        .args(["-r", "@"])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"");
    assert_eq!(output.stderr, b"");
}

#[test]
fn empty_revision_does_not_fall_back_to_linting_the_directory() {
    let project = project();
    std::fs::write(project.path().join("file.rs"), "use source::*;\n").expect("write source");
    jj(project.path(), &["new"]);

    assert_eq!(lint(project.path(), &["-r", "@"]), Vec::new());
}

#[test]
fn selected_files_missing_from_the_working_copy_are_skipped() {
    let project = project();
    std::fs::write(project.path().join("file.rs"), "use source::*;\n").expect("write source");
    jj(project.path(), &["new"]);
    std::fs::remove_file(project.path().join("file.rs")).expect("delete source");

    assert_eq!(lint(project.path(), &["-r", "@-"]), Vec::new());
}

#[test]
fn invalid_revision_is_an_error_even_with_exit_zero() {
    let project = project();
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(project.path())
        .env("JJ_CONFIG", "")
        .args(["--exit-zero", "changed", "-r", "missing_revision"])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(64));
    assert_eq!(output.stdout, b"");
    assert!(String::from_utf8_lossy(&output.stderr).contains("missing_revision"));
}

#[test]
fn changed_requires_a_jj_repository() {
    let project = tempfile::tempdir().expect("create project");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(project.path())
        .env("PATH", project.path())
        .args(["changed"])
        .output()
        .expect("run shapelint");
    assert_eq!(output.status.code(), Some(64));
    assert_eq!(output.stdout, b"");
    assert!(String::from_utf8_lossy(&output.stderr).contains("requires a jj repository"));
}
