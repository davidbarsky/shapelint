#![feature(rustc_private)]

use hegel::PrintableGenerator;
use hegel::generators::{BoxedPrintableGenerator, DefaultGenerator};
use std::os::unix::fs::PermissionsExt;
use std::path::PathBuf;
use std::process::{Command, Output};

#[derive(serde::Deserialize)]
struct Finding {
    path: String,
    rule: String,
    kind: String,
    line: u32,
}

struct Project {
    directory: tempfile::TempDir,
    path: std::ffi::OsString,
}

impl Project {
    fn new() -> Project {
        let directory = tempfile::tempdir().expect("create project");
        std::fs::create_dir(directory.path().join(".jj")).expect("mark jj repository");
        let bin = directory.path().join("bin");
        std::fs::create_dir(&bin).expect("create command directory");
        let jj = bin.join("jj");
        std::fs::write(&jj, include_str!("fixtures/jj.py")).expect("write jj protocol fixture");
        std::fs::set_permissions(&jj, std::fs::Permissions::from_mode(0o755))
            .expect("make jj executable");
        std::fs::write(
            directory.path().join("file.rs"),
            "use first::*;\nuse second::*;\nuse third::*;\n",
        )
        .expect("write source");
        std::fs::write(
            directory.path().join("jj-output.patch"),
            "@@ -1,3 +1,3 @@\n",
        )
        .expect("write diff");
        let path = std::env::join_paths(std::iter::once(bin).chain(std::env::split_paths(
            &std::env::var_os("PATH").expect("PATH is set"),
        )))
        .expect("join command path");
        Project { directory, path }
    }

    fn write(&self, name: &str, contents: &str) {
        let path = self.directory.path().join(name);
        std::fs::write(&path, contents)
            .unwrap_or_else(|error| panic!("writing {}: {error}", path.display()));
    }

    fn jj_arguments(&self) -> Vec<String> {
        let bytes = std::fs::read(self.directory.path().join("jj-arguments.json"))
            .expect("read jj invocation");
        serde_json::from_slice(&bytes).expect("decode jj arguments")
    }

    fn run(&self, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_shapelint"))
            .current_dir(self.directory.path())
            .env("PATH", &self.path)
            .args(args)
            .output()
            .expect("run shapelint")
    }
}

#[test]
fn help_constructs_the_complete_command() {
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .arg("--help")
        .output()
        .expect("run help");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stderr, b"");
    assert!(String::from_utf8_lossy(&output.stdout).contains("--revision"));
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum CommandPosition {
    Default,
    CheckBefore,
    CheckAfter,
    ChangedBefore,
    ChangedAfter,
}

#[derive(Debug)]
struct RevisionInput {
    command: CommandPosition,
    revision: String,
}

impl DefaultGenerator for RevisionInput {
    type Generator = BoxedPrintableGenerator<'static, Self>;

    fn default_generator() -> Self::Generator {
        hegel::compose!(|tc| {
            let command = tc.draw(hegel::generators::default::<CommandPosition>());
            let revision = tc.draw(hegel::generators::text().exclude_characters("\0"));
            RevisionInput { command, revision }
        })
        .boxed_printable()
    }
}

#[hegel::test]
fn revision_flags_reach_jj_from_every_command_position(tc: hegel::TestCase) {
    let RevisionInput { command, revision } =
        tc.draw(hegel::generators::default::<RevisionInput>());
    let project = Project::new();
    let flag = format!("--revision={revision}");
    let args = match command {
        CommandPosition::Default => vec!["--format=json", &flag],
        CommandPosition::CheckBefore => vec!["--format=json", &flag, "check"],
        CommandPosition::CheckAfter => vec!["--format=json", "check", &flag],
        CommandPosition::ChangedBefore => vec!["--format=json", &flag, "changed"],
        CommandPosition::ChangedAfter => vec!["--format=json", "changed", &flag],
    };
    let output = project.run(&args);
    assert_eq!(
        output.status.code(),
        Some(1),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stderr, b"");
    let args = project.jj_arguments();
    let index = args
        .iter()
        .position(|argument| argument == "-r")
        .expect("revision flag");
    assert_eq!(args[index + 1], revision);
}

#[test]
fn revision_and_explicit_paths_are_rejected_together() {
    let project = Project::new();
    let output = project.run(&["-r", "@-", "check", "file.rs"]);
    assert_eq!(output.status.code(), Some(64));
    assert_eq!(output.stdout, b"");
    assert!(String::from_utf8_lossy(&output.stderr).contains("explicit paths"));
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum FlagPosition {
    Before,
    After,
}

#[hegel::test]
fn report_flags_apply_on_both_sides_of_the_subcommand(tc: hegel::TestCase) {
    let position = tc.draw(hegel::generators::default::<FlagPosition>());
    let project = Project::new();
    let args = match position {
        FlagPosition::Before => vec!["--format=json", "check", "file.rs"],
        FlagPosition::After => vec!["check", "file.rs", "--format=json"],
    };
    let output = project.run(&args);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(output.stderr, b"");
    let findings: Vec<Finding> = serde_json::Deserializer::from_slice(&output.stdout)
        .into_iter()
        .collect::<Result<_, _>>()
        .expect("JSON findings");
    assert_eq!(findings.len(), 3);
    assert_eq!(findings[0].path, "file.rs");
    assert_eq!(findings[0].rule, "glob-import");
}

#[test]
fn bare_paths_select_check_and_apply_the_failure_policy() {
    let project = Project::new();
    project.write("other.toml", "timeout_ms = 86400000\n");
    let output = project.run(&[
        "--fail-on",
        "mechanical",
        "--format=json",
        "file.rs",
        "other.toml",
    ]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(output.stderr, b"");
    let findings: Vec<Finding> = serde_json::Deserializer::from_slice(&output.stdout)
        .into_iter()
        .collect::<Result<_, _>>()
        .expect("JSON findings");
    assert!(findings.iter().any(|finding| finding.path == "file.rs"));
    assert!(findings.iter().any(|finding| finding.path == "other.toml"));
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum EmittedRule {
    GlobImport,
    CollectionChoice,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum ReportingMode {
    OnlyLints,
    OnlyMechanical,
    FailOnLints,
    FailOnMechanical,
}

#[hegel::test]
fn rule_selection_and_exit_status_are_independent_of_the_lint_kind(tc: hegel::TestCase) {
    let (rule, mode) = tc.draw(hegel::generators::default::<(EmittedRule, ReportingMode)>());
    let project = Project::new();
    let (source, name) = match rule {
        EmittedRule::GlobImport => ("use example::*;", "glob-import"),
        EmittedRule::CollectionChoice => (
            "type Index = std::collections::BTreeMap<u32, u32>;",
            "collection-choice",
        ),
    };
    project.write("file.rs", source);
    let flag = match mode {
        ReportingMode::OnlyLints => "--only=lint",
        ReportingMode::OnlyMechanical => "--only=mechanical",
        ReportingMode::FailOnLints => "--fail-on=lint",
        ReportingMode::FailOnMechanical => "--fail-on=mechanical",
    };
    let output = project.run(&["check", "--format=json", flag, "file.rs"]);
    let (code, expected_rules) = match (rule, mode) {
        (EmittedRule::CollectionChoice, ReportingMode::OnlyMechanical) => (0, vec![]),
        (EmittedRule::CollectionChoice, ReportingMode::FailOnMechanical) => (0, vec![name]),
        _ => (1, vec![name]),
    };
    assert_eq!(output.status.code(), Some(code));
    assert_eq!(output.stderr, b"");
    let findings = serde_json::Deserializer::from_slice(&output.stdout).into_iter::<Finding>();
    let rules: Vec<_> = findings
        .map(|finding| {
            let finding = finding.expect("JSON finding");
            assert_eq!(finding.kind, "lint");
            finding.rule
        })
        .collect();
    assert_eq!(rules, expected_rules);
}

#[test]
fn global_color_before_the_subcommand_colors_diagnostics() {
    let project = Project::new();
    let output = project.run(&["--color", "always", "check", "file.rs"]);
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(output.stderr, b"");
    assert!(output.stdout.windows(2).any(|bytes| bytes == b"\x1b["));
}

#[test]
fn unknown_rule_is_rejected_with_a_suggestion() {
    let project = Project::new();
    let output = project.run(&["rules", "shallow-helpr"]);
    assert_eq!(output.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&output.stderr).contains("shallow-helper"));
}

#[hegel::test]
fn exclusions_match_complete_normalized_path_components(tc: hegel::TestCase) {
    let components = tc.draw(hegel::generators::vecs(hegel::generators::integers::<u16>()));
    let suffix: PathBuf = components
        .iter()
        .map(|part| format!("dir-{part}"))
        .collect();
    let project = Project::new();
    let path = PathBuf::from("unused/../fixtures/.")
        .join(&suffix)
        .join("file.rs");
    let output = project.run(&[
        "--exclude",
        "fixtures",
        path.to_str().expect("generated path is UTF-8"),
    ]);
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(output.stdout, b"");
    assert_eq!(output.stderr, b"");
    let included = PathBuf::from("fixtures-extra")
        .join(&suffix)
        .join("file.rs");
    let output = project.run(&[
        "--exclude",
        "fixtures",
        included.to_str().expect("generated path is UTF-8"),
    ]);
    assert_eq!(output.status.code(), Some(64));
    let nested = PathBuf::from("src/fixtures").join(&suffix).join("file.rs");
    let output = project.run(&[
        "--exclude",
        "fixtures",
        nested.to_str().expect("generated path is UTF-8"),
    ]);
    assert_eq!(output.status.code(), Some(64));
    let absolute = project
        .directory
        .path()
        .canonicalize()
        .expect("resolve process working directory")
        .join("fixtures")
        .join(&suffix)
        .join("file.rs");
    let output = project.run(&[
        "--exclude",
        "fixtures",
        absolute.to_str().expect("generated path is UTF-8"),
    ]);
    assert_eq!(output.status.code(), Some(0));
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum LineCount {
    Implicit,
    Explicit(u16),
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Hunk {
    offset: u16,
    count: LineCount,
}

#[hegel::test]
fn diff_hunks_select_only_findings_on_added_lines(tc: hegel::TestCase) {
    let hunks = tc.draw(hegel::generators::vecs(hegel::generators::default::<Hunk>()));
    let project = Project::new();
    let mut diff = String::from("diff --git a/file.rs b/file.rs\n--- a/file.rs\n+++ b/file.rs\n");
    // shapelint: allow(collection-choice) Expected findings must follow source-line order, including overlapping hunks.
    let mut lines = std::collections::BTreeSet::new();
    for Hunk { offset, count } in hunks {
        let start = u32::from(offset) + 1;
        let count = match count {
            LineCount::Implicit => {
                diff.push_str(&format!("@@ -1 +{start} @@\n-old\n+new\n"));
                1
            }
            LineCount::Explicit(count) => {
                diff.push_str(&format!("@@ -1 +{start},{count} @@\n"));
                u32::from(count)
            }
        };
        lines.extend((start..start + count).filter(|line| *line <= 3));
    }
    project.write("jj-output.patch", &diff);
    let output = project.run(&["changed", "--format=json", "--exit-zero"]);
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stderr, b"");
    let findings: Vec<Finding> = serde_json::Deserializer::from_slice(&output.stdout)
        .into_iter()
        .collect::<Result<_, _>>()
        .expect("JSON findings");
    assert_eq!(
        findings
            .iter()
            .map(|finding| finding.line)
            .collect::<Vec<_>>(),
        lines.into_iter().collect::<Vec<_>>()
    );
}

#[hegel::test]
fn malformed_diff_hunks_report_the_offending_header(tc: hegel::TestCase) {
    let suffix = tc.draw(hegel::generators::default::<String>());
    let project = Project::new();
    let diff = format!("@@ -1 +invalid{suffix:?} @@\n");
    project.write("jj-output.patch", &diff);
    let output = project.run(&["changed", "--format=json", "--exit-zero"]);
    assert_eq!(output.status.code(), Some(64));
    assert_eq!(output.stdout, b"");
    assert!(String::from_utf8_lossy(&output.stderr).contains(diff.trim_end()));
}
