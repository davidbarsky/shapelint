#![feature(rustc_private)]

use std::process::Command;

use shapelint::{Config, SourceInput, lint, lint_sources};
use tempfile::TempDir;

struct CliOutput {
    status: Option<i32>,
    stdout: String,
}

#[test]
fn one_implementation_across_sources_reports_on_the_trait() {
    let inputs = vec![
        SourceInput::try_new(
            "src/clock.rs",
            include_str!("../fixtures/feedback/workspace/trait.rs"),
        )
        .expect("fixture source fits in u32"),
        SourceInput::try_new(
            "src/system.rs",
            include_str!("../fixtures/feedback/workspace/impl.rs"),
        )
        .expect("fixture source fits in u32"),
    ];
    let findings = lint_sources(&inputs, &Config::default()).expect("sources lint successfully");
    assert_eq!(
        findings[0]
            .iter()
            .filter(|finding| finding.rule == "single-impl-trait")
            .count(),
        1
    );
    assert!(
        findings[1]
            .iter()
            .all(|finding| finding.rule != "single-impl-trait")
    );
    assert!(findings[0][0].footers.iter().any(|footer| match footer {
        shapelint::Footer::Note { message } => message.contains("supplied sources"),
        shapelint::Footer::Help { .. } | shapelint::Footer::Suggestion { .. } => false,
    }));
    assert!(findings[0][0].footers.iter().any(|footer| match footer {
        shapelint::Footer::Note { message } => {
            message.contains("impl Clock for SystemClock") && message.contains("src/system.rs")
        }
        shapelint::Footer::Help { .. } | shapelint::Footer::Suggestion { .. } => false,
    }));
}

#[test]
fn a_second_implementation_exempts_the_trait() {
    let inputs = vec![
        SourceInput::try_new(
            "src/clock.rs",
            include_str!("../fixtures/feedback/workspace/trait.rs"),
        )
        .expect("fixture source fits in u32"),
        SourceInput::try_new(
            "src/system.rs",
            include_str!("../fixtures/feedback/workspace/impl.rs"),
        )
        .expect("fixture source fits in u32"),
        SourceInput::try_new(
            "tests/clock.rs",
            include_str!("../fixtures/feedback/workspace/second_impl.rs"),
        )
        .expect("fixture source fits in u32"),
    ];
    let findings = lint_sources(&inputs, &Config::default()).expect("sources lint successfully");
    assert!(
        findings[0]
            .iter()
            .all(|finding| finding.rule != "single-impl-trait")
    );
}

#[test]
fn same_name_traits_in_different_modules_are_not_conflated() {
    let inputs = vec![
        SourceInput::try_new(
            "src/a.rs",
            include_str!("../fixtures/feedback/workspace/ambiguous_a.rs"),
        )
        .expect("fixture source fits in u32"),
        SourceInput::try_new(
            "src/b.rs",
            include_str!("../fixtures/feedback/workspace/ambiguous_b.rs"),
        )
        .expect("fixture source fits in u32"),
        SourceInput::try_new(
            "src/worker.rs",
            include_str!("../fixtures/feedback/workspace/ambiguous_impl.rs"),
        )
        .expect("fixture source fits in u32"),
    ];
    let findings = lint_sources(&inputs, &Config::default()).expect("sources lint successfully");
    assert!(
        findings[0]
            .iter()
            .all(|finding| finding.rule != "single-impl-trait")
    );
    assert!(
        findings[1]
            .iter()
            .all(|finding| finding.rule != "single-impl-trait")
    );
}

// shapelint: allow(literal-test-cases) These sizes form one cross-size ambiguity scaling gate.
#[test]
fn many_ambiguous_short_names_remain_conservative() {
    for count in [8, 16, 32] {
        let mut inputs = Vec::with_capacity(count + 1);
        for index in 0..count {
            inputs.push(
                SourceInput::try_new(
                    format!("src/module_{index}.rs"),
                    "pub trait Shared { fn run(&self); }\n",
                )
                .expect("fixture source fits in u32"),
            );
        }
        inputs.push(
            SourceInput::try_new(
                "src/worker.rs",
                "struct Worker;\nimpl Shared for Worker { fn run(&self) {} }\n",
            )
            .expect("fixture source fits in u32"),
        );
        let findings =
            lint_sources(&inputs, &Config::default()).expect("sources lint successfully");
        assert!(
            findings
                .iter()
                .flatten()
                .all(|finding| { finding.rule != "single-impl-trait" })
        );
        eprintln!("AUDIT workspace ambiguous count={count}");
    }
}

#[test]
fn qualified_path_uses_file_module_scope() {
    let inputs = vec![
        SourceInput::try_new("src/clock.rs", "pub trait Clock { fn run(&self); }\n")
            .expect("fixture source fits in u32"),
        SourceInput::try_new(
            "src/worker.rs",
            "struct Worker;\nimpl clock::Clock for Worker { fn run(&self) {} }\n",
        )
        .expect("fixture source fits in u32"),
    ];
    let findings = lint_sources(&inputs, &Config::default()).expect("sources lint successfully");
    assert_eq!(
        findings[0]
            .iter()
            .filter(|finding| finding.rule == "single-impl-trait")
            .count(),
        1
    );
}

#[test]
fn same_module_files_share_unqualified_trait_resolution() {
    let inputs = vec![
        SourceInput::try_new(
            "crate_a/src/foo.rs",
            "pub trait Shared { fn run(&self); }\n",
        )
        .expect("fixture source fits in u32"),
        SourceInput::try_new(
            "crate_b/src/foo.rs",
            "pub trait Shared { fn run(&self); }\n",
        )
        .expect("fixture source fits in u32"),
        SourceInput::try_new(
            "crate_a/src/foo/mod.rs",
            "struct Worker;\nimpl Shared for Worker { fn run(&self) {} }\n",
        )
        .expect("fixture source fits in u32"),
    ];
    let findings = lint_sources(&inputs, &Config::default()).expect("sources lint successfully");
    assert_eq!(
        findings[0]
            .iter()
            .filter(|finding| finding.rule == "single-impl-trait")
            .count(),
        1
    );
    assert!(
        findings[1]
            .iter()
            .all(|finding| finding.rule != "single-impl-trait")
    );
}

#[test]
fn qualified_paths_ignore_comments_and_whitespace() {
    let input = SourceInput::try_new(
        "src/lib.rs",
        include_str!("../fixtures/feedback/workspace/qualified_paths.rs"),
    )
    .expect("fixture source fits in u32");
    let findings = lint(&input, &Config::default()).expect("source lints successfully");
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "single-impl-trait")
            .count(),
        1
    );
}

#[test]
fn unique_names_across_different_crates_are_not_matched() {
    let inputs = vec![
        SourceInput::try_new("crate_a/src/lib.rs", "pub trait Clock { fn run(&self); }\n")
            .expect("fixture source fits in u32"),
        SourceInput::try_new(
            "crate_b/src/worker.rs",
            "struct Worker;\nimpl Clock for Worker { fn run(&self) {} }\n",
        )
        .expect("fixture source fits in u32"),
    ];
    let findings = lint_sources(&inputs, &Config::default()).expect("sources lint successfully");
    assert!(
        findings[0]
            .iter()
            .all(|finding| finding.rule != "single-impl-trait")
    );
}

#[test]
fn generic_trait_paths_are_counted_and_marked_as_generic() {
    let input = SourceInput::try_new(
        "src/generic.rs",
        include_str!("../fixtures/feedback/workspace/generic.rs"),
    )
    .expect("fixture source fits in u32");
    let findings = lint(&input, &Config::default()).expect("source lints successfully");
    let findings: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "single-impl-trait")
        .collect();
    assert_eq!(findings.len(), 1);
    assert!(findings[0].footers.iter().any(|footer| match footer {
        shapelint::Footer::Note { message } => message.contains("generic"),
        shapelint::Footer::Help { .. } | shapelint::Footer::Suggestion { .. } => false,
    }));
}

#[test]
fn suppression_is_applied_to_workspace_findings() {
    let inputs = vec![
        SourceInput::try_new(
            "src/suppressed.rs",
            include_str!("../fixtures/feedback/workspace/suppressed.rs"),
        )
        .expect("fixture source fits in u32"),
    ];
    let findings = lint_sources(&inputs, &Config::default()).expect("sources lint successfully");
    assert!(
        findings[0]
            .iter()
            .all(|finding| finding.rule != "single-impl-trait")
    );
}

#[test]
fn one_source_uses_the_same_workspace_pass() {
    let input = SourceInput::try_new(
        "src/local.rs",
        "trait Local { fn run(&self); }\nstruct Worker;\nimpl Local for Worker { fn run(&self) {} }\n",
    ).expect("fixture source fits in u32");
    let findings = lint(&input, &Config::default()).expect("source lints successfully");
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "single-impl-trait")
            .count(),
        1
    );
}

#[test]
fn negative_implementations_do_not_count() {
    let input = SourceInput::try_new(
        "src/negative.rs",
        include_str!("../fixtures/feedback/workspace/negative.rs"),
    )
    .expect("fixture source fits in u32");
    let findings = lint(&input, &Config::default()).expect("source lints successfully");
    assert!(
        findings
            .iter()
            .all(|finding| finding.rule != "single-impl-trait")
    );
}

#[test]
fn qualified_super_path_uses_the_parent_module_scope() {
    let input = SourceInput::try_new(
        "src/parent.rs",
        include_str!("../fixtures/feedback/workspace/qualified_super.rs"),
    )
    .expect("fixture source fits in u32");
    let findings = lint(&input, &Config::default()).expect("source lints successfully");
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "single-impl-trait")
            .count(),
        1
    );
}

#[test]
fn local_traits_do_not_share_the_file_module_scope() {
    let input = SourceInput::try_new(
        "src/local.rs",
        "fn build() { trait Local { fn run(&self); } struct Worker; impl Local for Worker { fn run(&self) {} } }\n",
    ).expect("fixture source fits in u32");
    let findings = lint(&input, &Config::default()).expect("source lints successfully");
    assert!(
        findings
            .iter()
            .all(|finding| finding.rule != "single-impl-trait")
    );
}

#[test]
fn cli_counts_only_the_sources_in_the_corpus() {
    let project = tempfile::tempdir().expect("create temporary project");
    write_fixture(
        &project,
        "src/clock.rs",
        include_str!("../fixtures/feedback/workspace/trait.rs"),
    );
    write_fixture(
        &project,
        "src/system.rs",
        include_str!("../fixtures/feedback/workspace/impl.rs"),
    );
    write_fixture(
        &project,
        "tests/fake.rs",
        include_str!("../fixtures/feedback/workspace/second_impl.rs"),
    );

    let src = run_cli_with_paths(&project, [project.path().join("src")]);
    assert_eq!(src.status, Some(1));
    let src_paths = single_impl_paths(&src.stdout);
    assert_eq!(src_paths.len(), 1);
    assert!(src_paths[0].ends_with("/src/clock.rs"));

    let full = run_cli_with_paths(&project, [project.path().to_path_buf()]);
    assert_eq!(full.status, Some(0));
    assert!(single_impl_paths(&full.stdout).is_empty());
}

#[test]
fn cli_accepts_absolute_paths_for_separate_modules() {
    let project = tempfile::tempdir().expect("create temporary project");
    write_fixture(
        &project,
        "src/clock.rs",
        include_str!("../fixtures/feedback/workspace/trait.rs"),
    );
    write_fixture(
        &project,
        "src/system.rs",
        include_str!("../fixtures/feedback/workspace/impl.rs"),
    );
    let output = run_cli_with_paths(
        &project,
        [
            project.path().join("src/clock.rs"),
            project.path().join("src/system.rs"),
        ],
    );
    assert_eq!(output.status, Some(1));
    let paths = single_impl_paths(&output.stdout);
    assert_eq!(paths.len(), 1);
    assert!(paths[0].ends_with("/src/clock.rs"));
}

#[test]
fn cli_mixes_relative_and_absolute_paths_in_one_corpus() {
    let project = tempfile::tempdir().expect("create temporary project");
    write_fixture(
        &project,
        "src/clock.rs",
        include_str!("../fixtures/feedback/workspace/trait.rs"),
    );
    write_fixture(
        &project,
        "src/system.rs",
        include_str!("../fixtures/feedback/workspace/impl.rs"),
    );
    let output = run_cli_with_paths(
        &project,
        [
            std::path::PathBuf::from("src/clock.rs"),
            project.path().join("src/system.rs"),
        ],
    );
    assert_eq!(output.status, Some(1));
    let paths = single_impl_paths(&output.stdout);
    assert_eq!(paths.len(), 1);
    assert_eq!(paths, ["src/clock.rs"]);
}

fn write_fixture(project: &TempDir, path: &str, text: &str) {
    let path = project.path().join(path);
    std::fs::create_dir_all(path.parent().expect("fixture has a parent"))
        .expect("create fixture directory");
    std::fs::write(path, text).expect("write fixture");
}

fn run_cli_with_paths<I>(project: &TempDir, paths: I) -> CliOutput
where
    I: IntoIterator<Item = std::path::PathBuf>,
{
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint"))
        .current_dir(project.path())
        .arg("--format")
        .arg("json")
        .arg("--only")
        .arg("lint")
        .arg("check")
        .args(paths)
        .output()
        .expect("run shapelint");
    CliOutput {
        status: output.status.code(),
        stdout: String::from_utf8(output.stdout).expect("CLI output is UTF-8"),
    }
}

fn single_impl_paths(output: &str) -> Vec<String> {
    output
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("finding JSON"))
        .filter_map(|finding| {
            (finding.get("rule")?.as_str()? == "single-impl-trait")
                .then(|| finding.get("path")?.as_str().map(str::to_string))
                .flatten()
        })
        .collect()
}
