#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use std::fmt::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use rustc_middle::ty::TyCtxt;
use shapelint_driver::contracts::graph::with_graph;
use shapelint_driver::{analysis, artifacts, callers, contracts, diagnostics, pipeline};

const REFERENCE: &str = concat!(env!("CARGO_MANIFEST_DIR"), "/../fixtures/reference");

#[test]
fn reference_crate_preserves_complete_diagnostics() {
    let reference = Path::new(REFERENCE)
        .canonicalize()
        .expect("reference crate");
    let directory = tempfile::tempdir().expect("compiler outputs");
    let run = |flags: &[&str]| -> Vec<serde_json::Value> {
        let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .current_dir(&reference)
            .args([
                "--format=json",
                "--crate-type=lib",
                "--crate-name=shapelint_reference",
                "--edition=2024",
                "--emit=metadata",
            ])
            .args(flags)
            .arg("--out-dir")
            .arg(directory.path())
            .arg("src/lib.rs")
            .output()
            .expect("reference analysis");
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
        let output = String::from_utf8(output.stdout).expect("UTF-8 findings");
        output
            .lines()
            .map(|line| serde_json::from_str(line).expect("serialized finding"))
            .collect()
    };
    let expected: Vec<serde_json::Value> = serde_json::from_str(
        &std::fs::read_to_string(reference.join("expected.json")).expect("diagnostic oracle"),
    )
    .expect("expected findings");
    assert_eq!(run(&[]), expected, "reference diagnostics changed");
    let (gaps, findings): (Vec<_>, Vec<_>) = run(&["--show-analysis-gaps"])
        .into_iter()
        .partition(|row| row["kind"] == "analysis-gap");
    assert_eq!(findings, expected, "coverage changed default findings");
    assert_eq!(gaps.len(), 4);
    assert!(
        gaps.iter()
            .all(|gap| gap["rule"] == "unproven-precondition")
    );
    assert!(
        gaps.iter()
            .any(|gap| gap["item"] == "forwarding::unchecked")
    );
}

fn requirement_work(source: &Path) -> contracts::Work {
    #[derive(Default)]
    struct Capture {
        work: Option<contracts::Work>,
    }
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            self.work = Some(with_graph(|mut graph| {
                let sources = diagnostics::Sources::default();
                let mut analyses = Vec::new();
                for def in tcx.hir_body_owners() {
                    let body = tcx.mir_promoted(def).0.borrow();
                    analyses.push(
                        analysis::analyze(tcx, def, &body, &mut graph, &[], &sources)
                            .expect("MIR analysis"),
                    );
                }
                let imported = artifacts::Inputs::default()
                    .import(tcx, &mut graph)
                    .expect("empty imports");
                let linked = pipeline::Collected::from(analyses).link(imported);
                let analyzed = linked
                    .analyze(
                        tcx,
                        &mut graph,
                        callers::Scope::Library,
                        shapelint_driver::pipeline::AnalysisGaps::Show,
                        &shapelint::Config::default(),
                        &sources,
                    )
                    .expect("linked analysis");
                let findings: &[pipeline::SourceFindings] = analyzed.as_ref();
                let roots: Vec<_> = findings
                    .iter()
                    .flat_map(|source| &source.findings)
                    .filter(|finding| {
                        finding.rule == "unproven-precondition" && finding.item == "root"
                    })
                    .collect();
                assert_eq!(roots.len(), 1, "the forwarded requirement must reach root");
                analyzed.work
            }));
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("compiler outputs");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--crate-name=shapelint_reference".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        source.display().to_string(),
    ];
    let mut callback = Capture::default();
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut callback));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
    callback.work.expect("analysis callback ran")
}

#[test]
fn identity_forwarding_has_linear_requirement_work() {
    let directory = tempfile::tempdir().expect("scaled reference crate");
    let reference = PathBuf::from(REFERENCE);
    for file in std::fs::read_dir(reference.join("src")).expect("fixture sources") {
        let file = file.expect("source entry");
        std::fs::copy(file.path(), directory.path().join(file.file_name())).expect("fixture copy");
    }
    let original = std::fs::read_to_string(reference.join("src/lib.rs")).expect("crate root");
    let source = directory.path().join("lib.rs");
    let mut observations = Vec::new();
    for depth in [8, 16, 32] {
        let mut text = original.clone();
        let mut callee = String::from("forwarding::unchecked");
        for index in 0..depth {
            let name = format!("forward_{index}");
            writeln!(
                text,
                "fn {name}(bytes: &[u8], index: usize) -> u8 {{ {callee}(bytes, index) }}"
            )
            .expect("forwarding function");
            callee = name;
        }
        writeln!(
            text,
            "pub fn root(bytes: &[u8], index: usize) -> u8 {{ {callee}(bytes, index) }}"
        )
        .expect("reporting root");
        std::fs::write(&source, text).expect("scaled crate source");
        let work = requirement_work(&source);
        eprintln!("forwarding depth {depth}: {work:?}");
        observations.push(work);
    }
    let [small, medium, large] = observations.as_slice() else {
        panic!("three doubling observations");
    };
    assert!(medium.requirement_visits >= small.requirement_visits);
    assert!(large.requirement_visits >= medium.requirement_visits);
    let first_growth = medium.requirement_visits - small.requirement_visits;
    let second_growth = large.requirement_visits - medium.requirement_visits;
    assert!(
        second_growth <= 2 * first_growth,
        "doubling the added forwarders must at most double added requirement visits: \
         {first_growth} then {second_growth}; observations: {observations:?}"
    );
}
