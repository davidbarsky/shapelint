#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;

use rustc_index::IndexVec;
use rustc_middle::mir::{
    BasicBlockData, BasicBlocks, Local, Operand, Place, RETURN_PLACE, Rvalue, START_BLOCK,
    Statement, StatementKind, Terminator, TerminatorKind, WithRetag,
};
use rustc_middle::ty::TyCtxt;
use shapelint_driver::contracts::graph::{ExprNode, with_graph};
use shapelint_driver::diagnostics::Sources;
use shapelint_driver::states;

#[derive(Debug, hegel::DefaultGenerator)]
enum Noise {
    Input,
    Chain,
}

#[hegel::test(print_blob = true)]
fn demanded_chain_survives_unrelated_scalar_assignments(tc: hegel::TestCase) {
    struct Capture(Vec<Noise>);
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let def = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "run")
                .expect("fixture function");
            let mut body = tcx.mir_promoted(def).0.borrow().clone();
            let source_info = body.basic_blocks[START_BLOCK].terminator().source_info;
            let mut statements = Vec::new();
            let declaration = body.local_decls[Local::from_usize(1)].clone();
            let mut previous = Local::from_usize(1);
            for noise in &self.0 {
                let local = body.local_decls.push(declaration.clone());
                statements.push(Statement::new(
                    source_info,
                    StatementKind::Assign(Box::new((
                        Place::from(local),
                        Rvalue::Use(Operand::Copy(Place::from(previous)), WithRetag::No),
                    ))),
                ));
                previous = local;
                let local = body.local_decls.push(declaration.clone());
                let source = match noise {
                    Noise::Input => Local::from_usize(1),
                    Noise::Chain => previous,
                };
                statements.push(Statement::new(
                    source_info,
                    StatementKind::Assign(Box::new((
                        Place::from(local),
                        Rvalue::Use(Operand::Copy(Place::from(source)), WithRetag::No),
                    ))),
                ));
            }
            statements.push(Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(RETURN_PLACE),
                    Rvalue::Use(Operand::Copy(Place::from(previous)), WithRetag::No),
                ))),
            ));
            body.basic_blocks =
                BasicBlocks::new(IndexVec::from_raw(vec![BasicBlockData::new_stmts(
                    statements,
                    Some(Terminator {
                        attributes: Default::default(),
                        source_info,
                        kind: TerminatorKind::Return,
                    }),
                    false,
                )]));
            with_graph(|mut graph| {
                let capture = states::analyze(tcx, &body, &mut graph, &[], &Sources::default())
                    .expect("capture");
                assert_eq!(capture.work.statement_dispatches, self.0.len() * 2 + 1);
                assert_eq!(capture.work.statement_transfers, self.0.len() + 1);
                let [returned] = capture.observations.contracts.returns.as_slice() else {
                    panic!("one return")
                };
                match graph[returned.value] {
                    ExprNode::Argument(0) => {}
                    ref actual => panic!("unexpected returned expression: {actual:?}"),
                }
            });
            rustc_driver::Compilation::Stop
        }
    }
    let count = tc.draw(hegel::generators::default::<Vec<Noise>>());
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("capture.rs");
    std::fs::write(&source, "pub fn run(value: u32) -> u32 { value }").expect("fixture source");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        source.display().to_string(),
    ];
    let status = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut Capture(count))
    });
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[hegel::test(print_blob = true)]
fn alias_mutation_preserves_all_diagnostics_with_scalar_noise(tc: hegel::TestCase) {
    let noise = tc.draw(hegel::generators::default::<Vec<u8>>());
    let noise: String = noise
        .into_iter()
        .map(|value| format!("let _noise = index == {value};"))
        .collect();
    let prefix =
        "pub fn run(values: &mut Vec<u8>, index: usize) -> Option<u8> { if index < values.len() {";
    let suffix = "values.clear(); Some(values[index]) } else { None } }";
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("capture.rs");
    let analyze = |body: String| {
        std::fs::write(&source, &body).expect("fixture source");
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .args([
                "--format=json",
                "--crate-type=lib",
                "--edition=2024",
                "--emit=metadata",
            ])
            .arg("--out-dir")
            .arg(directory.path())
            .arg(&source)
            .output()
            .expect("analysis");
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
        let mut findings: Vec<serde_json::Value> = String::from_utf8(output.stdout)
            .expect("UTF-8")
            .lines()
            .map(|line| serde_json::from_str(line).expect("finding"))
            .collect();
        let mut embedded_sources = 0;
        for finding in &mut findings {
            let related = finding["related"]
                .as_array_mut()
                .expect("related locations");
            for location in related {
                let input = &mut location["input"];
                if input["name"] == source.to_string_lossy().as_ref() {
                    assert_eq!(input["text"], body);
                    input["text"] = serde_json::Value::String(String::new());
                    embedded_sources += 1;
                }
            }
        }
        assert!(embedded_sources > 0);
        findings
    };
    let baseline = analyze(format!("{prefix}{}{suffix}", " ".repeat(noise.len())));
    let actual = analyze(format!("{prefix}{noise}{suffix}"));
    assert_eq!(actual, baseline);
    let invalidated: Vec<_> = actual
        .iter()
        .filter(|finding| finding["rule"] == "invalidated-validation")
        .collect();
    assert_eq!(invalidated.len(), 1);
}

#[hegel::test(print_blob = true)]
fn scalar_noise_preserves_full_direct_summary_in_mixed_control_flow(tc: hegel::TestCase) {
    struct Capture(Vec<Noise>);
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let def = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "run")
                .expect("fixture function");
            let baseline = tcx.mir_promoted(def).0.borrow().clone();
            let mut noisy = baseline.clone();
            let source_info = noisy.basic_blocks[START_BLOCK].terminator().source_info;
            let declaration = noisy.local_decls[Local::from_usize(2)].clone();
            let mut statements = Vec::new();
            for _ in &self.0 {
                let local = noisy.local_decls.push(declaration.clone());
                statements.push(Statement::new(
                    source_info,
                    StatementKind::Assign(Box::new((
                        Place::from(local),
                        Rvalue::Use(
                            Operand::Copy(Place::from(Local::from_usize(2))),
                            WithRetag::No,
                        ),
                    ))),
                ));
            }
            statements.append(&mut noisy.basic_blocks.as_mut()[START_BLOCK].statements);
            noisy.basic_blocks.as_mut()[START_BLOCK].statements = statements;
            with_graph(|mut graph| {
                let baseline_capture =
                    states::analyze(tcx, &baseline, &mut graph, &[], &Sources::default())
                        .expect("baseline capture");
                let left = graph
                    .freeze(baseline_capture.observations.contracts)
                    .expect("baseline summary");
                let noisy_capture =
                    states::analyze(tcx, &noisy, &mut graph, &[], &Sources::default())
                        .expect("noisy capture");
                let right = graph
                    .freeze(noisy_capture.observations.contracts)
                    .expect("noisy summary");
                assert_eq!(
                    noisy_capture.work.statement_dispatches,
                    baseline_capture.work.statement_dispatches + self.0.len()
                );
                assert_eq!(
                    noisy_capture.work.statement_transfers,
                    baseline_capture.work.statement_transfers
                );
                let left = graph.summaries[left];
                let right = graph.summaries[right];
                assert!(graph.summaries.returns.len(left.returns) > 0);
                assert!(graph.summaries.calls.len(left.calls) > 0);
                assert!(left.inspections == right.inspections);
                assert!(left.escapes == right.escapes);
                assert!(left.escaped_arguments == right.escaped_arguments);
                assert!(left.loops == right.loops);
                assert!(left.requirements == right.requirements);
                assert!(left.calls == right.calls);
                assert!(left.mutations == right.mutations);
                assert!(left.output == right.output);
                assert!(left.returns == right.returns);
                assert!(left.checks == right.checks);
                assert!(left.protocol_checks == right.protocol_checks);
                assert!(left.protocol_returns == right.protocol_returns);
                assert!(left.constructions == right.constructions);
                assert!(left.behavior == right.behavior);
            });
            rustc_driver::Compilation::Stop
        }
    }
    let noise = tc.draw(hegel::generators::default::<Vec<Noise>>());
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("mixed.rs");
    std::fs::write(&source, "pub fn run(value: &mut Option<u32>, index: u32) -> u32 { if value.is_none() { *value = Some(index); } value.take().unwrap_or(index) }").expect("fixture source");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        source.display().to_string(),
    ];
    let status = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(&args, &mut Capture(noise))
    });
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}
