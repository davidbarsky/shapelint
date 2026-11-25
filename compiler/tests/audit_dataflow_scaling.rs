#![feature(rustc_private)]

//! Semantic controls for isolated work counters in `artifacts/exhaustive-audit/`.

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use std::fmt::Write;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::Mutability;
use rustc_middle::ty::{Ty, TyCtxt};
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
use shapelint_driver::contracts::{Order, Summary};
use shapelint_driver::protocols::{self, Flow};
use shapelint_driver::values::{Captures, with_values};
use shapelint_driver::{analysis, diagnostics};

#[derive(Debug)]
struct SwitchMeasurement {
    blocks: usize,
    findings: usize,
    statement_dispatches: usize,
    block_transfers: usize,
    discriminant_index_visits: usize,
    discriminant_index_lookups: usize,
}

// shapelint: allow(identity-string) The source string is the rustc fixture identity under test.
fn analyze_switch_fixture(source: &str) -> SwitchMeasurement {
    struct Capture(Option<SwitchMeasurement>);

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
            let body = tcx.mir_promoted(def).0.borrow();
            self.0 = Some(with_graph(|mut graph| {
                let capture = analysis::analyze(
                    tcx,
                    def,
                    &body,
                    &mut graph,
                    &[],
                    &diagnostics::Sources::default(),
                )
                .expect("MIR analysis");
                let findings = capture
                    .findings
                    .iter()
                    .filter(|finding| {
                        let shapelint::CompilerEvidence::BorrowedClone { .. } = finding.evidence
                        else {
                            return false;
                        };
                        true
                    })
                    .count();
                SwitchMeasurement {
                    blocks: body.basic_blocks.len(),
                    findings,
                    statement_dispatches: capture.work.statement_dispatches,
                    block_transfers: capture.work.block_transfers,
                    discriminant_index_visits: capture.work.discriminant_index_visits,
                    discriminant_index_lookups: capture.work.discriminant_index_lookups,
                }
            }));
            rustc_driver::Compilation::Stop
        }
    }

    let mut capture = Capture(None);
    run_fixture(source, &mut capture);
    capture.0.expect("analysis callback ran")
}

#[test]
fn unknown_select_chain_projects_away_irrelevant_prefix_guards() {
    const DEPTH: usize = 64;

    struct Analyze;
    impl rustc_driver::Callbacks for Analyze {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let owner = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "run")
                .expect("run")
                .to_def_id();
            with_graph(|mut graph| {
                let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                let ready = graph.intern_flow(Flow::Ready).expect("ready");
                let dirty = graph
                    .intern_flow(Flow::Dirty {
                        def: owner,
                        span: tcx.def_span(owner),
                    })
                    .expect("dirty");
                let mut flow = dirty;
                for index in 0..DEPTH {
                    let argument = graph
                        .intern_expr(ExprNode::Argument(index))
                        .expect("argument");
                    let condition = graph
                        .intern_condition(ConditionNode::Compare(Order::Equal, argument, zero))
                        .expect("condition");
                    // The no branch is the previous chain.  Each branch is
                    // unknown, but the descendant query's projection cannot
                    // retain the outer condition because it is not in that
                    // descendant's support.
                    flow = graph
                        .intern_flow(Flow::Select(condition, ready, flow))
                        .expect("select");
                }
                let mut summary = Summary::default();
                summary.protocol_checks.push(protocols::Obligation {
                    name: rustc_span::Symbol::intern("durability"),
                    span: tcx.def_span(owner),
                    flow,
                    guards: Default::default(),
                });
                let summary = graph.freeze(summary).expect("freeze summary");
                let summaries = FxHashMap::from_iter([(owner, summary)]);
                let findings = protocols::findings(
                    tcx,
                    &mut graph,
                    &summaries,
                    &diagnostics::Sources::default(),
                )
                .expect("protocol findings");
                // The dirty leaf remains semantically reachable through the
                // all-false path, and the graph has exactly one node per
                // select.  This is a representation/cardinality witness,
                // not a query-work counter (the query engine is private).
                assert_eq!(findings.len(), 1);
                assert_eq!(graph.flows().count(), DEPTH + 2);
            });
            rustc_driver::Compilation::Stop
        }
    }

    run_fixture("pub fn run() {}", &mut Analyze);
}

#[test]
fn enum_switch_keeps_one_clone_finding_per_variant() {
    let observations = [8, 16, 32].map(|variants| {
        let measurement = analyze_switch_fixture(&enum_switch_source(variants));
        assert_eq!(measurement.findings, variants);
        assert!(measurement.blocks >= variants);
        assert!(measurement.statement_dispatches >= variants);
        assert!(measurement.block_transfers >= variants);
        assert!(measurement.discriminant_index_visits > 0);
        assert!(measurement.discriminant_index_lookups > 0);
        eprintln!("ADT switch with {variants} variants: {measurement:?}");
        measurement
    });
    assert!(observations[1].blocks >= observations[0].blocks);
    assert!(observations[2].blocks >= observations[1].blocks);
    for pair in observations.windows(2) {
        assert!(
            pair[1].discriminant_index_visits <= 2 * pair[0].discriminant_index_visits,
            "discriminant index construction must be linear: {observations:?}"
        );
        assert!(
            pair[1].discriminant_index_lookups <= 2 * pair[0].discriminant_index_lookups,
            "discriminant index lookup work must be linear: {observations:?}"
        );
    }
}

fn enum_switch_source(variants: usize) -> String {
    let mut source = String::from("pub enum Choice {");
    for index in 0..variants {
        writeln!(source, "V{index},").expect("variant source");
    }
    source.push_str("}\npub fn run(choice: Choice, value: &String) { match choice {");
    for index in 0..variants {
        writeln!(
            source,
            "Choice::V{index} => {{ let copy_{index} = value.clone(); let _len_{index} = copy_{index}.len(); }},"
        )
        .expect("switch source");
    }
    source.push_str("}}");
    source
}

#[test]
fn repeated_restore_of_a_deep_reference_preserves_the_rustc_type() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        // shapelint: allow(literal-test-cases) These sizes form one cross-size scaling comparison.
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            for size in [8, 16, 32] {
                let mut ty = tcx.types.u8;
                for _ in 0..size {
                    ty = Ty::new_ref(tcx, tcx.lifetimes.re_erased, ty, Mutability::Not);
                }
                with_values(|values| {
                    let mut captures = Captures::new(tcx, values.share());
                    let id = captures.capture_type(ty).expect("deep reference capture");
                    let mut restorer = values.restorer(tcx);
                    let before = restorer.restore_visits;
                    for _ in 0..size {
                        assert_eq!(restorer.restore_type(id), Some(ty));
                    }
                    let after = restorer.restore_visits;
                    eprintln!(
                        "restore deep reference depth={size} repeats={size}: before={before} after={after} visits={}",
                        after - before
                    );
                    assert_eq!(after - before, 2 * size + 2);
                });
            }
            rustc_driver::Compilation::Stop
        }
    }
    run_fixture("pub fn run<T>(_value: T) {}", &mut Capture);
}

// shapelint: allow(identity-string) The source string is the rustc fixture identity under test.
fn run_fixture(source: &str, callbacks: &mut (impl rustc_driver::Callbacks + Send)) {
    let directory = tempfile::tempdir().expect("fixture directory");
    let path = directory.path().join("values.rs");
    std::fs::write(&path, source).expect("fixture source");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        path.display().to_string(),
    ];
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, callbacks));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}
