#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use std::fmt::Write;

use rustc_middle::mir::{Operand, Place, Rvalue, StatementKind, VarDebugInfoContents, WithRetag};
use rustc_middle::ty::TyCtxt;
use shapelint_driver::contracts::graph::with_graph;
use shapelint_driver::{analysis, diagnostics, states};

#[derive(Debug)]
struct Measurement {
    work: states::Work,
    blocks: usize,
    findings: usize,
}

fn borrowed_clone_work(text: &str) -> Measurement {
    struct Capture(Option<Measurement>);
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
                    .filter(|finding| match finding.evidence {
                        shapelint::CompilerEvidence::BorrowedClone { .. } => true,
                        _ => false,
                    })
                    .count();
                let measurement = Measurement {
                    work: capture.work,
                    blocks: body.basic_blocks.len(),
                    findings,
                };
                measurement
            }));
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("fixture directory");
    let path = directory.path().join("scaling.rs");
    std::fs::write(&path, text).expect("fixture source");
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
    let mut capture = Capture(None);
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut capture));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
    capture.0.expect("analysis callback ran")
}

#[test]
fn handle_clones_index_body_calls_once() {
    let measurements = [8, 16, 32].map(|count| {
        let mut source = String::from("pub fn run(value: &std::sync::Arc<String>) {");
        for index in 0..count {
            writeln!(source, "let copy_{index} = std::sync::Arc::clone(value); let _length_{index} = copy_{index}.len();")
                .expect("clone source");
        }
        source.push('}');
        let measurement = borrowed_clone_work(&source);
        assert_eq!(measurement.findings, 0);
        assert_eq!(measurement.work.clone_call_block_visits, measurement.blocks);
        assert_eq!(measurement.work.clone_call_set_checks, count);
        eprintln!("handle clones {count}: {measurement:?}");
        measurement
    });
    let [small, medium, large] = &measurements;
    assert_eq!(
        measurements
            .each_ref()
            .map(|sample| sample.work.clone_call_block_visits),
        [42, 82, 162]
    );
    assert_eq!(
        medium.work.clone_call_set_checks,
        2 * small.work.clone_call_set_checks
    );
    assert_eq!(
        large.work.clone_call_set_checks,
        2 * medium.work.clone_call_set_checks
    );
    assert!(large.work.clone_call_block_visits <= 2 * medium.work.clone_call_block_visits);
    assert!(large.work.clone_use_visits <= 2 * medium.work.clone_use_visits);
}

#[test]
fn buffer_clones_resolve_arguments_directly() {
    let measurements = [8, 16, 32].map(|count| {
        let mut source = String::from("pub fn run(");
        for index in 1..count {
            write!(source, "_unused_{index}: u8,").expect("argument source");
        }
        source.push_str("value: &String) {");
        for index in 0..count {
            writeln!(
                source,
                "let copy_{index} = value.clone(); let _length_{index} = copy_{index}.len();"
            )
            .expect("clone source");
        }
        source.push('}');
        let measurement = borrowed_clone_work(&source);
        assert_eq!(measurement.findings, count);
        assert_eq!(measurement.work.clone_argument_lookups, count);
        assert_eq!(measurement.work.clone_call_block_visits, 0);
        eprintln!("buffer clones and arguments {count}: {measurement:?}");
        measurement
    });
    let [small, medium, large] = &measurements;
    assert_eq!(
        measurements
            .each_ref()
            .map(|sample| sample.work.clone_argument_lookups),
        [8, 16, 32]
    );
    assert_eq!(
        medium.work.clone_argument_lookups,
        2 * small.work.clone_argument_lookups
    );
    assert_eq!(
        large.work.clone_argument_lookups,
        2 * medium.work.clone_argument_lookups
    );
    assert!(medium.work.clone_use_visits <= 2 * small.work.clone_use_visits);
    assert!(large.work.clone_use_visits <= 2 * medium.work.clone_use_visits);
}

#[test]
fn buffer_clones_share_origin_resolution() {
    let measurements = [8, 16, 32].map(|count| {
        let mut source = String::from("pub fn run(value: &String) { let alias_0 = value;");
        for index in 1..count {
            writeln!(source, "let alias_{index} = alias_{};", index - 1).expect("alias source");
        }
        for index in 0..count {
            writeln!(
                source,
                "let copy_{index} = alias_{}.clone(); let _length_{index} = copy_{index}.len();",
                count - 1
            )
            .expect("clone source");
        }
        source.push('}');
        let measurement = borrowed_clone_work(&source);
        assert_eq!(measurement.findings, count);
        assert_eq!(measurement.work.clone_argument_lookups, count);
        assert_eq!(measurement.work.clone_call_block_visits, 0);
        eprintln!("buffer clones and aliases {count}: {measurement:?}");
        measurement
    });
    let [small, medium, large] = &measurements;
    let first_growth = medium.work.clone_origin_lookups - small.work.clone_origin_lookups;
    let second_growth = large.work.clone_origin_lookups - medium.work.clone_origin_lookups;
    assert!(second_growth <= 2 * first_growth);
    assert!(medium.work.clone_use_visits <= 2 * small.work.clone_use_visits);
    assert!(large.work.clone_use_visits <= 2 * medium.work.clone_use_visits);
}

#[derive(Debug, hegel::DefaultGenerator)]
enum CloneUse {
    BufferRead,
    ReassignedOrigin,
    BufferEscape,
    HandleRead,
    HandleOtherCall,
    HandleEscape,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct CloneCase {
    aliases: Vec<()>,
    usage: CloneUse,
}

#[hegel::test(print_blob = true)]
fn clone_aliases_preserve_origin_and_escape_checks(tc: hegel::TestCase) {
    let CloneCase { aliases, usage } = tc.draw(hegel::generators::default::<CloneCase>());
    struct Example {
        prefix: &'static str,
        receiver: &'static str,
        consumer: &'static str,
        expected: usize,
    }
    let Example {
        prefix,
        receiver,
        consumer,
        expected,
    } = match usage {
        CloneUse::BufferRead => Example {
            prefix: "pub fn run(value: &String) {",
            receiver: "value",
            consumer: "let _length = copy.len();",
            expected: 1,
        },
        CloneUse::ReassignedOrigin => Example {
            prefix: "pub fn run(value: &String, other: &String, flag: bool) { let mut receiver = value; if flag { receiver = other; }",
            receiver: "receiver",
            consumer: "let _length = copy.len();",
            expected: 0,
        },
        CloneUse::BufferEscape => Example {
            prefix: "fn consume(_: String) {} pub fn run(value: &String) {",
            receiver: "value",
            consumer: "consume(copy);",
            expected: 0,
        },
        CloneUse::HandleRead => Example {
            prefix: "pub fn run(value: &std::sync::Arc<String>) {",
            receiver: "value",
            consumer: "let _length = copy.len();",
            expected: 1,
        },
        CloneUse::HandleOtherCall => Example {
            prefix: "pub fn run(value: &std::sync::Arc<String>) {",
            receiver: "value",
            consumer: "let _length = copy.len(); std::hint::black_box(());",
            expected: 0,
        },
        CloneUse::HandleEscape => Example {
            prefix: "fn consume(_: std::sync::Arc<String>) {} pub fn run(value: &std::sync::Arc<String>) {",
            receiver: "value",
            consumer: "consume(copy);",
            expected: 0,
        },
    };
    let mut source = String::from(prefix);
    let mut receiver = String::from(receiver);
    let aliases = aliases.iter().enumerate();
    for (index, ()) in aliases {
        let alias = format!("alias_{index}");
        writeln!(source, "let {alias} = {receiver};").expect("alias source");
        receiver = alias;
    }
    writeln!(source, "let copy = {receiver}.clone(); {consumer} }}").expect("clone source");
    let measurement = borrowed_clone_work(&source);
    assert_eq!(measurement.findings, expected, "{source}");
}

#[test]
fn cyclic_clone_origins_remain_unknown_and_terminate() {
    struct Capture;
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
            let first = body
                .var_debug_info
                .iter()
                .find_map(|info| match (&info.value, info.name.as_str()) {
                    (VarDebugInfoContents::Place(place), "first") => Some(place.local),
                    _ => None,
                })
                .expect("first alias");
            let second = body
                .var_debug_info
                .iter()
                .find_map(|info| match (&info.value, info.name.as_str()) {
                    (VarDebugInfoContents::Place(place), "second") => Some(place.local),
                    _ => None,
                })
                .expect("second alias");
            let mut replacements = 0;
            for block in body.basic_blocks.as_mut() {
                for statement in &mut block.statements {
                    if let StatementKind::Assign(assignment) = &mut statement.kind
                        && assignment.0.local == first
                    {
                        assignment.1 =
                            Rvalue::Use(Operand::Copy(Place::from(second)), WithRetag::No);
                        replacements += 1;
                    }
                }
            }
            assert_eq!(replacements, 1);
            let mut work = states::Work::default();
            let findings = shapelint_driver::transfers::borrowed_clones(
                tcx,
                &body,
                &diagnostics::Sources::default(),
                &mut work,
            );
            assert!(findings.is_empty());
            assert_eq!(work.clone_argument_lookups, 0);
            assert!(work.clone_origin_lookups > 0);
            assert!(work.clone_origin_lookups <= work.clone_use_visits);
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("fixture directory");
    let path = directory.path().join("cycle.rs");
    std::fs::write(
        &path,
        "pub fn run(value: &String) { let first = value; let second = first; let copy_a = second.clone(); let _length_a = copy_a.len(); let copy_b = second.clone(); let _length_b = copy_b.len(); }",
    )
    .expect("fixture source");
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
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Capture));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}
