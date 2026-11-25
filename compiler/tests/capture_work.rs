#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_errors;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_transform;
extern crate rustc_ty_utils;

use rustc_index::IndexVec;
use rustc_middle::mir::{
    BasicBlock, BasicBlockData, BasicBlocks, Local, Operand, Place, RETURN_PLACE, Rvalue,
    START_BLOCK, Statement, StatementKind, SwitchTargets, Terminator, TerminatorKind, WithRetag,
};
use rustc_middle::ty::TyCtxt;
use shapelint_driver::contracts::graph::{ExprNode, with_graph};
use shapelint_driver::diagnostics::Sources;
use shapelint_driver::states;

#[derive(Debug, Default, PartialEq, Eq)]
struct Nodes {
    arguments: usize,
    numbers: usize,
    predicates: usize,
    selections: usize,
    other: usize,
}

fn run(mut callback: impl rustc_driver::Callbacks + Send) {
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("capture.rs");
    std::fs::write(&source, "pub fn run(choice:u8,value:u8)->u8{value}").expect("fixture source");
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
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut callback));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[test]
fn reverse_fanin_captures_each_block_once_without_partial_join_graphs() {
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
            let original = tcx.mir_promoted(def).0.borrow().clone();
            let source_info = original.basic_blocks[START_BLOCK].terminator().source_info;
            let assignment = Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(RETURN_PLACE),
                    Rvalue::Use(
                        Operand::Copy(Place::from(Local::from_usize(2))),
                        WithRetag::No,
                    ),
                ))),
            );
            let capture = |branches: usize| {
                let mut body = original.clone();
                let join = BasicBlock::from_usize(branches + 1);
                let mut blocks = vec![BasicBlockData::new_stmts(
                    vec![assignment.clone()],
                    Some(Terminator {
                        attributes: Default::default(),
                        source_info,
                        kind: TerminatorKind::SwitchInt {
                            discr: Operand::Copy(Place::from(Local::from_usize(1))),
                            targets: SwitchTargets::new(
                                (0..branches - 1).map(|value| {
                                    (value as u128, BasicBlock::from_usize(value + 1))
                                }),
                                BasicBlock::from_usize(branches),
                            ),
                        },
                    }),
                    false,
                )];
                for _ in 0..branches {
                    blocks.push(BasicBlockData::new_stmts(
                        vec![assignment.clone()],
                        Some(Terminator {
                            attributes: Default::default(),
                            source_info,
                            kind: TerminatorKind::Goto { target: join },
                        }),
                        false,
                    ));
                }
                blocks.push(BasicBlockData::new_stmts(
                    vec![assignment.clone()],
                    Some(Terminator {
                        attributes: Default::default(),
                        source_info,
                        kind: TerminatorKind::Return,
                    }),
                    false,
                ));
                body.basic_blocks = BasicBlocks::new(IndexVec::from_raw(blocks));
                let expected_blocks = body.basic_blocks.len();
                let expected_statements: usize = body
                    .basic_blocks
                    .iter()
                    .map(|block| block.statements.len())
                    .sum();
                with_graph(|mut graph| {
                    let capture = states::analyze(tcx, &body, &mut graph, &[], &Sources::default())
                        .expect("capture final fanin");
                    assert_eq!(capture.work.block_transfers, expected_blocks);
                    assert_eq!(capture.work.statement_dispatches, expected_statements);
                    assert_eq!(capture.work.merges, branches - 1);
                    assert!(capture.work.attachments > 0);
                    let expressions = graph.expressions();
                    let mut nodes = Nodes::default();
                    for expression in expressions {
                        match expression {
                            ExprNode::Argument(_) => nodes.arguments += 1,
                            ExprNode::Number(_) => nodes.numbers += 1,
                            ExprNode::Test(_) => nodes.predicates += 1,
                            ExprNode::Select(..) => nodes.selections += 1,
                            _ => nodes.other += 1,
                        }
                    }
                    nodes
                })
            };
            let small = capture(16);
            let medium = capture(32);
            let large = capture(48);
            let first_growth = Nodes {
                arguments: medium.arguments - small.arguments,
                numbers: medium.numbers - small.numbers,
                predicates: medium.predicates - small.predicates,
                selections: medium.selections - small.selections,
                other: medium.other - small.other,
            };
            let second_growth = Nodes {
                arguments: large.arguments - medium.arguments,
                numbers: large.numbers - medium.numbers,
                predicates: large.predicates - medium.predicates,
                selections: large.selections - medium.selections,
                other: large.other - medium.other,
            };
            assert_eq!(
                first_growth, second_growth,
                "equal fanin increments must add equal node-family work: {small:?}, {medium:?}, {large:?}"
            );
            rustc_driver::Compilation::Stop
        }
    }
    run(Capture);
}

#[test]
fn repeated_nested_loop_exits_forward_the_same_states_as_full_transfers() {
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
                .unwrap();
            let original = tcx.mir_promoted(def).0.borrow().clone();
            let source_info = original.basic_blocks[START_BLOCK].terminator().source_info;
            let bb = BasicBlock::from_usize;
            let place = |local| Place::from(Local::from_usize(local));
            let assign = |destination, source| {
                Statement::new(
                    source_info,
                    StatementKind::Assign(Box::new((
                        place(destination),
                        Rvalue::Use(Operand::Copy(place(source)), WithRetag::No),
                    ))),
                )
            };
            let go = |target| TerminatorKind::Goto { target: bb(target) };
            let switch = |local, zero, other| TerminatorKind::SwitchInt {
                discr: Operand::Copy(place(local)),
                targets: SwitchTargets::new([(0, bb(zero))].into_iter(), bb(other)),
            };
            let block = |statements, kind| {
                BasicBlockData::new_stmts(
                    statements,
                    Some(Terminator {
                        source_info,
                        attributes: Default::default(),
                        kind,
                    }),
                    false,
                )
            };
            let exit = bb(4);
            let blocks = vec![
                block(vec![assign(0, 2)], go(1)),
                block(vec![], switch(2, 5, 2)),
                block(vec![], switch(1, 3, 4)),
                block(vec![assign(1, 2)], go(2)),
                block(vec![Statement::new(source_info, StatementKind::Nop)], go(1)),
                block(vec![], TerminatorKind::Return),
            ];
            with_graph(|mut graph| {
                let mut body = original.clone();
                body.basic_blocks = BasicBlocks::new(IndexVec::from_raw(blocks.clone()));
                let forwarded = states::analyze(tcx, &body, &mut graph, &[], &Sources::default())
                    .expect("capture transparent exit");
                let mut reference = blocks;
                // The unreachable predecessor disables forwarding without affecting any input.
                reference.push(block(vec![], TerminatorKind::Goto { target: exit }));
                body.basic_blocks = BasicBlocks::new(IndexVec::from_raw(reference));
                let full = states::analyze(tcx, &body, &mut graph, &[], &Sources::default())
                    .expect("capture full transfers");
                assert!(forwarded.work.nested_exit_forwards > 0);
                assert_eq!(full.work.nested_exit_forwards, 0);
                assert_eq!(
                    forwarded.work.block_transfers + forwarded.work.nested_exit_forwards,
                    full.work.block_transfers
                );
                assert_eq!(forwarded.work.merges, full.work.merges);
                assert!(!forwarded.observations.contracts.returns.is_empty());
                assert_eq!(
                    graph.freeze(forwarded.observations.contracts).unwrap(),
                    graph.freeze(full.observations.contracts).unwrap()
                );
            });
            rustc_driver::Compilation::Stop
        }
    }
    run(Capture);
}

#[test]
fn unequal_paths_execute_a_shared_statement_sequence_only_once() {
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
            let source_info = body.basic_blocks[START_BLOCK].terminator().source_info;
            let assignment = Statement::new(
                source_info,
                StatementKind::Assign(Box::new((
                    Place::from(RETURN_PLACE),
                    Rvalue::Use(
                        Operand::Copy(Place::from(Local::from_usize(2))),
                        WithRetag::No,
                    ),
                ))),
            );
            let paths = 32;
            let join = BasicBlock::from_usize(paths);
            let mut blocks = Vec::new();
            for path in 0..paths {
                let kind = match path + 1 {
                    next if next == paths => TerminatorKind::Goto { target: join },
                    next => TerminatorKind::SwitchInt {
                        discr: Operand::Copy(Place::from(Local::from_usize(1))),
                        targets: SwitchTargets::new(
                            std::iter::once((path as u128, join)),
                            BasicBlock::from_usize(next),
                        ),
                    },
                };
                blocks.push(BasicBlockData::new_stmts(
                    vec![assignment.clone()],
                    Some(Terminator {
                        attributes: Default::default(),
                        source_info,
                        kind,
                    }),
                    false,
                ));
            }
            blocks.push(BasicBlockData::new_stmts(
                vec![assignment; 64],
                Some(Terminator {
                    attributes: Default::default(),
                    source_info,
                    kind: TerminatorKind::Return,
                }),
                false,
            ));
            body.basic_blocks = BasicBlocks::new(IndexVec::from_raw(blocks));
            let expected_blocks = body.basic_blocks.len();
            let expected_statements: usize = body
                .basic_blocks
                .iter()
                .map(|block| block.statements.len())
                .sum();
            with_graph(|mut graph| {
                let capture = states::analyze(tcx, &body, &mut graph, &[], &Sources::default())
                    .expect("capture final ladder join");
                assert_eq!(capture.work.block_transfers, expected_blocks);
                assert_eq!(capture.work.statement_dispatches, expected_statements);
                assert_eq!(capture.work.merges, paths - 1);
            });
            rustc_driver::Compilation::Stop
        }
    }
    run(Capture);
}

#[test]
fn repeated_capture_views_share_canonical_summary_identities() {
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
            let body = tcx.mir_promoted(def).0.borrow().clone();
            let session = shapelint_driver::analysis::Session::new();
            let sources = Sources::default();
            session
                .capture(tcx, def, &body, &[], &sources)
                .expect("first capture");
            session
                .capture(tcx, def, &body, &[], &sources)
                .expect("second capture");
            session.finish(tcx, |graph, analyses| {
                let [first, second] = analyses.as_slice() else {
                    panic!("both captures are retained");
                };
                assert_eq!(first.contracts, second.contracts);
                let summary = graph.summaries[first.contracts];
                assert!(graph.summaries.returns.len(summary.returns) > 0);
            });
            rustc_driver::Compilation::Stop
        }
    }
    run(Capture);
}

#[test]
fn shared_views_reuse_the_first_published_alternative_order() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            use shapelint_driver::contracts::Expr;

            let session = shapelint_driver::analysis::Session::new();
            let (first, count) = session.finish(tcx, |graph, _| {
                let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
                let two = graph.intern_expr(ExprNode::Number(2)).unwrap();
                let alternatives = graph.alternatives([one, two]).unwrap();
                (graph.raise_expr(alternatives), graph.expression_count())
            });
            let (second, after) = session.finish(tcx, |graph, _| {
                let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
                let two = graph.intern_expr(ExprNode::Number(2)).unwrap();
                let alternatives = graph.alternatives([two, one]).unwrap();
                (graph.raise_expr(alternatives), graph.expression_count())
            });
            assert_eq!(
                first,
                Expr::Alternatives(vec![Expr::Number(1), Expr::Number(2)])
            );
            assert_eq!(second, first);
            assert_eq!(after, count);
            rustc_driver::Compilation::Stop
        }
    }
    run(Capture);
}

#[test]
// shapelint: allow(implicit-dependency) The rustc provider signature has no captured context.
fn reentrant_provider_capture_shares_the_session_graph() {
    use rustc_data_structures::steal::Steal;
    use rustc_hir::def_id::{DefId, LocalDefId};
    use rustc_middle::mir::{Body, Promoted};
    use rustc_middle::ty::{self, GenericArgsRef};
    use shapelint_driver::analysis::Session;
    use std::cell::Cell;
    use std::sync::OnceLock;
    use std::sync::atomic::{AtomicBool, Ordering};

    // shapelint: allow(implicit-dependency) The rustc provider signature has no captured context.
    static SESSION: OnceLock<Session> = OnceLock::new();
    // shapelint: allow(implicit-dependency) The rustc provider signature has no captured context.
    static SIBLING: OnceLock<LocalDefId> = OnceLock::new();
    // shapelint: allow(implicit-dependency) The rustc provider signature has no captured context.
    static REENTERED: AtomicBool = AtomicBool::new(false);
    // shapelint: allow(implicit-dependency) The rustc provider signature has no captured context.
    thread_local! { static DEPTH: Cell<usize> = const { Cell::new(0) }; }

    fn promoted<'tcx>(
        tcx: TyCtxt<'tcx>,
        def: LocalDefId,
    ) -> (
        &'tcx Steal<Body<'tcx>>,
        &'tcx Steal<IndexVec<Promoted, Body<'tcx>>>,
    ) {
        let mut providers = rustc_middle::util::Providers::default();
        rustc_mir_transform::provide(&mut providers);
        let result = (providers.queries.mir_promoted)(tcx, def);
        let mut body = result.0.borrow().clone();
        if tcx.item_name(def.to_def_id()).as_str() == "run" {
            for block in body.basic_blocks.as_mut() {
                let terminator = block.terminator_mut();
                if let TerminatorKind::Call { func, .. } = &mut terminator.kind {
                    let ty::FnDef(value, _) = func.ty(&body.local_decls, tcx).kind() else {
                        panic!("fixture calls value directly");
                    };
                    let args = ty::Binder::dummy([tcx.types.u16]);
                    let ty = ty::Ty::new_fn_def(tcx, *value, args);
                    *func = Operand::zero_sized_constant(ty, terminator.source_info.span);
                }
            }
        }
        DEPTH.with(|depth| {
            depth.set(depth.get() + 1);
            SESSION
                .get()
                .unwrap()
                .capture(tcx, def, &body, &[], &Sources::default())
                .expect("MIR capture");
            depth.set(depth.get() - 1);
        });
        result
    }

    fn resolve<'tcx>(
        tcx: TyCtxt<'tcx>,
        key: ty::PseudoCanonicalInput<'tcx, (DefId, GenericArgsRef<'tcx>)>,
    ) -> Result<Option<ty::Instance<'tcx>>, rustc_errors::ErrorGuaranteed> {
        if DEPTH.with(|depth| depth.get() > 0) && tcx.item_name(key.value.0).as_str() == "value" {
            REENTERED.store(true, Ordering::SeqCst);
            let _ = tcx.mir_promoted(*SIBLING.get().unwrap());
        }
        let mut providers = rustc_middle::query::Providers::default();
        rustc_ty_utils::provide(&mut providers);
        (providers.resolve_instance_raw)(tcx, key)
    }

    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn config(&mut self, config: &mut rustc_interface::interface::Config) {
            config.override_queries = Some(|_, providers| {
                providers.queries.mir_promoted = promoted;
                providers.queries.resolve_instance_raw = resolve;
            });
            config.opts.incremental = None;
        }
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let mut run = None;
            let mut sibling = None;
            for def in tcx.hir_body_owners() {
                match tcx.item_name(def.to_def_id()).as_str() {
                    "run" => run = Some(def),
                    "sibling" => sibling = Some(def),
                    _ => {}
                }
            }
            let run = run.expect("run function");
            let sibling = sibling.expect("sibling function");
            SESSION
                .set(Session::new())
                .unwrap_or_else(|_| panic!("one test session"));
            SIBLING.set(sibling).expect("one sibling");
            let _ = tcx.mir_promoted(run);
            assert!(
                REENTERED.load(Ordering::SeqCst),
                "nested provider was not entered during capture"
            );
            SESSION.get().unwrap().finish(tcx, |graph, analyses| {
                let definitions: Vec<_> = analyses.iter().map(|analysis| analysis.def).collect();
                assert!(definitions.contains(&run));
                assert!(definitions.contains(&sibling));
                assert_eq!(definitions.len(), 2);
                for analysis in analyses {
                    let summary = graph.summaries[analysis.contracts];
                    assert!(graph.summaries.returns.len(summary.returns) > 0);
                }
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("reentrant.rs");
    std::fs::write(&source, "pub fn run() -> u32 { value::<u8>() } pub fn value<T>() -> u32 { 1 } pub fn sibling() -> u32 { 2 }")
        .expect("fixture source");
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
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Capture));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[test]
fn comparison_contexts_remain_usable_across_session_views() {
    use shapelint_driver::contracts::graph::{ConditionNode, Graph};
    use shapelint_driver::contracts::{Order, Truth};

    fn prove<'g>(graph: &mut Graph<'g>, threshold: u128) -> Truth {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let last = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let bound = graph.intern_expr(ExprNode::Number(5)).unwrap();
        let threshold = graph.intern_expr(ExprNode::Number(threshold)).unwrap();
        let bridge = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, first, last))
            .unwrap();
        let boundary = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, bound, first))
            .unwrap();
        let guards = graph
            .condition_sequences
            .from_iter([bridge, boundary])
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, threshold, last))
            .unwrap();
        graph.truth(required, &guards).unwrap()
    }

    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let session = shapelint_driver::analysis::Session::new();
            let first = session.finish(tcx, |graph, _| prove(graph, 4));
            let second = session.finish(tcx, |graph, _| prove(graph, 3));
            assert_eq!(first, Truth::Proven);
            assert_eq!(second, Truth::Proven);
            rustc_driver::Compilation::Stop
        }
    }
    run(Capture);
}
