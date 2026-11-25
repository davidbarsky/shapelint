#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use shapelint::{CheckOutcome, CompilerEvidence};
use shapelint_driver::analysis::Analysis;
use shapelint_driver::calls::{Dispatch, Instance};
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, TargetNode, with_graph};
use shapelint_driver::contracts::{self, Check, Order, Return, Summary};
use shapelint_driver::{artifacts, callers, pipeline};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Topology {
    SelfCall,
    Mutual,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Invocation {
    Base,
    Loop,
    GuardedLoop,
    ClosedPaths,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct Case {
    topology: Topology,
    invocation: Invocation,
}

#[hegel::test(print_blob = true)]
fn recursive_return_evidence_keeps_the_fixed_point_and_incoming_facts(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Case>());
    struct Analyze(Case);
    impl rustc_driver::Callbacks for Analyze {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let definitions: Vec<_> = tcx.hir_body_owners().collect();
            let root = definitions
                .iter()
                .copied()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "run")
                .expect("root");
            let first = definitions
                .iter()
                .copied()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "first")
                .expect("first");
            let second = definitions
                .iter()
                .copied()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "second")
                .expect("second");
            with_graph(|mut graph| {
                let analyses: Vec<_> = definitions
                    .iter()
                    .map(|def| Analysis {
                        def: *def,
                        span: tcx.def_span(*def),
                        regions: None,
                        contracts: {
                            let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
                            let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
                            let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
                            let enabled = graph
                                .intern_condition(ConditionNode::Compare(
                                    Order::Equal,
                                    argument,
                                    one,
                                ))
                                .unwrap();
                            let disabled = graph.negate(enabled).unwrap();
                            let mut summary = Summary::default();
                            match *def {
                                def if def == root => {
                                    let value = match self.0.invocation {
                                        Invocation::Base => one,
                                        Invocation::Loop | Invocation::GuardedLoop => zero,
                                        Invocation::ClosedPaths => argument,
                                    };
                                    let instance = graph
                                        .values
                                        .intern_instance(&Instance {
                                            def: first.to_def_id(),
                                            args: Vec::new(),
                                            dispatch: Dispatch::Item,
                                        })
                                        .unwrap();
                                    let args =
                                        graph.expression_sequences.from_iter([value]).unwrap();
                                    let returned = graph
                                        .intern_condition(ConditionNode::Returned(
                                            TargetNode::Direct(instance),
                                            args,
                                        ))
                                        .unwrap();
                                    let (condition, guards) = match self.0.invocation {
                                        Invocation::Base
                                        | Invocation::Loop
                                        | Invocation::ClosedPaths => {
                                            (returned, shapelint_driver::sequence::Sequence::EMPTY)
                                        }
                                        Invocation::GuardedLoop => {
                                            let returned = graph
                                                .intern_expr(ExprNode::Test(returned))
                                                .unwrap();
                                            let selected = graph
                                                .intern_expr(ExprNode::Select(
                                                    enabled, returned, one,
                                                ))
                                                .unwrap();
                                            let condition = graph
                                                .intern_condition(ConditionNode::Compare(
                                                    Order::Equal,
                                                    selected,
                                                    one,
                                                ))
                                                .unwrap();
                                            (
                                                condition,
                                                graph
                                                    .condition_sequences
                                                    .from_iter([enabled])
                                                    .unwrap(),
                                            )
                                        }
                                    };
                                    summary.checks.push(Check {
                                        basis: shapelint_driver::contracts::CheckBasis::Expression,
                                        loop_writes: None,
                                        condition,
                                        guards,
                                        span: tcx.def_span(root),
                                    });
                                }
                                def => {
                                    let callee = match (self.0.topology, def) {
                                        (Topology::SelfCall, _) => def,
                                        (Topology::Mutual, def) if def == first => second,
                                        (Topology::Mutual, _) => first,
                                    };
                                    let instance = graph
                                        .values
                                        .intern_instance(&Instance {
                                            def: callee.to_def_id(),
                                            args: Vec::new(),
                                            dispatch: Dispatch::Item,
                                        })
                                        .unwrap();
                                    let args =
                                        graph.expression_sequences.from_iter([argument]).unwrap();
                                    let recursive = graph
                                        .intern_expr(ExprNode::Call(
                                            TargetNode::Direct(instance),
                                            args,
                                            None,
                                        ))
                                        .unwrap();
                                    match self.0.invocation {
                                        Invocation::ClosedPaths => {
                                            let selected = graph
                                                .intern_expr(ExprNode::Select(
                                                    enabled, one, recursive,
                                                ))
                                                .unwrap();
                                            summary.returns.push(Return {
                                                value: selected,
                                                guards: graph
                                                    .condition_sequences
                                                    .from_iter([enabled])
                                                    .unwrap(),
                                            });
                                            summary.returns.push(Return {
                                                value: one,
                                                guards: graph
                                                    .condition_sequences
                                                    .from_iter([disabled])
                                                    .unwrap(),
                                            });
                                        }
                                        Invocation::Base
                                        | Invocation::Loop
                                        | Invocation::GuardedLoop => {
                                            summary.returns.push(Return {
                                                value: one,
                                                guards: graph
                                                    .condition_sequences
                                                    .from_iter([enabled])
                                                    .unwrap(),
                                            });
                                            summary.returns.push(Return {
                                                value: recursive,
                                                guards: graph
                                                    .condition_sequences
                                                    .from_iter([disabled])
                                                    .unwrap(),
                                            });
                                        }
                                    }
                                }
                            }
                            graph.freeze(summary).unwrap()
                        },
                        findings: Vec::new(),
                        invariants: Vec::new(),
                        constructions: Vec::new(),
                        work: Default::default(),
                    })
                    .collect();
                let linked = pipeline::Collected::from(analyses).link(
                    artifacts::Inputs::default()
                        .import(tcx, &mut graph)
                        .expect("empty imports"),
                );
                let contracts::Analysis { findings, work: _ } = contracts::findings(
                    tcx,
                    linked.as_ref(),
                    &mut graph,
                    callers::Scope::Library,
                    shapelint_driver::pipeline::AnalysisGaps::Show,
                    &Default::default(),
                )
                .expect("findings");
                let checks: Vec<_> = findings
                    .iter()
                    .filter_map(|(owner, finding)| match &finding.evidence {
                        CompilerEvidence::RedundantCheck {
                            outcome,
                            established,
                            ..
                        } if *owner == root => Some((outcome, established)),
                        _ => None,
                    })
                    .collect();
                let [(outcome, evidence)] = checks.as_slice() else {
                    panic!("one return-predicate proof for {:?}", self.0);
                };
                match self.0.invocation {
                    Invocation::Base | Invocation::ClosedPaths => {
                        match outcome {
                            CheckOutcome::AlwaysTrue => {}
                            CheckOutcome::AlwaysFalse => panic!("base case returns"),
                        }
                        assert!(evidence.starts_with("Known values imply"), "{evidence}");
                    }
                    Invocation::Loop => {
                        match outcome {
                            CheckOutcome::AlwaysFalse => {}
                            CheckOutcome::AlwaysTrue => panic!("recursive cycle does not return"),
                        }
                        assert_eq!(
                            evidence.as_str(),
                            "Recursive return and control-flow analysis establishes this result."
                        );
                    }
                    Invocation::GuardedLoop => {
                        match outcome {
                            CheckOutcome::AlwaysFalse => {}
                            CheckOutcome::AlwaysTrue => panic!("recursive cycle does not return"),
                        }
                        assert!(
                            evidence.starts_with(
                                "Recursive return and control-flow analysis, together with"
                            ),
                            "{evidence}"
                        );
                        assert!(!evidence.contains("Known values"), "{evidence}");
                    }
                }
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("recursive.rs");
    let recurrence = match case.topology {
        Topology::SelfCall => "first",
        Topology::Mutual => "second",
    };
    let second_recurrence = match case.topology {
        Topology::SelfCall => "second",
        Topology::Mutual => "first",
    };
    std::fs::write(&source, format!("pub fn first(done:bool)->u8{{if done{{1}}else{{{recurrence}(done)}}}} pub fn second(done:bool)->u8{{if done{{1}}else{{{second_recurrence}(done)}}}} pub fn run(input:bool)->bool{{input}}" )).expect("source");
    let arguments = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        source.display().to_string(),
    ];
    assert_eq!(
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(
            &arguments,
            &mut Analyze(case)
        )),
        std::process::ExitCode::SUCCESS
    );
}
