#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use shapelint_driver::contracts::graph::{
    AlternativeId, ConditionNode, ExprNode, FlowId, Graph, with_graph,
};
use shapelint_driver::contracts::{Order, Summary};
use shapelint_driver::protocols::{self, Flow};
use std::hash::{DefaultHasher, Hash, Hasher};

#[test]
fn identical_flow_widening_preserves_identity_with_a_decision() {
    use shapelint_driver::contracts::Join;

    with_graph(|mut graph| {
        let flow = graph.intern_flow(Flow::Ready).expect("ready");
        let condition = graph
            .intern_condition(ConditionNode::Unknown)
            .expect("condition");

        let joined = graph
            .join_flow(flow, flow, Join::Widen, Some(condition))
            .expect("stable widening");

        assert_eq!(joined, flow);
        assert_eq!(graph[joined], Flow::Ready);
    });
}

#[test]
fn deep_flow_traits_preserve_branch_order_and_drop_normally() {
    with_graph(|mut graph| {
        let condition = graph
            .intern_condition(ConditionNode::Unknown)
            .expect("condition");
        let incoming = graph.intern_flow(Flow::Incoming).expect("incoming");
        let unknown = graph.intern_flow(Flow::Unknown).expect("unknown");
        let ready = graph.intern_flow(Flow::Ready).expect("ready");
        let mut flow = incoming;
        for _ in 0..100_000 {
            let alternatives = graph
                .intern_alternatives([flow, unknown])
                .expect("alternatives");
            flow = graph
                .intern_flow(Flow::Select(condition, alternatives, ready))
                .expect("selection");
        }
        let cloned = graph
            .intern_flow(graph[flow].clone())
            .expect("canonical root");
        assert_eq!(flow, cloned);
        let mut original_hash = DefaultHasher::new();
        flow.hash(&mut original_hash);
        let mut cloned_hash = DefaultHasher::new();
        cloned.hash(&mut cloned_hash);
        assert_eq!(original_hash.finish(), cloned_hash.finish());
        assert!(!format!("{flow:?}").is_empty());
        let mut current = cloned;
        for _ in 0..100_000 {
            let Flow::Select(actual_condition, yes, no) = &graph[current] else {
                panic!("expected selected flow");
            };
            assert_eq!(*actual_condition, condition);
            assert_eq!(*no, ready);
            let Flow::Alternatives(values) = &graph[*yes] else {
                panic!("expected ordered alternatives");
            };
            let values = alternatives(&graph, *values);
            assert_eq!(values.len(), 2);
            assert_eq!(values[1], unknown);
            current = values[0];
        }
        assert_eq!(current, incoming);
        let nodes = graph.flows().count();
        assert_eq!(nodes, 200_003);
    });
}

fn freeze_summaries<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    summaries: rustc_data_structures::fx::FxHashMap<
        rustc_hir::def_id::DefId,
        shapelint_driver::contracts::Summary<
            'g,
            shapelint_driver::contracts::graph::ExprId<'g>,
            shapelint_driver::contracts::graph::ConditionId<'g>,
            shapelint_driver::contracts::graph::TargetNode<'g>,
            shapelint_driver::contracts::graph::FlowId<'g>,
        >,
    >,
) -> rustc_data_structures::fx::FxHashMap<
    rustc_hir::def_id::DefId,
    shapelint_driver::contracts::summaries::SummaryId<'g>,
> {
    summaries
        .into_iter()
        .map(|(def, summary)| {
            let id = graph
                .summaries
                .freeze(
                    &mut graph.values,
                    &mut graph.function_sets,
                    &mut graph.input_sets,
                    &mut graph.expression_sequences,
                    summary,
                )
                .unwrap();
            (def, id)
        })
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum Atom {
    Incoming,
    Unknown,
    Ready,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Alternatives {
    values: Vec<Atom>,
}

#[hegel::test(print_blob = true)]
fn flow_clone_preserves_every_alternative_in_order(tc: hegel::TestCase) {
    let Alternatives { values } = tc.draw(hegel::generators::default::<Alternatives>());
    with_graph(|mut graph| {
        let children: Vec<_> = values
            .iter()
            .map(|value| {
                graph
                    .intern_flow(match value {
                        Atom::Incoming => Flow::Incoming,
                        Atom::Unknown => Flow::Unknown,
                        Atom::Ready => Flow::Ready,
                    })
                    .expect("alternative")
            })
            .collect();
        let flow = graph.intern_alternatives(children).expect("alternatives");
        let cloned = flow;
        let Flow::Alternatives(actual) = &graph[cloned] else {
            panic!("expected alternatives");
        };
        let actual = alternatives(&graph, *actual)
            .iter()
            .map(|value| match &graph[*value] {
                Flow::Incoming => Atom::Incoming,
                Flow::Unknown => Atom::Unknown,
                Flow::Ready => Atom::Ready,
                value => panic!("unexpected flow {value:?}"),
            })
            .collect::<Vec<_>>();
        assert_eq!(actual, values);
    });
}

#[test]
fn deep_protocol_call_dependencies_retain_the_dirty_witness() {
    struct Analyze;
    impl rustc_driver::Callbacks for Analyze {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let owner = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "run")
                .expect("run function")
                .to_def_id();
            let helper = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "helper")
                .expect("helper function")
                .to_def_id();
            with_graph(|mut graph| {
                let name = rustc_span::Symbol::intern("durability");
                let span = tcx.def_span(owner);
                let mut flow = graph
                    .intern_flow(Flow::Dirty { def: owner, span })
                    .expect("dirty");
                for _ in 0..100_000 {
                    flow = graph
                        .intern_flow(Flow::Call {
                            callee: helper,
                            argument: 0,
                            input: flow,
                        })
                        .expect("call");
                }
                let mut caller = Summary::default();
                caller.protocol_checks.push(protocols::Obligation {
                    name,
                    span,
                    flow,
                    guards: Default::default(),
                });
                let mut callee = Summary::default();
                callee.protocol_returns.push(protocols::Return {
                    name,
                    argument: 0,
                    flow: graph.intern_flow(Flow::Incoming).expect("incoming"),
                });
                let summaries = rustc_data_structures::fx::FxHashMap::from_iter([
                    (owner, caller),
                    (helper, callee),
                ]);
                let nodes = graph.flows().count();
                assert_eq!(nodes, 100_002);
                let summaries = freeze_summaries(&mut graph, summaries);
                let findings = protocols::findings(
                    tcx,
                    &mut graph,
                    &summaries,
                    &shapelint_driver::diagnostics::Sources::default(),
                )
                .expect("protocol effects");
                assert_eq!(findings.len(), 1);
                assert_eq!(findings[0].0, owner.expect_local());
                assert_eq!(findings[0].1.span, span);
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("protocol.rs");
    std::fs::write(&source, "pub fn run() {} pub fn helper() {}").expect("protocol source");
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
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Analyze));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[test]
fn deep_selected_protocol_paths_reach_the_proven_branch() {
    struct Analyze;
    impl rustc_driver::Callbacks for Analyze {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let owner = tcx
                .hir_body_owners()
                .next()
                .expect("run function")
                .to_def_id();
            with_graph(|mut graph| {
                let name = rustc_span::Symbol::intern("durability");
                let span = tcx.def_span(owner);
                let mut flow = graph
                    .intern_flow(Flow::Dirty { def: owner, span })
                    .expect("dirty");
                let one = graph.intern_expr(ExprNode::Number(1)).expect("one");
                let condition = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, one, one))
                    .expect("condition");
                for _ in 0..100_000 {
                    let ready = graph.intern_flow(Flow::Ready).expect("ready");
                    flow = graph
                        .intern_flow(Flow::Select(condition, flow, ready))
                        .expect("selection");
                }
                let mut summary = Summary::default();
                summary.protocol_checks.push(protocols::Obligation {
                    name,
                    span,
                    flow,
                    guards: Default::default(),
                });
                let summaries = rustc_data_structures::fx::FxHashMap::from_iter([(owner, summary)]);
                let summaries = freeze_summaries(&mut graph, summaries);
                let findings = protocols::findings(
                    tcx,
                    &mut graph,
                    &summaries,
                    &shapelint_driver::diagnostics::Sources::default(),
                )
                .expect("selected protocol paths");
                assert_eq!(findings.len(), 1);
                assert_eq!(findings[0].0, owner.expect_local());
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("protocol.rs");
    std::fs::write(&source, "pub fn run() {}").expect("protocol source");
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
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Analyze));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Merge {
    Hull,
    Widen,
}

#[hegel::test(print_blob = true)]
fn empty_protocol_states_ignore_shared_symbolic_branch_values(tc: hegel::TestCase) {
    use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
    use shapelint_driver::contracts::{Arithmetic, Join};

    let (depth, merge) = tc.draw(hegel::generators::default::<(u8, Merge)>());
    with_graph(|mut graph| {
        let mut value = graph.intern_expr(ExprNode::Argument(0)).expect("argument");
        for _ in 0..depth {
            value = graph
                .intern_expr(ExprNode::Arithmetic(
                    Arithmetic::Add(rustc_middle::ty::UintTy::U8),
                    value,
                    value,
                ))
                .expect("shared expression");
        }
        let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, value, zero))
            .expect("condition");
        protocols::with_stores(&mut graph, |stores, graph| {
            let mut left = protocols::State::default();
            let right = protocols::State::default();
            let join = match merge {
                Merge::Hull => Join::Hull,
                Merge::Widen => Join::Widen,
            };
            left.merge(stores, graph, &right, join, Some(condition))
                .expect("merge");
            assert!(left == right);
            assert!(left.returns(stores, 0).is_empty());
        });
    });
}

#[test]
fn shared_protocol_diamonds_keep_linear_nodes_through_capture() {
    use shapelint_driver::contracts::Join;

    with_graph(|mut graph| {
        let condition = graph
            .intern_condition(ConditionNode::Unknown)
            .expect("condition");
        let mut flow = graph.intern_flow(Flow::Incoming).expect("incoming");
        let ready = graph.intern_flow(Flow::Ready).expect("ready");
        for _ in 0..100_000 {
            let left = graph
                .intern_alternatives([flow, ready])
                .expect("left branch");
            let right = graph
                .intern_alternatives([ready, flow])
                .expect("right branch");
            flow = graph
                .join_flow(left, right, Join::Hull, Some(condition))
                .expect("diamond");
        }
        let nodes = graph.flows().count();
        assert_eq!(nodes, 300_002);
        graph.intern_flow(Flow::Unknown).expect("unreachable flow");
        let mut summary = Summary::default();
        summary.protocol_returns.push(protocols::Return {
            name: rustc_span::sym::test,
            argument: 0,
            flow,
        });
        let summary = graph.freeze(summary).expect("captured history");
        let summary = graph.summaries[summary];
        let nodes = graph.flows().count();
        assert_eq!(nodes, 300_003);
        let returns: Vec<_> = graph
            .summaries
            .protocol_returns
            .iter(summary.protocol_returns)
            .copied()
            .collect();
        let [returned] = returns.as_slice() else {
            panic!("one protocol return");
        };
        let mut flow = returned.flow;
        for _ in 0..100_000 {
            let Flow::Select(condition, left, right) = graph[flow] else {
                panic!("diamond selection");
            };
            let ConditionNode::Unknown = graph[condition] else {
                panic!("captured condition");
            };
            let Flow::Alternatives(left) = &graph[left] else {
                panic!("left branch");
            };
            let Flow::Alternatives(right) = &graph[right] else {
                panic!("right branch");
            };
            let left = alternatives(&graph, *left);
            let right = alternatives(&graph, *right);
            assert_eq!(left[0], right[1]);
            assert_eq!(left[1], right[0]);
            assert_eq!(graph[left[1]], Flow::Ready);
            flow = left[0];
        }
        assert_eq!(graph[flow], Flow::Incoming);
    });
}

#[hegel::test(print_blob = true)]
fn joining_protocol_histories_retains_first_occurrence_order(tc: hegel::TestCase) {
    use shapelint_driver::contracts::Join;
    let Alternatives { values } = tc.draw(hegel::generators::default::<Alternatives>());
    with_graph(|mut graph| {
        let mut root = graph.intern_flow(Flow::Alternatives(None)).expect("empty");
        for atom in &values {
            let node = match atom {
                Atom::Incoming => Flow::Incoming,
                Atom::Unknown => Flow::Unknown,
                Atom::Ready => Flow::Ready,
            };
            let next = graph.intern_flow(node).expect("atom");
            root = graph.join_flow(root, next, Join::Hull, None).expect("join");
        }
        let mut expected = Vec::new();
        for value in values {
            if !expected.contains(&value) {
                expected.push(value);
            }
        }
        let Flow::Alternatives(sequence) = graph[root] else {
            panic!("joined alternatives");
        };
        let actual = alternatives(&graph, sequence)
            .into_iter()
            .map(|id| match graph[id] {
                Flow::Incoming => Atom::Incoming,
                Flow::Unknown => Atom::Unknown,
                Flow::Ready => Atom::Ready,
                ref other => panic!("unexpected history {other:?}"),
            })
            .collect::<Vec<_>>();
        for id in alternatives(&graph, sequence) {
            let joined = graph
                .join_flow(root, id, Join::Hull, None)
                .expect("rejoined alternative");
            assert_eq!(
                joined, root,
                "joining an existing alternative preserves identity"
            );
            let widened = graph
                .join_flow(root, joined, Join::Widen, None)
                .expect("widened alternative");
            assert_eq!(
                widened, root,
                "widening an unchanged ordered set preserves its history"
            );
        }
        assert_eq!(actual, expected);
    });
}

fn alternatives<'g>(graph: &Graph<'g>, mut sequence: Option<AlternativeId<'g>>) -> Vec<FlowId<'g>> {
    let mut values = Vec::new();
    while let Some(id) = sequence {
        values.push(graph[id].value);
        sequence = graph[id].previous;
    }
    values.reverse();
    values
}

#[test]
fn rejoining_a_dirty_alternative_does_not_widen_to_unknown() {
    use shapelint_driver::contracts::Join;
    with_graph(|mut graph| {
        let dirty = graph
            .intern_flow(Flow::Dirty {
                def: rustc_hir::def_id::LOCAL_CRATE.as_def_id(),
                span: rustc_span::DUMMY_SP,
            })
            .expect("dirty");
        let ready = graph.intern_flow(Flow::Ready).expect("ready");
        let original = graph
            .join_flow(dirty, ready, Join::Hull, None)
            .expect("original alternatives");
        let rejoined = graph
            .join_flow(original, dirty, Join::Hull, None)
            .expect("same dirty alternative");
        let widened = graph
            .join_flow(original, rejoined, Join::Widen, None)
            .expect("widened alternatives");
        assert_eq!(rejoined, original);
        assert_eq!(widened, original);
        let Flow::Alternatives(sequence) = graph[widened] else {
            panic!("dirty history survives widening");
        };
        assert_eq!(alternatives(&graph, sequence), vec![dirty, ready]);
    });
}

#[test]
fn growing_alternative_lists_share_prefixes_and_rejoin_them_without_growth() {
    use shapelint_driver::contracts::Join;
    with_graph(|mut graph| {
        let incoming = graph.intern_flow(Flow::Incoming).expect("incoming");
        let mut root = incoming;
        let mut member = incoming;
        let mut prefix = incoming;
        for index in 0..100_000 {
            member = graph
                .intern_flow(Flow::Call {
                    callee: rustc_hir::def_id::LOCAL_CRATE.as_def_id(),
                    argument: 0,
                    input: member,
                })
                .expect("distinct member");
            root = graph
                .join_flow(root, member, Join::Hull, None)
                .expect("append member");
            if index == 49_999 {
                prefix = root;
            }
        }
        let flows = graph.flows().count();
        assert_eq!(flows, 200_001);
        let sequences = graph.flow_alternatives().count();
        assert_eq!(sequences, 200_001);
        for _ in 0..100_000 {
            assert_eq!(
                graph
                    .join_flow(root, prefix, Join::Hull, None)
                    .expect("shared prefix"),
                root
            );
        }
        let sequences = graph.flow_alternatives().count();
        assert_eq!(sequences, 200_001);
        let mut summary = Summary::default();
        summary.protocol_returns.push(protocols::Return {
            name: rustc_span::sym::test,
            argument: 0,
            flow: root,
        });
        let summary = graph.freeze(summary).expect("captured shared list");
        let summary = graph.summaries[summary];
        let flows = graph.flows().count();
        assert_eq!(flows, 200_001);
        let sequences = graph.flow_alternatives().count();
        assert_eq!(sequences, 200_001);
        let root = graph
            .summaries
            .protocol_returns
            .iter(summary.protocol_returns)
            .next()
            .unwrap()
            .flow;
        let Flow::Alternatives(mut prefix) = graph[root] else {
            panic!("captured alternatives");
        };
        for _ in 0..50_000 {
            let Some(id) = prefix else {
                panic!("complete prefix");
            };
            prefix = graph[id].previous;
        }
        let prefix = graph
            .intern_flow(Flow::Alternatives(prefix))
            .expect("captured prefix root");
        assert_eq!(
            graph
                .join_flow(root, prefix, Join::Hull, None)
                .expect("captured prefix union"),
            root
        );
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
struct AlternativeJoin {
    left: Vec<Atom>,
    right: Vec<Atom>,
}

#[hegel::test(print_blob = true)]
fn joining_explicit_alternatives_preserves_left_duplicates_and_right_first_occurrences(
    tc: hegel::TestCase,
) {
    use shapelint_driver::contracts::Join;
    let AlternativeJoin { left, right } = tc.draw(hegel::generators::default::<AlternativeJoin>());
    let mut expected = left.clone();
    for atom in &right {
        if !expected.contains(atom) {
            expected.push(*atom);
        }
    }
    with_graph(|mut graph| {
        let incoming = graph.intern_flow(Flow::Incoming).expect("incoming");
        let unknown = graph.intern_flow(Flow::Unknown).expect("unknown");
        let ready = graph.intern_flow(Flow::Ready).expect("ready");
        let id = |atom: &Atom| match atom {
            Atom::Incoming => incoming,
            Atom::Unknown => unknown,
            Atom::Ready => ready,
        };
        let left = graph
            .intern_alternatives(left.iter().map(id))
            .expect("explicit left");
        let right = graph
            .intern_alternatives(right.iter().map(id))
            .expect("explicit right");
        let expected = graph
            .intern_alternatives(expected.iter().map(id))
            .expect("ordered union");
        let joined = graph
            .join_flow(left, right, Join::Hull, None)
            .expect("joined history");
        assert_eq!(joined, expected);
        assert_eq!(
            graph
                .join_flow(expected, joined, Join::Widen, None)
                .expect("equal histories"),
            expected
        );
    });
}

#[test]
fn rejoining_an_explicit_duplicate_left_preserves_its_identity() {
    use shapelint_driver::contracts::Join;
    with_graph(|mut graph| {
        let dirty = graph
            .intern_flow(Flow::Dirty {
                def: rustc_hir::def_id::LOCAL_CRATE.as_def_id(),
                span: rustc_span::DUMMY_SP,
            })
            .expect("dirty");
        let ready = graph.intern_flow(Flow::Ready).expect("ready");
        let original = graph
            .intern_alternatives([dirty, dirty, ready])
            .expect("explicit duplicates");
        let joined = graph
            .join_flow(original, dirty, Join::Hull, None)
            .expect("duplicate rejoin");
        let widened = graph
            .join_flow(original, joined, Join::Widen, None)
            .expect("unchanged history");
        assert_eq!(widened, original);
        let Flow::Alternatives(sequence) = graph[widened] else {
            panic!("explicit alternative sequence");
        };
        assert_eq!(alternatives(&graph, sequence), vec![dirty, dirty, ready]);
    });
}
