#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::ty::TyCtxt;
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
use shapelint_driver::contracts::{InvalidatedFact, Order};
use shapelint_driver::diagnostics::Sources;
use shapelint_driver::states::facts::{Facts, with_context};

fn run(mut callback: impl rustc_driver::Callbacks + Send) {
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("facts.rs");
    std::fs::write(&source, "pub fn run() {}").expect("fixture source");
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

#[derive(Debug, hegel::DefaultGenerator)]
struct Merge {
    left: Vec<u8>,
    right: Vec<u8>,
    lost_left: Vec<u8>,
    lost_right: Vec<u8>,
    additional: Option<u8>,
}

impl rustc_driver::Callbacks for Merge {
    fn after_expansion<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let def = tcx.hir_body_owners().next().expect("fixture function");
        let body = tcx.mir_promoted(def).0.borrow();
        with_graph(|mut graph| {
            let values = graph.values.share();
            with_context(tcx, &body, &Sources::default(), values, |mut context| {
                let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                let keys: FxHashSet<_> = self
                    .left
                    .iter()
                    .chain(&self.right)
                    .chain(&self.lost_left)
                    .chain(&self.lost_right)
                    .chain(self.additional.iter())
                    .copied()
                    .collect();
                let conditions: FxHashMap<_, _> = keys
                    .into_iter()
                    .map(|key| {
                        let value = graph
                            .intern_expr(ExprNode::Argument(usize::from(key)))
                            .expect("argument");
                        let condition = graph
                            .intern_condition(ConditionNode::Compare(Order::Equal, value, zero))
                            .expect("condition");
                        (key, condition)
                    })
                    .collect();
                let mut left = Facts::default();
                let mut right = Facts::default();
                for key in &self.left {
                    left.condition(conditions[key], &mut graph, &mut context)
                        .expect("left condition");
                }
                for key in &self.right {
                    right
                        .condition(conditions[key], &mut graph, &mut context)
                        .expect("right condition");
                }
                for key in &self.lost_left {
                    left.lose(
                        InvalidatedFact {
                            condition: conditions[key],
                            def: def.to_def_id(),
                            span: body.span,
                        },
                        &mut graph,
                        &mut context,
                    )
                    .expect("left lost condition");
                }
                for key in &self.lost_right {
                    right
                        .lose(
                            InvalidatedFact {
                                condition: conditions[key],
                                def: def.to_def_id(),
                                span: body.span,
                            },
                            &mut graph,
                            &mut context,
                        )
                        .expect("right lost condition");
                }
                let before = left.clone();
                left.merge(
                    &right,
                    self.additional.map(|key| conditions[&key]),
                    &mut graph,
                    &mut context,
                )
                .expect("merge facts");
                let expected: Vec<_> = self
                    .left
                    .iter()
                    .filter(|key| self.right.contains(key))
                    .copied()
                    .chain(self.additional)
                    .map(|key| conditions[&key])
                    .collect();
                assert_eq!(
                    graph
                        .condition_sequences
                        .iter(left.conditions)
                        .copied()
                        .collect::<Vec<_>>(),
                    expected
                );
                let mut seen = FxHashSet::default();
                let expected_lost: Vec<_> = self
                    .lost_left
                    .iter()
                    .filter(|key| self.lost_right.contains(key) && seen.insert(**key))
                    .map(|key| conditions[key])
                    .collect();
                let actual_lost: Vec<_> = graph
                    .invalidated_sequences
                    .iter(left.lost)
                    .map(|fact| fact.condition)
                    .collect();
                assert_eq!(actual_lost, expected_lost);
                let original: Vec<_> = self.left.iter().map(|key| conditions[key]).collect();
                assert_eq!(
                    graph
                        .condition_sequences
                        .iter(before.conditions)
                        .copied()
                        .collect::<Vec<_>>(),
                    original
                );
                let mut seen = FxHashSet::default();
                let original_lost: Vec<_> = self
                    .lost_left
                    .iter()
                    .filter(|key| seen.insert(**key))
                    .map(|key| conditions[key])
                    .collect();
                let saved_lost: Vec<_> = graph
                    .invalidated_sequences
                    .iter(before.lost)
                    .map(|fact| fact.condition)
                    .collect();
                assert_eq!(saved_lost, original_lost);
                left.merge(&right, None, &mut graph, &mut context)
                    .expect("subsequent intersection");
                let expected: Vec<_> = self
                    .left
                    .iter()
                    .copied()
                    .filter(|key| self.right.contains(key))
                    .chain(self.additional.filter(|key| self.right.contains(key)))
                    .map(|key| conditions[&key])
                    .collect();
                assert_eq!(
                    graph
                        .condition_sequences
                        .iter(left.conditions)
                        .copied()
                        .collect::<Vec<_>>(),
                    expected
                );
            })
            .unwrap();
        });
        rustc_driver::Compilation::Stop
    }
}

#[hegel::test(print_blob = true)]
fn fact_merges_preserve_order_multiplicity_lost_facts_and_snapshots(tc: hegel::TestCase) {
    run(tc.draw(hegel::generators::default::<Merge>()));
}

#[test]
fn replacement_equal_to_a_removed_condition_keeps_one_occurrence() {
    run(Merge {
        left: vec![1, 1],
        right: vec![],
        lost_left: vec![],
        lost_right: vec![],
        additional: Some(1),
    });
}

#[test]
fn replacement_equal_to_a_common_condition_appends_one_occurrence() {
    run(Merge {
        left: vec![1, 1],
        right: vec![1],
        lost_left: vec![2, 2, 3],
        lost_right: vec![2],
        additional: Some(1),
    });
}

#[test]
fn expanding_disjunctions_attach_only_new_graph_nodes() {
    struct Growth;
    impl rustc_driver::Callbacks for Growth {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let def = tcx.hir_body_owners().next().expect("fixture function");
            let body = tcx.mir_promoted(def).0.borrow();
            with_graph(|mut graph| {
                let values = graph.values.share();
                with_context(tcx, &body, &Sources::default(), values, |mut context| {
                    let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                    let one = graph.intern_expr(ExprNode::Number(1)).expect("one");
                    let argument = graph
                        .intern_expr(ExprNode::Argument(0))
                        .expect("first argument");
                    let mut previous = graph
                        .intern_condition(ConditionNode::Compare(Order::Equal, argument, zero))
                        .expect("initial condition");
                    let mut facts = Facts::default();
                    facts
                        .condition(previous, &mut graph, &mut context)
                        .expect("initial facts");
                    let mut attached = 0;
                    for index in 1..1_000 {
                        let before = graph.expression_count() + graph.condition_count();
                        let argument = graph
                            .intern_expr(ExprNode::Argument(index))
                            .expect("next argument");
                        let next = graph
                            .intern_condition(ConditionNode::Compare(Order::Equal, argument, zero))
                            .expect("next condition");
                        let mut incoming = Facts::default();
                        incoming
                            .condition(next, &mut graph, &mut context)
                            .expect("incoming facts");
                        let alternative = graph
                            .intern_expr(ExprNode::Test(next))
                            .expect("alternative");
                        let union = graph
                            .intern_expr(ExprNode::Select(previous, one, alternative))
                            .expect("disjunction");
                        let union = graph.from_expr(union, 1).expect("union condition");
                        let added = facts
                            .merge(&incoming, Some(union), &mut graph, &mut context)
                            .expect("merged facts");
                        let after = graph.expression_count() + graph.condition_count();
                        // The initial one constant becomes reachable at the first union.
                        assert!(added <= after - before + usize::from(index == 1));
                        attached += added;
                        assert_eq!(
                            graph
                                .condition_sequences
                                .iter(facts.conditions)
                                .copied()
                                .collect::<Vec<_>>(),
                            vec![union]
                        );
                        previous = union;
                    }
                    let unique = graph.expression_count() + graph.condition_count();
                    assert!(attached <= unique);
                })
                .unwrap();
            });
            rustc_driver::Compilation::Stop
        }
    }
    run(Growth);
}

#[derive(Debug, hegel::DefaultGenerator)]
struct GuardPaths {
    left: Vec<u8>,
    right: Vec<u8>,
}

impl rustc_driver::Callbacks for GuardPaths {
    fn after_expansion<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let def = tcx.hir_body_owners().next().expect("fixture function");
        let body = tcx.mir_promoted(def).0.borrow();
        with_graph(|mut graph| {
            let values = graph.values.share();
            with_context(tcx, &body, &Sources::default(), values, |mut context| {
                let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                let one = graph.intern_expr(ExprNode::Number(1)).expect("one");
                let keys: FxHashSet<_> = self.left.iter().chain(&self.right).copied().collect();
                let conditions: FxHashMap<_, _> = keys
                    .into_iter()
                    .map(|key| {
                        let value = graph
                            .intern_expr(ExprNode::Argument(usize::from(key)))
                            .expect("argument");
                        let condition = graph
                            .intern_condition(ConditionNode::Compare(Order::Equal, value, zero))
                            .expect("condition");
                        (key, condition)
                    })
                    .collect();
                let left = graph
                    .condition_sequences
                    .from_iter(self.left.iter().map(|key| conditions[key]))
                    .expect("left guards");
                let right = graph
                    .condition_sequences
                    .from_iter(self.right.iter().map(|key| conditions[key]))
                    .expect("right guards");
                let expected = match (self.left.as_slice(), self.right.as_slice()) {
                    ([], _) | (_, []) => None,
                    (left_keys @ [_, ..], right_keys @ [_, ..]) => {
                        let mut left_path = one;
                        for key in left_keys {
                            left_path = graph
                                .intern_expr(ExprNode::Select(conditions[key], left_path, zero))
                                .expect("ordered left path");
                        }
                        let mut right_path = one;
                        for key in right_keys {
                            right_path = graph
                                .intern_expr(ExprNode::Select(conditions[key], right_path, zero))
                                .expect("ordered right path");
                        }
                        let choice = graph.from_expr(left_path, 1).expect("left path condition");
                        let union = graph
                            .intern_expr(ExprNode::Select(choice, one, right_path))
                            .expect("union");
                        let condition = graph.from_expr(union, 1).expect("union condition");
                        match graph
                            .truth(condition, &Default::default())
                            .expect("union proof")
                        {
                            shapelint_driver::contracts::Truth::Proven => None,
                            shapelint_driver::contracts::Truth::Refuted
                            | shapelint_driver::contracts::Truth::Unknown(_) => Some(condition),
                        }
                    }
                };
                let actual = context
                    .join_conditions(&left, &right, &mut graph)
                    .expect("cached union");
                assert_eq!(
                    actual, expected,
                    "the original ordered Select construction is canonical"
                );
                assert_eq!(
                    context
                        .join_conditions(&left, &right, &mut graph)
                        .expect("repeated union"),
                    expected
                );
                if let Some(condition) = actual {
                    let proof = graph.prove(condition, &left).expect("left path proof");
                    let shapelint_driver::contracts::graph::evidence::Proof::Proven(evidence) =
                        proof
                    else {
                        panic!("the left conjunction implies the union: {proof:?}");
                    };
                    let used = graph.evidence_sequence(evidence).expect("proof evidence");
                    for condition in graph.condition_sequences.iter(used) {
                        let Some(_) = graph
                            .condition_sequences
                            .iter(left)
                            .find(|left| *left == condition)
                        else {
                            panic!("proof evidence must come from the left path");
                        };
                    }
                    assert_eq!(
                        graph.truth(condition, &used).expect("replay evidence"),
                        shapelint_driver::contracts::Truth::Proven
                    );
                    let proof = graph.prove(condition, &right).expect("right path proof");
                    let shapelint_driver::contracts::graph::evidence::Proof::Proven(evidence) =
                        proof
                    else {
                        panic!("the right conjunction implies the union: {proof:?}");
                    };
                    let used = graph.evidence_sequence(evidence).expect("proof evidence");
                    for condition in graph.condition_sequences.iter(used) {
                        let Some(_) = graph
                            .condition_sequences
                            .iter(right)
                            .find(|right| *right == condition)
                        else {
                            panic!("proof evidence must come from the right path");
                        };
                    }
                    assert_eq!(
                        graph.truth(condition, &used).expect("replay evidence"),
                        shapelint_driver::contracts::Truth::Proven
                    );
                }
            })
            .unwrap();
        });
        rustc_driver::Compilation::Stop
    }
}

#[hegel::test(print_blob = true)]
fn cached_guard_paths_preserve_ordered_nodes_and_sufficient_evidence(tc: hegel::TestCase) {
    run(tc.draw(hegel::generators::default::<GuardPaths>()));
}

#[test]
fn ordered_guard_paths_retain_repeated_conditions_and_shared_members() {
    run(GuardPaths {
        left: vec![2, 1, 2, 3],
        right: vec![3, 2, 4],
    });
}

#[test]
fn an_empty_guard_path_needs_no_union_condition() {
    run(GuardPaths {
        left: vec![],
        right: vec![1, 2],
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
enum EqualityArms {
    EqualFirst,
    UnequalFirst,
}

#[derive(Debug, hegel::DefaultGenerator)]
enum Operands {
    ArgumentFirst,
    NumberFirst,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct ComplementaryGuards {
    arms: EqualityArms,
    operands: Operands,
    number: u64,
}

impl rustc_driver::Callbacks for ComplementaryGuards {
    fn after_expansion<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let def = tcx.hir_body_owners().next().expect("fixture function");
        let body = tcx.mir_promoted(def).0.borrow();
        with_graph(|mut graph| {
            let values = graph.values.share();
            with_context(tcx, &body, &Sources::default(), values, |mut context| {
                let arg = graph.intern_expr(ExprNode::Argument(0)).expect("argument");
                let number = graph
                    .intern_expr(ExprNode::Number(self.number.into()))
                    .expect("number");
                let (lhs, rhs) = match self.operands {
                    Operands::ArgumentFirst => (arg, number),
                    Operands::NumberFirst => (number, arg),
                };
                let equal = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, lhs, rhs))
                    .expect("equality");
                let unequal = graph.negate(equal).expect("inequality");
                let (left, right) = match self.arms {
                    EqualityArms::EqualFirst => (equal, unequal),
                    EqualityArms::UnequalFirst => (unequal, equal),
                };
                let left = graph
                    .condition_sequences
                    .from_iter([left])
                    .expect("left arm");
                let right = graph
                    .condition_sequences
                    .from_iter([right])
                    .expect("right arm");
                let counts = (graph.expression_count(), graph.condition_count());
                assert_eq!(
                    context
                        .join_conditions(&left, &right, &mut graph)
                        .expect("exhaustive arms"),
                    None
                );
                assert_eq!(counts, (graph.expression_count(), graph.condition_count()));

                let other = graph
                    .intern_expr(ExprNode::Argument(1))
                    .expect("other argument");
                let guard = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, other, number))
                    .expect("extra guard");
                let guarded = graph
                    .condition_sequences
                    .push(right, guard)
                    .expect("guarded arm");
                context
                    .join_conditions(&left, &guarded, &mut graph)
                    .expect("guarded union")
                    .expect("an extra guard restricts the union");
            })
            .expect("facts context");
        });
        rustc_driver::Compilation::Stop
    }
}

#[hegel::test]
fn complementary_singleton_guards_merge_without_constructing_a_predicate(tc: hegel::TestCase) {
    run(tc.draw(hegel::generators::default::<ComplementaryGuards>()));
}
