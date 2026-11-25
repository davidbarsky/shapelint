#![feature(rustc_private)]

use shapelint_driver::contracts::graph::evidence::Proof;
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, TargetNode, with_graph};
use shapelint_driver::contracts::{Order, ProofGap, Truth};
use shapelint_driver::sequence::Sequence;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Evidence {
    Present,
    Absent,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Noise {
    Returned(u128),
    Set,
    Clear,
    NotSet,
    NotClear,
    UnknownReturn,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Projection {
    evidence: Evidence,
    branches: [u128; 2],
    threshold: u128,
    noise: Vec<Noise>,
}

#[hegel::test(print_blob = true)]
fn unrelated_guards_preserve_generated_branch_truth(tc: hegel::TestCase) {
    let Projection {
        evidence,
        branches,
        threshold,
        noise,
    } = tc.draw(hegel::generators::default::<Projection>());
    let yes = match branches[0].cmp(&threshold) {
        std::cmp::Ordering::Less => Truth::Proven,
        std::cmp::Ordering::Equal | std::cmp::Ordering::Greater => Truth::Refuted,
    };
    let no = match branches[1].cmp(&threshold) {
        std::cmp::Ordering::Less => Truth::Proven,
        std::cmp::Ordering::Equal | std::cmp::Ordering::Greater => Truth::Refuted,
    };
    let expected = match (evidence, yes, no) {
        (Evidence::Present, truth, _) => truth,
        (Evidence::Absent, Truth::Proven, Truth::Proven) => Truth::Proven,
        (Evidence::Absent, Truth::Refuted, Truth::Refuted) => Truth::Refuted,
        (Evidence::Absent, _, _) => Truth::Unknown(ProofGap::Comparison),
    };
    with_graph(|mut graph| {
        let target = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let returned = graph
            .intern_condition(ConditionNode::Returned(
                TargetNode::Indirect(target),
                Sequence::EMPTY,
            ))
            .unwrap();
        let yes = graph.intern_expr(ExprNode::Number(branches[0])).unwrap();
        let no = graph.intern_expr(ExprNode::Number(branches[1])).unwrap();
        let selected = graph
            .intern_expr(ExprNode::Select(returned, yes, no))
            .unwrap();
        let threshold = graph.intern_expr(ExprNode::Number(threshold)).unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Less, selected, threshold))
            .unwrap();
        let relevant: Sequence<_> = match evidence {
            Evidence::Present => graph.condition_sequences.from_iter([returned]).unwrap(),
            Evidence::Absent => Sequence::default(),
        };
        assert_eq!(graph.truth(required, &relevant).unwrap(), expected);
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        let mut guards = Sequence::default();
        let entries = noise.into_iter().enumerate();
        for (index, noise) in entries {
            let input = graph.intern_expr(ExprNode::Argument(index + 1)).unwrap();
            let node = match noise {
                Noise::Returned(argument) => {
                    let argument = graph.intern_expr(ExprNode::Number(argument)).unwrap();
                    ConditionNode::Returned(
                        TargetNode::Indirect(input),
                        graph.expression_sequences.from_iter([argument]).unwrap(),
                    )
                }
                Noise::UnknownReturn => ConditionNode::Returned(
                    TargetNode::Indirect(input),
                    graph.expression_sequences.from_iter([unknown]).unwrap(),
                ),
                Noise::Set | Noise::Clear | Noise::NotSet | Noise::NotClear => {
                    let predicate = graph.from_expr(input, 1).unwrap();
                    let composite = graph.intern_expr(ExprNode::Test(predicate)).unwrap();
                    let (order, constant) = match noise {
                        Noise::Set => (Order::Equal, one),
                        Noise::Clear => (Order::Equal, zero),
                        Noise::NotSet => (Order::NotEqual, one),
                        Noise::NotClear => (Order::NotEqual, zero),
                        Noise::Returned(_) | Noise::UnknownReturn => unreachable!(),
                    };
                    ConditionNode::Compare(order, composite, constant)
                }
            };
            let guard = graph.intern_condition(node).unwrap();
            guards = graph.condition_sequences.push(guards, guard).unwrap();
        }
        guards = graph.condition_sequences.append(guards, relevant).unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), expected);
        let values = graph
            .condition_sequences
            .iter(guards)
            .copied()
            .rev()
            .collect::<Vec<_>>();
        guards = graph.condition_sequences.from_iter(values).unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), expected);
        assert_eq!(graph.truth(required, &guards).unwrap(), expected);
    });
}

#[test]
fn inverted_boolean_selection_requires_its_own_return_guard() {
    with_graph(|mut graph| {
        let [returned, unrelated] = [0, 1].map(|index| {
            let target = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            graph
                .intern_condition(ConditionNode::Returned(
                    TargetNode::Indirect(target),
                    Sequence::EMPTY,
                ))
                .unwrap()
        });
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let selected = graph
            .intern_expr(ExprNode::Select(returned, zero, one))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Less, selected, one))
            .unwrap();
        let guards = graph.condition_sequences.from_iter([unrelated]).unwrap();
        assert_eq!(
            graph.truth(required, &guards).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
        let guards = graph.condition_sequences.from_iter([returned]).unwrap();
        let Proof::Proven(evidence) = graph.prove(required, &guards).unwrap() else {
            panic!("returning selects zero, which is less than one");
        };
        assert_eq!(graph.evidence_sequence(evidence).unwrap(), guards);
    });
}

#[test]
fn irrelevant_guard_family_over_a_large_shared_dag_preserves_identity_truth() {
    with_graph(|mut graph| {
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let mut value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let mut guards = Sequence::default();
        for index in 1..=4096 {
            let fields = graph
                .expression_sequences
                .from_iter([value, value])
                .unwrap();
            value = graph.intern_expr(ExprNode::Aggregate(fields)).unwrap();
            let input = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            let returned = graph
                .intern_condition(ConditionNode::Returned(
                    TargetNode::Indirect(input),
                    Sequence::EMPTY,
                ))
                .unwrap();
            guards = graph.condition_sequences.push(guards, returned).unwrap();
            let predicate = graph.from_expr(input, 1).unwrap();
            let composite = graph.intern_expr(ExprNode::Test(predicate)).unwrap();
            let equality = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, composite, one))
                .unwrap();
            guards = graph.condition_sequences.push(guards, equality).unwrap();
        }
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, value, value))
            .unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
        assert_eq!(
            graph.truth(required, &Sequence::default()).unwrap(),
            Truth::Proven
        );
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
    });
}
