#![feature(rustc_private)]

use std::collections::HashSet;

use shapelint_driver::contracts::graph::evidence::Proof;
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
use shapelint_driver::contracts::{Order, Truth};
use shapelint_driver::sequence::Sequence;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Relation {
    Strict,
    Inclusive,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Conclusion {
    Strict,
    Unequal,
    Equal,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Chain {
    links: Vec<Relation>,
    unrelated: Vec<u64>,
    conclusion: Conclusion,
}

#[hegel::test(print_blob = true)]
fn comparison_evidence_contains_the_transitive_path_and_no_unrelated_facts(tc: hegel::TestCase) {
    let Chain {
        links,
        unrelated,
        conclusion,
    } = tc.draw(hegel::generators::default::<Chain>());
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let mut last = first;
        let mut chain = Vec::new();
        let relations = std::iter::once(Relation::Inclusive)
            .chain(links)
            .chain(std::iter::once(Relation::Strict))
            .enumerate();
        for (index, relation) in relations {
            let next = graph.intern_expr(ExprNode::Argument(index + 1)).unwrap();
            let order = match relation {
                Relation::Strict => Order::Less,
                Relation::Inclusive => Order::LessEqual,
            };
            chain.push(
                graph
                    .intern_condition(ConditionNode::Compare(order, last, next))
                    .unwrap(),
            );
            last = next;
        }
        let mut guards = graph
            .condition_sequences
            .from_iter(chain.iter().copied())
            .unwrap();
        let unrelated = unrelated.into_iter().enumerate();
        for (index, bound) in unrelated {
            let value = graph
                .intern_expr(ExprNode::Argument(chain.len() + index + 1))
                .unwrap();
            let bound = graph
                .intern_expr(ExprNode::Number(u128::from(bound)))
                .unwrap();
            let guard = graph
                .intern_condition(ConditionNode::Compare(Order::LessEqual, bound, value))
                .unwrap();
            guards = graph.condition_sequences.push(guards, guard).unwrap();
        }
        let (order, expected) = match conclusion {
            Conclusion::Strict => (Order::Less, Truth::Proven),
            Conclusion::Unequal => (Order::NotEqual, Truth::Proven),
            Conclusion::Equal => (Order::Equal, Truth::Refuted),
        };
        let condition = graph
            .intern_condition(ConditionNode::Compare(order, first, last))
            .unwrap();
        let proof = graph.prove(condition, &guards).unwrap();
        assert_eq!(Truth::from(proof), expected);
        let evidence = match proof {
            Proof::Proven(evidence) | Proof::Refuted(evidence) => evidence,
            Proof::Unknown(gap) => panic!("missing transitive proof: {gap:?}"),
        };
        let facts: HashSet<_> = {
            let sequence = graph.evidence_sequence(evidence).unwrap();
            graph.condition_sequences.iter(sequence).copied().collect()
        };
        // The chain has no shortcuts: each link is necessary, and its strict final link decides all three conclusions.
        assert_eq!(facts, chain.into_iter().collect());
        let sufficient = graph.condition_sequences.from_iter(facts).unwrap();
        assert_eq!(graph.truth(condition, &sufficient).unwrap(), expected);
        assert_eq!(graph.prove(condition, &guards).unwrap(), proof);
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Incoming {
    Neither,
    Yes,
    No,
}

#[hegel::test(print_blob = true)]
fn branch_assumptions_are_discharged_only_when_they_were_not_incoming(tc: hegel::TestCase) {
    let incoming = tc.draw(hegel::generators::default::<Incoming>());
    with_graph(|mut graph| {
        let a = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let b = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let choice = graph
            .intern_condition(ConditionNode::Compare(Order::Less, a, b))
            .unwrap();
        let opposite = graph.negate(choice).unwrap();
        let minimum = graph.intern_expr(ExprNode::Select(choice, a, b)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, minimum, a))
            .unwrap();
        let expected: Sequence<_> = match incoming {
            Incoming::Neither => Sequence::default(),
            Incoming::Yes => graph.condition_sequences.from_iter([choice]).unwrap(),
            Incoming::No => graph.condition_sequences.from_iter([opposite]).unwrap(),
        };
        let Proof::Proven(evidence) = graph.prove(condition, &expected).unwrap() else {
            panic!("min(a,b) <= a for every branch");
        };
        assert_eq!(
            {
                let sequence = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(sequence)
                    .copied()
                    .collect::<HashSet<_>>()
            },
            graph.condition_sequences.iter(expected).copied().collect()
        );
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            Truth::Proven
        );
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Context {
    Direct,
    Transitive,
}

#[hegel::test(print_blob = true)]
fn equal_truth_results_retain_the_support_of_their_own_context(tc: hegel::TestCase) {
    let contexts = tc.draw(hegel::generators::default::<Vec<Context>>());
    with_graph(|mut graph| {
        let a = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let b = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let c = graph.intern_expr(ExprNode::Argument(2)).unwrap();
        let first = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, a, b))
            .unwrap();
        let second = graph
            .intern_condition(ConditionNode::Compare(Order::Less, b, c))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Less, a, c))
            .unwrap();
        let contexts = std::iter::once(Context::Direct)
            .chain(std::iter::once(Context::Transitive))
            .chain(contexts);
        for context in contexts {
            let expected: Sequence<_> = match context {
                Context::Direct => graph.condition_sequences.from_iter([required]).unwrap(),
                Context::Transitive => graph
                    .condition_sequences
                    .from_iter([first, second])
                    .unwrap(),
            };
            let Proof::Proven(evidence) = graph.prove(required, &expected).unwrap() else {
                panic!("both contexts establish a < c");
            };
            assert_eq!(
                {
                    let sequence = graph.evidence_sequence(evidence).unwrap();
                    graph
                        .condition_sequences
                        .iter(sequence)
                        .copied()
                        .collect::<HashSet<_>>()
                },
                graph.condition_sequences.iter(expected).copied().collect()
            );
        }
    });
}

#[test]
fn intrinsic_proof_has_empty_support_across_ten_thousand_guard_prefixes() {
    with_graph(|mut graph| {
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Less, zero, one))
            .unwrap();
        let mut guards = Sequence::default();
        for index in 0..10_000 {
            let value = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            let guard = graph
                .intern_condition(ConditionNode::Compare(Order::LessEqual, zero, value))
                .unwrap();
            guards = graph.condition_sequences.push(guards, guard).unwrap();
            let Proof::Proven(evidence) = graph.prove(condition, &guards).unwrap() else {
                panic!("0 < 1 is intrinsic");
            };
            assert_eq!(
                {
                    let sequence = graph.evidence_sequence(evidence).unwrap();
                    graph.condition_sequences.iter(sequence).count()
                },
                0
            );
        }
    });
}
