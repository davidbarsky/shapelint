#![feature(rustc_private)]

use std::collections::HashSet;

use shapelint_driver::contracts::graph::evidence::Proof;
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
use shapelint_driver::contracts::{Order, ProofGap, Truth};
use shapelint_driver::sequence::Sequence;

#[hegel::test(print_blob = true)]
fn shared_endpoints_preserve_transitive_evidence_across_context_shapes(tc: hegel::TestCase) {
    let noise = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_graph(|mut graph| {
        let input = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let output = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let predicate = graph.from_expr(input, 1).unwrap();
        let composite = graph.intern_expr(ExprNode::Test(predicate)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let evidence = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, composite, one))
            .unwrap();
        let bridge = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, composite, output))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, output, one))
            .unwrap();
        let mut guards = {
            let values = [evidence];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        assert_ne!(graph.truth(required, &guards).unwrap(), Truth::Proven);
        let noise_count = noise.len();
        let noise = noise.into_iter().enumerate();
        for (index, value) in noise {
            let input = graph.intern_expr(ExprNode::Argument(index + 2)).unwrap();
            let value = graph
                .intern_expr(ExprNode::Number(u128::from(value)))
                .unwrap();
            {
                let value = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, input, value))
                    .unwrap();
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
        }
        {
            let value = bridge;
            guards = graph.condition_sequences.push(guards, value).unwrap();
        };
        {
            let value = evidence;
            guards = graph.condition_sequences.push(guards, value).unwrap();
        };
        let reverse = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, one, output))
            .unwrap();
        let another_input = graph
            .intern_expr(ExprNode::Argument(noise_count + 2))
            .unwrap();
        let another_predicate = graph.from_expr(another_input, 1).unwrap();
        let another_composite = graph
            .intern_expr(ExprNode::Test(another_predicate))
            .unwrap();
        let another_evidence = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, another_composite, one))
            .unwrap();
        {
            let value = another_evidence;
            guards = graph.condition_sequences.push(guards, value).unwrap();
        };
        let Proof::Proven(proof_evidence) = graph.prove(required, &guards).unwrap() else {
            panic!("the shared endpoint proves the forward equality");
        };
        let facts: HashSet<_> = {
            let values = graph.evidence_sequence(proof_evidence).unwrap();
            graph.condition_sequences.iter(values).copied().collect()
        };
        assert_eq!(facts, HashSet::from([bridge, evidence]));
        let Proof::Proven(proof_evidence) = graph.prove(reverse, &guards).unwrap() else {
            panic!("the shared endpoint proves the reverse equality");
        };
        let facts: HashSet<_> = {
            let values = graph.evidence_sequence(proof_evidence).unwrap();
            graph.condition_sequences.iter(values).copied().collect()
        };
        assert_eq!(facts, HashSet::from([bridge, evidence]));
        let Proof::Proven(evidence) = graph.prove(another_evidence, &guards).unwrap() else {
            panic!("the separate guard proves itself");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![another_evidence]
        );
        let refuted = graph.negate(required).unwrap();
        let other = {
            let values = [refuted];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        assert_eq!(graph.truth(required, &other).unwrap(), Truth::Refuted);
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
        assert_eq!(graph.truth(required, &other).unwrap(), Truth::Refuted);
        let reordered = {
            let values = graph
                .condition_sequences
                .iter(guards)
                .copied()
                .rev()
                .collect::<Vec<_>>();
            graph.condition_sequences.from_iter(values).unwrap()
        };
        assert_eq!(graph.truth(required, &reordered).unwrap(), Truth::Proven);
        let independently_built = {
            let values = graph
                .condition_sequences
                .iter(guards)
                .copied()
                .collect::<Vec<_>>();
            graph.condition_sequences.from_iter(values).unwrap()
        };
        assert_eq!(
            graph.truth(required, &independently_built).unwrap(),
            Truth::Proven
        );
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
        assert_eq!(graph.truth(required, &other).unwrap(), Truth::Refuted);
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Direction {
    Forward,
    Backward,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Conclusion {
    Equal,
    NotEqual,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct EqualChain {
    links: Vec<Direction>,
    query: Direction,
    conclusion: Conclusion,
    unrelated: Vec<u64>,
}

#[hegel::test(print_blob = true)]
fn equality_evidence_retains_both_transitive_directions(tc: hegel::TestCase) {
    let EqualChain {
        links,
        query,
        conclusion,
        unrelated,
    } = tc.draw(hegel::generators::default::<EqualChain>());
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let mut last = first;
        let mut chain = Vec::new();
        let directions = std::iter::once(Direction::Forward)
            .chain(links)
            .chain(std::iter::once(Direction::Backward))
            .enumerate();
        for (index, direction) in directions {
            let next = graph.intern_expr(ExprNode::Argument(index + 1)).unwrap();
            let (left, right) = match direction {
                Direction::Forward => (last, next),
                Direction::Backward => (next, last),
            };
            chain.push(
                graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, left, right))
                    .unwrap(),
            );
            last = next;
        }
        let mut guards = graph
            .condition_sequences
            .from_iter(chain.iter().copied())
            .unwrap();
        let unrelated = unrelated.into_iter().enumerate();
        for (index, value) in unrelated {
            let input = graph
                .intern_expr(ExprNode::Argument(chain.len() + index + 1))
                .unwrap();
            let value = graph
                .intern_expr(ExprNode::Number(u128::from(value)))
                .unwrap();
            {
                let value = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, input, value))
                    .unwrap();
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
        }
        let (left, right) = match query {
            Direction::Forward => (first, last),
            Direction::Backward => (last, first),
        };
        let (order, expected) = match conclusion {
            Conclusion::Equal => (Order::Equal, Truth::Proven),
            Conclusion::NotEqual => (Order::NotEqual, Truth::Refuted),
        };
        let required = graph
            .intern_condition(ConditionNode::Compare(order, left, right))
            .unwrap();
        let proof = graph.prove(required, &guards).unwrap();
        assert_eq!(Truth::from(proof), expected);
        let evidence = match proof {
            Proof::Proven(evidence) | Proof::Refuted(evidence) => evidence,
            Proof::Unknown(gap) => panic!("every link equates the endpoints: {gap:?}"),
        };
        let facts: HashSet<_> = {
            let values = graph.evidence_sequence(evidence).unwrap();
            graph.condition_sequences.iter(values).copied().collect()
        };
        assert_eq!(facts, chain.into_iter().collect());
        let sufficient = graph.condition_sequences.from_iter(facts).unwrap();
        assert_eq!(graph.truth(required, &sufficient).unwrap(), expected);
    });
}

#[hegel::test(print_blob = true)]
fn one_inclusive_direction_does_not_establish_equality(tc: hegel::TestCase) {
    let conclusion = tc.draw(hegel::generators::default::<Conclusion>());
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let middle = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let last = graph.intern_expr(ExprNode::Argument(2)).unwrap();
        let guards = {
            let values = [
                graph
                    .intern_condition(ConditionNode::Compare(Order::LessEqual, first, middle))
                    .unwrap(),
                graph
                    .intern_condition(ConditionNode::Compare(Order::LessEqual, middle, last))
                    .unwrap(),
            ];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        let order = match conclusion {
            Conclusion::Equal => Order::Equal,
            Conclusion::NotEqual => Order::NotEqual,
        };
        let required = graph
            .intern_condition(ConditionNode::Compare(order, first, last))
            .unwrap();
        let Proof::Unknown(_) = graph.prove(required, &guards).unwrap() else {
            panic!("both equal and unequal endpoint values satisfy an inclusive chain");
        };
    });
}

#[test]
fn a_strict_witness_keeps_precedence_over_conflicting_equality_guards() {
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let middle = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let last = graph.intern_expr(ExprNode::Argument(2)).unwrap();
        let strict = graph
            .intern_condition(ConditionNode::Compare(Order::Less, first, last))
            .unwrap();
        let guards = {
            let values = [
                graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, first, middle))
                    .unwrap(),
                graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, middle, last))
                    .unwrap(),
                strict,
            ];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, first, last))
            .unwrap();
        let Proof::Refuted(evidence) = graph.prove(required, &guards).unwrap() else {
            panic!("the existing strict path decides equality before inclusive evidence");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![strict]
        );
    });
}

#[hegel::test(print_blob = true)]
fn repeated_guard_prefixes_keep_selection_results_and_evidence_separate(tc: hegel::TestCase) {
    let repetitions = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_graph(|mut graph| {
        let left = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let right = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let choice = graph
            .intern_condition(ConditionNode::Compare(Order::Less, left, right))
            .unwrap();
        let opposite = graph.negate(choice).unwrap();
        let yes = graph.intern_expr(ExprNode::Number(4)).unwrap();
        let no = graph.intern_expr(ExprNode::Number(9)).unwrap();
        let selected = graph
            .intern_expr(ExprNode::Select(choice, yes, no))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, selected, yes))
            .unwrap();
        let mut positive = Sequence::default();
        let mut negative = Sequence::default();
        for _ in repetitions {
            {
                let value = choice;
                positive = graph.condition_sequences.push(positive, value).unwrap();
            };
            {
                let value = opposite;
                negative = graph.condition_sequences.push(negative, value).unwrap();
            };
        }
        {
            let value = choice;
            positive = graph.condition_sequences.push(positive, value).unwrap();
        };
        {
            let value = opposite;
            negative = graph.condition_sequences.push(negative, value).unwrap();
        };
        let Proof::Proven(evidence) = graph.prove(required, &positive).unwrap() else {
            panic!("positive guard must prove the selected value");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![choice]
        );
        let Proof::Refuted(evidence) = graph.prove(required, &negative).unwrap() else {
            panic!("negative guard must refute the selected value");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![opposite]
        );
        let rebuilt = {
            let values = graph
                .condition_sequences
                .iter(positive)
                .copied()
                .collect::<Vec<_>>();
            graph.condition_sequences.from_iter(values).unwrap()
        };
        assert_eq!(graph.truth(required, &rebuilt).unwrap(), Truth::Proven);
        assert_eq!(graph.truth(required, &negative).unwrap(), Truth::Refuted);
    });
}

#[hegel::test(print_blob = true)]
fn generated_guard_prefixes_preserve_first_variant_witness(tc: hegel::TestCase) {
    let (variants, query) = tc.draw(hegel::generators::default::<(Vec<u8>, u8)>());
    with_graph(|mut graph| {
        let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let required = graph
            .intern_condition(ConditionNode::Variant(argument, usize::from(query)))
            .unwrap();
        let mut guards = Sequence::default();
        let mut expected = Vec::new();
        for variant in variants {
            let guard = graph
                .intern_condition(ConditionNode::Variant(argument, usize::from(variant)))
                .unwrap();
            {
                let value = guard;
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
            expected.push(variant);
            let truth = match expected.first() {
                Some(first) if *first == query => Truth::Proven,
                Some(_) => Truth::Refuted,
                None => unreachable!("the prefix contains the new guard"),
            };
            assert_eq!(graph.truth(required, &guards).unwrap(), truth);
            let rebuilt = {
                let values = graph
                    .condition_sequences
                    .iter(guards)
                    .copied()
                    .collect::<Vec<_>>();
                graph.condition_sequences.from_iter(values).unwrap()
            };
            assert_eq!(graph.truth(required, &rebuilt).unwrap(), truth);
        }
    });
}

#[hegel::test(print_blob = true)]
fn unknown_guards_do_not_change_first_variant_evidence(tc: hegel::TestCase) {
    let variants = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let unknown = graph.intern_condition(ConditionNode::Unknown).unwrap();
        let first = graph
            .intern_condition(ConditionNode::Variant(value, 0))
            .unwrap();
        let second = graph
            .intern_condition(ConditionNode::Variant(value, 1))
            .unwrap();
        let other = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let unrelated = graph
            .intern_condition(ConditionNode::Variant(other, 0))
            .unwrap();
        let mut guards = {
            let values = [unknown, unrelated, first, unknown, second, first];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        for variant in variants {
            let guard = graph
                .intern_condition(ConditionNode::Variant(value, usize::from(variant)))
                .unwrap();
            {
                let value = guard;
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
        }
        let Proof::Proven(evidence) = graph.prove(first, &guards).unwrap() else {
            panic!("the first variant decides the query");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![first]
        );
        let Proof::Refuted(evidence) = graph.prove(second, &guards).unwrap() else {
            panic!("the first variant decides the query");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![first]
        );
        let Proof::Proven(evidence) = graph.prove(first, &guards).unwrap() else {
            panic!("the first variant decides the query");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![first]
        );
        let Proof::Refuted(evidence) = graph.prove(second, &guards).unwrap() else {
            panic!("the first variant decides the query");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![first]
        );
    });
}

#[hegel::test(print_blob = true)]
fn mixed_contexts_preserve_selection_and_return_evidence_across_queries(tc: hegel::TestCase) {
    let noise = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_graph(|mut graph| {
        use shapelint_driver::contracts::graph::TargetNode;
        let input = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let other = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let choice = graph
            .intern_condition(ConditionNode::Compare(Order::Less, input, other))
            .unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let selected = graph
            .intern_expr(ExprNode::Select(choice, one, zero))
            .unwrap();
        let selected_guard = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, selected, one))
            .unwrap();
        let returned = graph
            .intern_condition(ConditionNode::Returned(
                TargetNode::Indirect(input),
                Sequence::EMPTY,
            ))
            .unwrap();
        let returned_value = graph.intern_expr(ExprNode::Test(returned)).unwrap();
        let returned_query = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, returned_value, one))
            .unwrap();
        let unknown = graph.intern_condition(ConditionNode::Unknown).unwrap();
        let mut guards = {
            let values = [unknown, choice, selected_guard, returned];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        let noise = noise.into_iter().enumerate();
        for (index, value) in noise {
            let argument = graph.intern_expr(ExprNode::Argument(index + 2)).unwrap();
            let number = graph
                .intern_expr(ExprNode::Number(u128::from(value)))
                .unwrap();
            {
                let value = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, argument, number))
                    .unwrap();
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
        }
        let Proof::Proven(evidence) = graph.prove(returned_query, &guards).unwrap() else {
            panic!("the corresponding guard proves the query");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![returned]
        );
        let Proof::Proven(evidence) = graph.prove(selected_guard, &guards).unwrap() else {
            panic!("the corresponding guard proves the query");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![selected_guard]
        );
        let Proof::Proven(evidence) = graph.prove(returned_query, &guards).unwrap() else {
            panic!("the corresponding guard proves the query");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![returned]
        );
        let Proof::Proven(evidence) = graph.prove(selected_guard, &guards).unwrap() else {
            panic!("the corresponding guard proves the query");
        };
        assert_eq!(
            {
                let values = graph.evidence_sequence(evidence).unwrap();
                graph
                    .condition_sequences
                    .iter(values)
                    .copied()
                    .collect::<Vec<_>>()
            },
            vec![selected_guard]
        );
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum GuardKind {
    Variant,
    Boundary,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum GuardPolarity {
    Positive,
    Negative,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct GuardScenario {
    kind: GuardKind,
    polarity: GuardPolarity,
    unrelated: Vec<u8>,
}

#[hegel::test(print_blob = true)]
fn unknown_proofs_are_independent_of_guard_contexts(tc: hegel::TestCase) {
    let GuardScenario {
        kind,
        polarity,
        unrelated,
    } = tc.draw(hegel::generators::default::<GuardScenario>());
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let index = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let unknown = graph.intern_condition(ConditionNode::Unknown).unwrap();
        let positive = graph
            .intern_condition(match kind {
                GuardKind::Variant => ConditionNode::Variant(value, 0),
                GuardKind::Boundary => ConditionNode::Boundary(value, index),
            })
            .unwrap();
        let guard = match polarity {
            GuardPolarity::Positive => positive,
            GuardPolarity::Negative => graph.negate(positive).unwrap(),
        };
        let mut guards = Sequence::default();
        assert_eq!(
            graph.prove(unknown, &guards).unwrap(),
            Proof::Unknown(ProofGap::Value)
        );
        {
            let value = unknown;
            guards = graph.condition_sequences.push(guards, value).unwrap();
        };
        {
            let value = guard;
            guards = graph.condition_sequences.push(guards, value).unwrap();
        };
        let unrelated = unrelated.into_iter().enumerate();
        for (i, variant) in unrelated {
            let other = graph.intern_expr(ExprNode::Argument(i + 2)).unwrap();
            let fact = graph
                .intern_condition(ConditionNode::Variant(other, usize::from(variant)))
                .unwrap();
            {
                let value = fact;
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
            {
                let value = guard;
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
            assert_eq!(
                graph.prove(unknown, &guards).unwrap(),
                Proof::Unknown(ProofGap::Value)
            );
        }
        let rebuilt = {
            let values = graph
                .condition_sequences
                .iter(guards)
                .copied()
                .collect::<Vec<_>>();
            graph.condition_sequences.from_iter(values).unwrap()
        };
        assert_eq!(
            graph.prove(unknown, &rebuilt).unwrap(),
            Proof::Unknown(ProofGap::Value)
        );
        assert_eq!(
            graph.prove(unknown, &guards).unwrap(),
            Proof::Unknown(ProofGap::Value)
        );
    });
}

#[hegel::test(print_blob = true)]
fn variant_and_boundary_guards_preserve_exact_evidence_across_contexts(tc: hegel::TestCase) {
    let GuardScenario {
        kind,
        polarity,
        unrelated,
    } = tc.draw(hegel::generators::default::<GuardScenario>());
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let index = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let positive = graph
            .intern_condition(match kind {
                GuardKind::Variant => ConditionNode::Variant(value, 0),
                GuardKind::Boundary => ConditionNode::Boundary(value, index),
            })
            .unwrap();
        let negative = graph.negate(positive).unwrap();
        let (guard, positive_truth, negative_truth) = match polarity {
            GuardPolarity::Positive => (positive, Truth::Proven, Truth::Refuted),
            GuardPolarity::Negative => (negative, Truth::Refuted, Truth::Proven),
        };
        let mut guards = Sequence::default();
        let unrelated = unrelated.into_iter().enumerate();
        for (i, variant) in unrelated {
            let other = graph.intern_expr(ExprNode::Argument(i + 2)).unwrap();
            {
                let value = graph
                    .intern_condition(ConditionNode::Variant(other, usize::from(variant)))
                    .unwrap();
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
            {
                let value = graph
                    .intern_condition(ConditionNode::NotBoundary(other, index))
                    .unwrap();
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
        }
        {
            let value = guard;
            guards = graph.condition_sequences.push(guards, value).unwrap();
        };
        let rebuilt = {
            let values = graph
                .condition_sequences
                .iter(guards)
                .copied()
                .collect::<Vec<_>>();
            graph.condition_sequences.from_iter(values).unwrap()
        };
        {
            let proof = graph.prove(positive, &guards).unwrap();
            assert_eq!(Truth::from(proof), positive_truth);
            let evidence = match proof {
                Proof::Proven(evidence) | Proof::Refuted(evidence) => evidence,
                Proof::Unknown(gap) => panic!("the exact guard decides the query: {gap:?}"),
            };
            assert_eq!(
                {
                    let values = graph.evidence_sequence(evidence).unwrap();
                    graph
                        .condition_sequences
                        .iter(values)
                        .copied()
                        .collect::<Vec<_>>()
                },
                vec![guard]
            );
            let proof = graph.prove(negative, &guards).unwrap();
            assert_eq!(Truth::from(proof), negative_truth);
            let evidence = match proof {
                Proof::Proven(evidence) | Proof::Refuted(evidence) => evidence,
                Proof::Unknown(gap) => panic!("the exact guard decides the negation: {gap:?}"),
            };
            assert_eq!(
                {
                    let values = graph.evidence_sequence(evidence).unwrap();
                    graph
                        .condition_sequences
                        .iter(values)
                        .copied()
                        .collect::<Vec<_>>()
                },
                vec![guard]
            );
        }
        assert_eq!(graph.truth(positive, &rebuilt).unwrap(), positive_truth);
        assert_eq!(graph.truth(negative, &rebuilt).unwrap(), negative_truth);
        assert_eq!(graph.truth(positive, &guards).unwrap(), positive_truth);
    });
}

#[hegel::test(print_blob = true)]
fn selection_retains_variant_and_boundary_choice_guards(tc: hegel::TestCase) {
    let GuardScenario {
        kind,
        polarity,
        unrelated,
    } = tc.draw(hegel::generators::default::<GuardScenario>());
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let index = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let choice = graph
            .intern_condition(match kind {
                GuardKind::Variant => ConditionNode::Variant(value, 0),
                GuardKind::Boundary => ConditionNode::Boundary(value, index),
            })
            .unwrap();
        let (guard, expected) = match polarity {
            GuardPolarity::Positive => (choice, Truth::Proven),
            GuardPolarity::Negative => (graph.negate(choice).unwrap(), Truth::Refuted),
        };
        let yes = graph.intern_expr(ExprNode::Number(4)).unwrap();
        let no = graph.intern_expr(ExprNode::Number(9)).unwrap();
        let selected = graph
            .intern_expr(ExprNode::Select(choice, yes, no))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, selected, yes))
            .unwrap();
        let mut guards = Sequence::default();
        let unrelated = unrelated.into_iter().enumerate();
        for (i, variant) in unrelated {
            let other = graph.intern_expr(ExprNode::Argument(i + 2)).unwrap();
            {
                let value = graph
                    .intern_condition(ConditionNode::Variant(other, usize::from(variant)))
                    .unwrap();
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
        }
        {
            let value = guard;
            guards = graph.condition_sequences.push(guards, value).unwrap();
        };
        let rebuilt = {
            let values = graph
                .condition_sequences
                .iter(guards)
                .copied()
                .collect::<Vec<_>>();
            graph.condition_sequences.from_iter(values).unwrap()
        };
        {
            let proof = graph.prove(required, &guards).unwrap();
            assert_eq!(Truth::from(proof), expected);
            let evidence = match proof {
                Proof::Proven(evidence) | Proof::Refuted(evidence) => evidence,
                Proof::Unknown(gap) => panic!("the choice guard decides the selection: {gap:?}"),
            };
            assert_eq!(
                {
                    let values = graph.evidence_sequence(evidence).unwrap();
                    graph
                        .condition_sequences
                        .iter(values)
                        .copied()
                        .collect::<Vec<_>>()
                },
                vec![guard]
            );
        }
        assert_eq!(graph.truth(required, &rebuilt).unwrap(), expected);
        assert_eq!(graph.truth(required, &guards).unwrap(), expected);
    });
}
