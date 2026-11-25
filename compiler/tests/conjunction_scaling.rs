#![feature(rustc_private)]

use shapelint_driver::contracts::graph::{
    ConditionId, ConditionNode, ExprNode, Graph, ProofWork, with_graph,
};
use shapelint_driver::contracts::{Order, ProofGap, Truth};
use shapelint_driver::sequence::Sequence;

fn unknown_conditions<'g>(graph: &mut Graph<'g>, count: usize) -> Vec<ConditionId<'g>> {
    (0..count)
        .map(|index| {
            let left = graph
                .intern_expr(ExprNode::Argument(index))
                .expect("left expression fits");
            let right = graph
                .intern_expr(ExprNode::Argument(index + count + 1))
                .expect("right expression fits");
            graph
                .intern_condition(ConditionNode::Compare(Order::LessEqual, left, right))
                .expect("condition fits")
        })
        .collect()
}

fn growing_conjunction_work(size: usize) -> ProofWork {
    with_graph(|mut graph| {
        let conditions = unknown_conditions(&mut graph, size);
        let mut sequence = Sequence::EMPTY;
        for condition in conditions {
            sequence = graph
                .condition_sequences
                .push(sequence, condition)
                .expect("sequence fits");
            assert_eq!(
                graph
                    .conjunction(&sequence, &Sequence::EMPTY)
                    .expect("conjunction fits"),
                Truth::Unknown(ProofGap::Comparison)
            );
        }
        graph.proof_work
    })
}

#[test]
fn repeated_conjunction_reuses_the_exact_ordered_query() {
    with_graph(|mut graph| {
        let conditions = unknown_conditions(&mut graph, 32);
        let sequence = graph
            .condition_sequences
            .from_iter(conditions.iter().copied())
            .expect("sequence fits");

        assert_eq!(
            graph
                .conjunction(&sequence, &Sequence::EMPTY)
                .expect("conjunction fits"),
            Truth::Unknown(ProofGap::Comparison)
        );
        let first = graph.proof_work;
        assert_eq!(
            graph
                .conjunction(&sequence, &Sequence::EMPTY)
                .expect("conjunction fits"),
            Truth::Unknown(ProofGap::Comparison)
        );

        assert_eq!(
            graph.proof_work.conjunction_queries,
            first.conjunction_queries + 1
        );
        assert_eq!(
            graph.proof_work.conjunction_condition_visits,
            first.conjunction_condition_visits
        );
        assert!(graph.proof_work.conjunction_cache_hits > first.conjunction_cache_hits);
        assert!(graph.proof_work.conjunction_cache_entries > 0);
    });
}

#[test]
fn growing_conjunctions_reuse_shared_sequence_fragments() {
    let measured = [8, 16, 32, 64].map(growing_conjunction_work);
    eprintln!("growing conjunctions: {measured:?}");
    let visits = measured.map(|work| work.conjunction_condition_visits);
    assert_eq!(visits, [8, 16, 32, 64]);
    let entries = measured.map(|work| work.conjunction_cache_entries);
    let observations = [8, 16, 32, 64].into_iter().zip(measured);
    for (size, work) in observations {
        assert!(work.conjunction_cache_hits >= size - 1);
        assert!(
            work.conjunction_cache_entries >= size,
            "the conjunction cache must retain each distinct condition leaf: {work:?}"
        );
    }
    for window in entries.windows(2) {
        assert!(
            window[1] <= window[0] * 3,
            "fragment retention grew faster than the measured near-linearithmic bound: {entries:?}"
        );
    }
}

#[test]
fn conjunction_unknown_then_proven_preserves_unknown() {
    with_graph(|mut graph| {
        let unknown = unknown_conditions(&mut graph, 1)
            .pop()
            .expect("one condition");
        let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero fits");
        let one = graph.intern_expr(ExprNode::Number(1)).expect("one fits");
        let proven = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, zero, one))
            .expect("condition fits");
        let sequence = graph
            .condition_sequences
            .from_iter([unknown, proven])
            .expect("sequence fits");

        assert_eq!(
            graph
                .conjunction(&sequence, &Sequence::EMPTY)
                .expect("conjunction fits"),
            Truth::Unknown(ProofGap::Comparison)
        );
    });
}

#[test]
fn conjunction_unknown_reason_follows_sequence_order() {
    with_graph(|mut graph| {
        let comparison = unknown_conditions(&mut graph, 1)
            .pop()
            .expect("one condition");
        let variant_value = graph
            .intern_expr(ExprNode::Argument(100))
            .expect("argument fits");
        let variant = graph
            .intern_condition(ConditionNode::Variant(variant_value, 0))
            .expect("condition fits");
        let comparison_then_variant = graph
            .condition_sequences
            .from_iter([comparison, variant])
            .expect("sequence fits");
        let variant_then_comparison = graph
            .condition_sequences
            .from_iter([variant, comparison])
            .expect("sequence fits");

        assert_eq!(
            graph
                .conjunction(&comparison_then_variant, &Sequence::EMPTY)
                .expect("conjunction fits"),
            Truth::Unknown(ProofGap::Variant)
        );
        assert_eq!(
            graph
                .conjunction(&variant_then_comparison, &Sequence::EMPTY)
                .expect("conjunction fits"),
            Truth::Unknown(ProofGap::Comparison)
        );
    });
}

#[test]
fn conjunction_refuted_short_circuits_and_wins() {
    with_graph(|mut graph| {
        let unknown = unknown_conditions(&mut graph, 1)
            .pop()
            .expect("one condition");
        let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero fits");
        let one = graph.intern_expr(ExprNode::Number(1)).expect("one fits");
        let refuted = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, one, zero))
            .expect("condition fits");
        let refuted_then_unknown = graph
            .condition_sequences
            .from_iter([refuted, unknown])
            .expect("sequence fits");
        let unknown_then_refuted = graph
            .condition_sequences
            .from_iter([unknown, refuted])
            .expect("sequence fits");

        assert_eq!(
            graph
                .conjunction(&refuted_then_unknown, &Sequence::EMPTY)
                .expect("conjunction fits"),
            Truth::Refuted
        );
        let visits_after_short_circuit = graph.proof_work.conjunction_condition_visits;
        assert_eq!(
            graph
                .conjunction(&unknown_then_refuted, &Sequence::EMPTY)
                .expect("conjunction fits"),
            Truth::Refuted
        );
        assert_eq!(
            graph.proof_work.conjunction_condition_visits,
            visits_after_short_circuit + 1
        );
    });
}

#[test]
fn conjunction_guard_context_is_part_of_the_cache_key() {
    with_graph(|mut graph| {
        let condition = unknown_conditions(&mut graph, 1)
            .pop()
            .expect("one condition");
        let sequence = graph
            .condition_sequences
            .from_iter([condition])
            .expect("sequence fits");

        assert_eq!(
            graph
                .conjunction(&sequence, &Sequence::EMPTY)
                .expect("conjunction fits"),
            Truth::Unknown(ProofGap::Comparison)
        );
        assert_eq!(
            graph
                .conjunction(&sequence, &sequence)
                .expect("conjunction fits"),
            Truth::Proven
        );
    });
}
