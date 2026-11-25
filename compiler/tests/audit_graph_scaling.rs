#![feature(rustc_private)]

//! Executable characterization fixtures for the graph-scaling audit.
//!
//! Semantic controls and executed-work gates for shared graph queries.

extern crate rustc_hir;

use rustc_hir::def_id::{DefId, DefIndex};
use shapelint_driver::contracts::graph::{
    ConditionNode, ExprNode, FlowId, Graph, NodeId, evidence::Proof, with_graph,
};
use shapelint_driver::contracts::{Join, Order, ProofGap};
use shapelint_driver::protocols::Flow;

/// Exercises the mixed-guard query path with exactly one relevant target per
/// query.  Every query compares against a distinct target, while the left
/// operand is one shared field chain.
#[derive(Debug)]
struct ReferenceWork {
    nodes: usize,
    combinations: usize,
    retained_nodes: usize,
    memo_entries: usize,
}

fn reference_fixture(depth: usize, queries: usize) -> ReferenceWork {
    with_graph(|mut graph| {
        let mut shared = graph
            .intern_expr(ExprNode::Argument(0))
            .expect("shared root");
        for _ in 0..depth {
            shared = graph
                .intern_expr(ExprNode::Field(shared, 0))
                .expect("shared field");
        }

        let mut cases = Vec::with_capacity(queries);
        for index in 0..queries {
            let target = graph
                .intern_expr(ExprNode::Argument(10_000 + index))
                .expect("target");
            let condition = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, shared, target))
                .expect("comparison");
            let guard = graph
                .intern_condition(ConditionNode::Variant(target, 0))
                .expect("variant guard");
            let guards = graph
                .condition_sequences
                .from_iter([guard])
                .expect("guard sequence");

            // A one-element Variant guard is known and classified as Mixed by
            // prepare_guards, with a target set of cardinality exactly one.
            assert_eq!(graph.condition_sequences.len(guards), 1);
            assert_eq!(graph.known(NodeId::Condition(guard)), Some(()));
            cases.push((condition, guards));
        }

        // The represented expression input remains linear: one shared chain
        // plus one target expression per query. The cases are then proved
        // only after this source-shape check, because proving can intern
        // derived comparison conditions.
        assert_eq!(graph.expression_count(), depth + 1 + queries);

        for (condition, guards) in cases {
            match graph.prove(condition, &guards).expect("proof") {
                Proof::Unknown(ProofGap::Comparison) => {}
                proof => panic!("unrelated variant guard must not prove the comparison: {proof:?}"),
            }
        }
        let counts = ReferenceWork {
            nodes: graph.proof_work.reference_nodes,
            combinations: graph.reference_sets.work.combination_visits,
            retained_nodes: graph.reference_sets.retained_nodes(),
            memo_entries: graph.reference_sets.memo_entries(),
        };
        eprintln!("references depth={depth} queries={queries}: {counts:?}");
        counts
    })
}

#[test]
fn mixed_guard_reference_fixture_keeps_one_target_per_query() {
    let counts = [8, 16, 32, 64].map(|size| reference_fixture(size, size));
    for pair in counts.windows(2) {
        assert!(pair[1].nodes <= 2 * pair[0].nodes, "{counts:?}");
        assert!(
            pair[1].combinations <= 3 * pair[0].combinations,
            "persistent set work: {counts:?}"
        );
        assert!(
            pair[1].retained_nodes <= 3 * pair[0].retained_nodes,
            "retained set nodes: {counts:?}"
        );
        assert!(
            pair[1].memo_entries <= 3 * pair[0].memo_entries,
            "retained set memo: {counts:?}"
        );
    }
}

fn flow_values<'g>(graph: &Graph<'g>, flow: FlowId<'g>) -> Vec<FlowId<'g>> {
    let Flow::Alternatives(mut current) = graph[flow].clone() else {
        return vec![flow];
    };
    let mut values = Vec::new();
    while let Some(id) = current {
        values.push(graph[id].value);
        current = graph[id].previous;
    }
    values.reverse();
    values
}

/// Repeats the same hull join over two disjoint histories.  This models the
/// per-resource call pattern in protocol merging while keeping the public
/// result canonical and preserving history order.
fn flow_join_fixture(history: usize, repeats: usize) {
    with_graph(|mut graph| {
        let incoming = graph.intern_flow(Flow::Incoming).expect("incoming");
        let left = graph
            .intern_flow(Flow::Call {
                callee: DefId::local(DefIndex::from_usize(100_000)),
                argument: 0,
                input: incoming,
            })
            .expect("left flow");
        let right_values: Vec<_> = (0..history)
            .map(|index| {
                graph
                    .intern_flow(Flow::Call {
                        callee: DefId::local(DefIndex::from_usize(index)),
                        argument: index,
                        input: incoming,
                    })
                    .expect("right flow")
            })
            .collect();
        let right = graph
            .intern_alternatives(right_values.iter().copied())
            .expect("right history");

        let first = graph
            .join_flow(left, right, Join::Hull, None)
            .expect("first join");
        let expected: Vec<_> = std::iter::once(left)
            .chain(right_values.iter().copied())
            .collect();
        assert_eq!(flow_values(&graph, first), expected);

        let steps = graph.proof_work.flow_join_steps;
        for _ in 0..repeats {
            let joined = graph
                .join_flow(left, right, Join::Hull, None)
                .expect("repeated join");
            assert_eq!(joined, first);
            assert_eq!(flow_values(&graph, joined), expected);
            assert_eq!(graph.proof_work.flow_join_steps, steps);
        }
        eprintln!("flow history={history} repeats={repeats}: {steps} steps");
        let widened = graph
            .join_flow(left, right, Join::Widen, None)
            .expect("widen");
        assert_eq!(graph[widened], Flow::Unknown);
        let condition = graph
            .intern_condition(ConditionNode::Unknown)
            .expect("condition");
        let selected = graph
            .join_flow(left, right, Join::Hull, Some(condition))
            .expect("select");
        assert_eq!(graph[selected], Flow::Select(condition, left, right));
        let reversed = graph
            .join_flow(right, left, Join::Hull, None)
            .expect("reverse join");
        let reversed_values: Vec<_> = right_values.into_iter().chain([left]).collect();
        assert_eq!(flow_values(&graph, reversed), reversed_values);
    });
}

#[test]
fn repeated_disjoint_flow_joins_preserve_one_canonical_history() {
    for &(history, repeats) in &[(8, 8), (16, 16), (32, 32)] {
        flow_join_fixture(history, repeats);
    }
}
