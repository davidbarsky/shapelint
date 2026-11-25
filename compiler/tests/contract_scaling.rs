#![feature(rustc_private)]

//! Bounds proof work and characterizes recursive invalidation work.

extern crate rustc_hir;

use rustc_hir::def_id::{DefId, DefIndex};
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, ProofWork, with_graph};
use shapelint_driver::contracts::recursion::Recursion;
use shapelint_driver::contracts::{Order, ProofGap, Truth};

fn unreachable_comparisons(nodes: usize, queries: usize) -> ProofWork {
    with_graph(|mut graph| {
        let values: Vec<_> = (0..nodes)
            .map(|index| graph.intern_expr(ExprNode::Argument(index)).unwrap())
            .collect();
        let mut guards = Vec::new();
        for index in 0..nodes {
            guards.push(
                graph
                    .intern_condition(ConditionNode::Compare(
                        Order::LessEqual,
                        values[index],
                        values[(index + 1) % nodes],
                    ))
                    .unwrap(),
            );
        }
        let guards = graph.condition_sequences.from_iter(guards).unwrap();
        let mut conditions = Vec::new();
        for index in nodes..nodes + queries {
            let unrelated = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            let condition = graph
                .intern_condition(ConditionNode::Compare(
                    Order::LessEqual,
                    values[0],
                    unrelated,
                ))
                .unwrap();
            assert_eq!(
                graph.truth(condition, &guards).unwrap(),
                Truth::Unknown(ProofGap::Comparison)
            );
            conditions.push(condition);
        }
        let work = graph.proof_work;
        for condition in conditions {
            assert_eq!(
                graph.truth(condition, &guards).unwrap(),
                Truth::Unknown(ProofGap::Comparison)
            );
        }
        assert_eq!(
            graph.proof_work, work,
            "identical queries reuse their proof"
        );
        work
    })
}

#[test]
fn distinct_unreachable_targets_share_one_comparison_search() {
    let observations = [8, 16, 32].map(|size| {
        let work = unreachable_comparisons(size, size);
        eprintln!("comparison cycle {size}, distinct targets {size}: {work:?}");
        work
    });
    assert_eq!(observations.map(|work| work.comparison_states), [8, 16, 32]);
    assert_eq!(observations.map(|work| work.comparison_edges), [8, 16, 32]);
    assert_eq!(observations.map(|work| work.guard_segments), [0; 3]);
    assert_eq!(
        observations.map(|work| work.guard_projection_fragments),
        [0; 3]
    );
}

#[hegel::test(print_blob = true)]
fn comparison_search_visits_each_state_once_for_many_targets(tc: hegel::TestCase) {
    #[derive(Debug, hegel::DefaultGenerator)]
    struct Search {
        additional_nodes: Vec<()>,
        targets: Vec<()>,
    }
    let Search {
        additional_nodes,
        targets,
    } = tc.draw(hegel::generators::default::<Search>());
    let nodes = 2 + additional_nodes.len();
    let visits = match targets.as_slice() {
        [] => 0,
        _ => nodes,
    };
    let work = unreachable_comparisons(nodes, targets.len());
    assert_eq!(work.comparison_states, visits);
    assert_eq!(work.comparison_edges, visits);
    assert_eq!(work.guard_segments, 0);
    assert_eq!(work.guard_projection_fragments, 0);
}

#[test]
fn short_comparison_proofs_leave_the_unneeded_frontier_pending() {
    with_graph(|mut graph| {
        let values: Vec<_> = (0..35)
            .map(|index| graph.intern_expr(ExprNode::Argument(index)).unwrap())
            .collect();
        let mut edges = vec![(0, 1), (1, 2), (0, 3)];
        edges.extend((3..34).map(|index| (index, index + 1)));
        let conditions: Vec<_> = edges
            .into_iter()
            .map(|(left, right)| {
                graph
                    .intern_condition(ConditionNode::Compare(
                        Order::LessEqual,
                        values[left],
                        values[right],
                    ))
                    .unwrap()
            })
            .collect();
        let guards = graph.condition_sequences.from_iter(conditions).unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(
                Order::LessEqual,
                values[0],
                values[2],
            ))
            .unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
        assert_eq!(graph.proof_work.comparison_states, 2);
        assert_eq!(graph.proof_work.comparison_edges, 3);
    });
}

fn variant_projections(count: usize) -> ProofWork {
    with_graph(|mut graph| {
        let conditions: Vec<_> = (0..count)
            .map(|index| {
                let value = graph.intern_expr(ExprNode::Argument(index)).unwrap();
                graph
                    .intern_condition(ConditionNode::Variant(value, 0))
                    .unwrap()
            })
            .collect();
        let guards = graph
            .condition_sequences
            .from_iter(conditions.iter().copied())
            .unwrap();
        for &condition in &conditions {
            let proof = graph.prove(condition, &guards).unwrap();
            let shapelint_driver::contracts::graph::evidence::Proof::Proven(evidence) = proof
            else {
                panic!("own variant guard proves the condition: {proof:?}");
            };
            let evidence = graph.evidence_sequence(evidence).unwrap();
            let evidence: Vec<_> = graph.condition_sequences.iter(evidence).copied().collect();
            assert_eq!(evidence, [condition]);
        }
        let work = graph.proof_work;
        for condition in conditions {
            assert_eq!(graph.truth(condition, &guards).unwrap(), Truth::Proven);
        }
        assert_eq!(
            graph.proof_work, work,
            "identical projections reuse their result"
        );
        work
    })
}

#[test]
fn independent_variant_queries_visit_only_indexed_segments() {
    let observations = [8, 16, 32].map(|size| {
        let work = variant_projections(size);
        eprintln!("variant guards {size}, distinct queries {size}: {work:?}");
        work
    });
    assert_eq!(observations.map(|work| work.comparison_states), [0; 3]);
    assert_eq!(observations.map(|work| work.comparison_edges), [0; 3]);
    assert_eq!(observations.map(|work| work.guard_segments), [16, 32, 64]);
    assert_eq!(
        observations.map(|work| work.guard_projection_fragments),
        [46, 110, 254]
    );
}

#[hegel::test(print_blob = true)]
fn guard_projection_work_is_bounded_for_independent_variant_facts(tc: hegel::TestCase) {
    let facts = tc.draw(hegel::generators::default::<Vec<()>>());
    let work = variant_projections(facts.len());
    assert_eq!(work.comparison_states, 0);
    assert_eq!(work.comparison_edges, 0);
    assert_eq!(work.guard_segments, 2 * facts.len());
    let levels = match facts.len().checked_ilog2() {
        Some(levels) => levels as usize,
        None => 0,
    };
    assert!(
        work.guard_projection_fragments <= facts.len() * (2 * levels + 4),
        "{work:?}"
    );
}

#[test]
fn growing_mixed_guard_prefixes_reuse_common_fragments() {
    let observations = [8, 16, 32].map(|size| {
        with_graph(|mut graph| {
            let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
            let mut guards = shapelint_driver::sequence::Sequence::EMPTY;
            for index in 0..size {
                let unrelated = graph.intern_expr(ExprNode::Argument(size + index)).unwrap();
                let common = graph
                    .intern_condition(ConditionNode::Compare(Order::LessEqual, zero, unrelated))
                    .unwrap();
                guards = graph.condition_sequences.push(guards, common).unwrap();
                let value = graph.intern_expr(ExprNode::Argument(index)).unwrap();
                let variant = graph
                    .intern_condition(ConditionNode::Variant(value, 0))
                    .unwrap();
                guards = graph.condition_sequences.push(guards, variant).unwrap();
                let proof = graph.prove(variant, &guards).unwrap();
                let shapelint_driver::contracts::graph::evidence::Proof::Proven(evidence) = proof
                else {
                    panic!("own variant guard proves the condition: {proof:?}");
                };
                let evidence = graph.evidence_sequence(evidence).unwrap();
                assert_eq!(
                    graph
                        .condition_sequences
                        .iter(evidence)
                        .copied()
                        .collect::<Vec<_>>(),
                    [variant]
                );
            }
            assert_eq!(graph.proof_work.guard_segments, 4 * size);
            assert_eq!(graph.proof_work.comparison_states, 0);
            assert_eq!(graph.proof_work.comparison_edges, 0);
            eprintln!("mixed growing guard prefix {size}: {:?}", graph.proof_work);
            graph.proof_work
        })
    });
    assert!(
        observations[2].guard_projection_fragments
            <= 3 * observations[1].guard_projection_fragments,
        "{observations:?}"
    );
}

#[test]
fn successive_cycle_merges_revisit_the_same_upstream_components() {
    let observations = [8, 16, 32].map(|merges| {
        let definitions: Vec<_> = (0..=2 * merges)
            .map(|index| DefId::local(DefIndex::from_usize(index)))
            .collect();
        let mut recursion = Recursion::try_from(
            definitions
                .windows(2)
                .map(|pair| (pair[0], pair[1]))
                .collect::<Vec<_>>(),
        )
        .unwrap();
        let tail = definitions[2 * merges];
        for index in (merges..2 * merges).rev() {
            let revision = recursion.revision(definitions[0]);
            assert_eq!(
                recursion.edge(tail, definitions[index]).unwrap(),
                Some((tail, definitions[index]))
            );
            assert_ne!(recursion.revision(definitions[0]), revision);
        }
        assert_eq!(recursion.components().count(), merges + 1);
        eprintln!("cycle merges {merges}: {:?}", recursion.work);
        recursion.work.invalidated_components
    });
    assert_eq!(observations, [108, 408, 1584]);
}
