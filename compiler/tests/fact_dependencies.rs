#![feature(rustc_private)]

extern crate rustc_data_structures;

extern crate rustc_hir;
extern crate rustc_middle;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};

use rustc_hir::def_id::CRATE_DEF_ID;
use rustc_middle::mir::Local;
use shapelint_driver::contracts::graph::{ExprNode, NodeId, with_graph};
use shapelint_driver::contracts::operations::GraphInvalidation;
use shapelint_driver::contracts::{Identity, Origin};
use shapelint_driver::states::facts::{Dependencies, with_dependencies};

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum Action {
    Put { root: u8, locals: Vec<u8> },
    Remove(u8),
    Save,
    Restore,
    Query(u8),
}

#[hegel::test(print_blob = true)]
fn active_fact_dependencies_follow_replacement_removal_and_snapshots(tc: hegel::TestCase) {
    let actions = tc.draw(hegel::generators::default::<Vec<Action>>());
    with_graph(|mut graph| {
        with_dependencies(|stores| {
            let mut actual = Dependencies::default();
            let mut expected = FxHashMap::<u8, Vec<u8>>::default();
            let mut saved = (actual.clone(), expected.clone());
            for action in actions {
                match action {
                    Action::Put { root, locals } => {
                        let mut value = graph
                            .intern_expr(ExprNode::Number(0))
                            .expect("number fits graph");
                        for local in &locals {
                            let local = graph
                                .intern_expr(ExprNode::Cursor {
                                    def: CRATE_DEF_ID.to_def_id(),
                                    local: Local::from_usize(usize::from(*local)),
                                })
                                .expect("cursor fits graph");
                            let fields = graph
                                .expression_sequences
                                .from_iter([value, local, local])
                                .unwrap();
                            value = graph
                                .intern_expr(ExprNode::Aggregate(fields))
                                .expect("aggregate fits graph");
                        }
                        actual
                            .insert(stores, root, NodeId::Expr(value), &graph)
                            .unwrap();
                        expected.insert(root, locals);
                    }
                    Action::Remove(root) => {
                        actual.remove(stores, &root, &graph).unwrap();
                        expected.remove(&root);
                    }
                    Action::Save => saved = (actual.clone(), expected.clone()),
                    Action::Restore => {
                        actual = saved.0.clone();
                        expected = saved.1.clone();
                    }
                    Action::Query(local) => {
                        let affected = actual
                            .affected(
                                stores,
                                GraphInvalidation::Local(Local::from_usize(usize::from(local))),
                                &mut graph,
                            )
                            .unwrap();
                        let observed: FxHashSet<_> =
                            actual.roots(stores, &graph, affected).into_keys().collect();
                        let expected: FxHashSet<_> = expected
                            .iter()
                            .filter_map(|(root, locals)| {
                                locals.iter().find(|value| **value == local).map(|_| *root)
                            })
                            .collect();
                        assert_eq!(observed, expected);
                    }
                }
            }
        });
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Memory {
    places: Vec<Vec<u8>>,
    written: Vec<u8>,
}

#[hegel::test(print_blob = true)]
fn memory_overlap_matches_the_independent_prefix_model(tc: hegel::TestCase) {
    let Memory { places, written } = tc.draw(hegel::generators::default::<Memory>());
    with_graph(|mut graph| {
        with_dependencies(|stores| {
            let base = graph
                .intern_expr(ExprNode::Argument(0))
                .expect("base fits graph");
            let unrelated = graph
                .intern_expr(ExprNode::Argument(1))
                .expect("other base fits graph");
            let mut dependencies = Dependencies::default();
            let entries = places.iter().enumerate();
            for (index, path) in entries {
                let mut location = base;
                for field in path {
                    location = graph
                        .intern_expr(ExprNode::Field(location, usize::from(*field)))
                        .expect("field fits graph");
                }
                let fields = graph
                    .expression_sequences
                    .from_iter([location, unrelated])
                    .unwrap();
                let value = graph
                    .intern_expr(ExprNode::Aggregate(fields))
                    .expect("root fits graph");
                dependencies
                    .insert(stores, index, NodeId::Expr(value), &graph)
                    .unwrap();
            }
            let mut target = base;
            for field in &written {
                target = graph
                    .intern_expr(ExprNode::Field(target, usize::from(*field)))
                    .expect("target fits graph");
            }
            let affected = dependencies
                .affected(stores, GraphInvalidation::Memory(target), &mut graph)
                .unwrap();
            let observed: FxHashSet<_> = dependencies
                .roots(stores, &graph, affected)
                .into_keys()
                .collect();
            let expected: FxHashSet<_> = places
                .iter()
                .enumerate()
                .filter_map(|(index, path)| {
                    match path.starts_with(&written) || written.starts_with(path) {
                        true => Some(index),
                        false => None,
                    }
                })
                .collect();
            assert_eq!(observed, expected);
        });
    });
}

#[test]
fn unrelated_assignments_have_no_affected_graph_nodes() {
    with_graph(|mut graph| {
        with_dependencies(|stores| {
            let mut dependencies = Dependencies::default();
            let count = 10_000;
            for index in 0..count {
                let value = graph
                    .intern_expr(ExprNode::Cursor {
                        def: CRATE_DEF_ID.to_def_id(),
                        local: Local::from_usize(index),
                    })
                    .expect("cursor fits graph");
                dependencies
                    .insert(stores, index, NodeId::Expr(value), &graph)
                    .unwrap();
                let affected = dependencies
                    .affected(
                        stores,
                        GraphInvalidation::Local(Local::from_usize(count + index)),
                        &mut graph,
                    )
                    .unwrap();
                assert_eq!(graph.reference_sets[affected].len, 0);
            }
            let affected = dependencies
                .affected(
                    stores,
                    GraphInvalidation::Local(Local::from_usize(count / 2)),
                    &mut graph,
                )
                .unwrap();
            assert_eq!(graph.reference_sets[affected].len, 1);
            assert_eq!(
                dependencies
                    .roots(stores, &graph, affected)
                    .into_keys()
                    .collect::<Vec<_>>(),
                vec![count / 2]
            );
        });
    });
}

#[test]
fn sibling_mutations_retire_only_their_own_dependency_paths() {
    with_graph(|mut graph| {
        with_dependencies(|stores| {
            let base = graph
                .intern_expr(ExprNode::Argument(0))
                .expect("base fits graph");
            let mut dependencies = Dependencies::default();
            let count = 10_000;
            let fields: Vec<_> = (0..count)
                .map(|index| {
                    let field = graph
                        .intern_expr(ExprNode::Field(base, index))
                        .expect("field fits graph");
                    let fields = graph
                        .expression_sequences
                        .from_iter([field, field])
                        .unwrap();
                    let consumer = graph
                        .intern_expr(ExprNode::Aggregate(fields))
                        .expect("consumer fits graph");
                    dependencies
                        .insert(stores, index, NodeId::Expr(consumer), &graph)
                        .unwrap();
                    field
                })
                .collect();
            let saved = dependencies.clone();
            let entries = fields.into_iter().enumerate();
            for (index, field) in entries {
                let affected = dependencies
                    .affected(stores, GraphInvalidation::Memory(field), &mut graph)
                    .unwrap();
                assert_eq!(graph.reference_sets[affected].len, 3);
                assert_eq!(
                    dependencies
                        .roots(stores, &graph, affected)
                        .into_keys()
                        .collect::<Vec<_>>(),
                    vec![index]
                );
                dependencies.remove(stores, &index, &graph).unwrap();
            }
            let affected = dependencies
                .affected(stores, GraphInvalidation::Memory(base), &mut graph)
                .unwrap();
            assert_eq!(graph.reference_sets[affected].len, 0);
            let affected = saved
                .affected(stores, GraphInvalidation::Memory(base), &mut graph)
                .unwrap();
            assert_eq!(saved.roots(stores, &graph, affected).len(), count);
        });
    });
}

#[hegel::test(print_blob = true)]
fn local_and_memory_changes_follow_their_respective_edge_classes(tc: hegel::TestCase) {
    let path = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_graph(|mut graph| {
        with_dependencies(|stores| {
            let local = Local::from_usize(1);
            let def = CRATE_DEF_ID.to_def_id();
            let origin = Origin {
                def,
                name: None,
                adt: None,
                identity: Some(Identity {
                    origin: (def, local),
                    fields: Vec::new(),
                    calls: Vec::new(),
                }),
            };
            let origin = graph.values.intern_origin(&origin).unwrap();
            let base = graph
                .intern_expr(ExprNode::Opaque(origin))
                .expect("base fits graph");
            let mut field = base;
            for index in path {
                field = graph
                    .intern_expr(ExprNode::Field(field, usize::from(index)))
                    .expect("field fits graph");
            }
            let fields = graph
                .expression_sequences
                .from_iter([field, field])
                .unwrap();
            let aggregate = graph
                .intern_expr(ExprNode::Aggregate(fields))
                .expect("aggregate fits graph");
            let projection = graph
                .intern_expr(ExprNode::Field(aggregate, 0))
                .expect("projection fits graph");
            let mut dependencies = Dependencies::default();
            dependencies
                .insert(stores, 0, NodeId::Expr(projection), &graph)
                .unwrap();
            let affected = dependencies
                .affected(stores, GraphInvalidation::Local(local), &mut graph)
                .unwrap();
            assert_eq!(
                dependencies
                    .roots(stores, &graph, affected)
                    .into_keys()
                    .collect::<Vec<_>>(),
                vec![0]
            );
            let affected = dependencies
                .affected(stores, GraphInvalidation::Memory(field), &mut graph)
                .unwrap();
            assert_eq!(
                dependencies
                    .roots(stores, &graph, affected)
                    .into_keys()
                    .collect::<Vec<_>>(),
                vec![0]
            );
            dependencies.remove(stores, &0, &graph).unwrap();
            let affected = dependencies
                .affected(stores, GraphInvalidation::Local(local), &mut graph)
                .unwrap();
            assert_eq!(graph.reference_sets[affected].len, 0);
            let affected = dependencies
                .affected(stores, GraphInvalidation::Memory(field), &mut graph)
                .unwrap();
            assert_eq!(graph.reference_sets[affected].len, 0);
        });
    });
}
