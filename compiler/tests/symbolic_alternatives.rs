#![feature(rustc_private)]

extern crate rustc_data_structures;

use rustc_data_structures::fx::FxHashMap;

use shapelint_driver::contracts::graph::{ExprNode, with_graph};
use shapelint_driver::contracts::{Expr, Invocation, Return, Summary};
use shapelint_driver::sequence::Sequence;

#[derive(Debug, hegel::DefaultGenerator)]
struct Groups {
    groups: Vec<Vec<u8>>,
}

#[derive(Default)]
struct Model {
    interned: FxHashMap<Vec<u128>, Vec<u128>>,
}

impl Model {
    fn intern(&mut self, values: impl IntoIterator<Item = u128>) -> Vec<u128> {
        let mut ordered = Vec::new();
        for value in values {
            match ordered.iter().find(|candidate| **candidate == value) {
                Some(_) => {}
                None => ordered.push(value),
            }
        }
        let mut key = ordered.clone();
        key.sort_unstable();
        self.interned.entry(key).or_insert(ordered).clone()
    }
}

#[hegel::test(print_blob = true)]
fn nested_groups_match_flat_first_interned_set_semantics(tc: hegel::TestCase) {
    let Groups { groups } = tc.draw(hegel::generators::default::<Groups>());
    with_graph(|mut graph| {
        let mut model = Model::default();
        let mut expected = model.intern([]);
        let mut root = graph.alternatives([]).unwrap();
        for group in groups {
            let members: Vec<_> = group
                .iter()
                .map(|value| {
                    graph
                        .intern_expr(ExprNode::Number(u128::from(*value)))
                        .unwrap()
                })
                .collect();
            let nested = graph.alternatives(members.iter().copied()).unwrap();
            let nested_expected = model.intern(group.into_iter().map(u128::from));
            let reverse = graph.alternatives(members.iter().rev().copied()).unwrap();
            assert_eq!(nested, reverse);
            root = graph.alternatives([root, nested, root]).unwrap();
            expected = model.intern(
                expected
                    .iter()
                    .chain(&nested_expected)
                    .chain(&expected)
                    .copied(),
            );
            let actual = graph.raise_expr(root);
            let actual: Vec<_> = match &actual {
                Expr::Number(value) => vec![*value],
                Expr::Alternatives(values) => values
                    .iter()
                    .map(|value| match value {
                        Expr::Number(value) => *value,
                        value => panic!("expected numeric member, got {value:?}"),
                    })
                    .collect(),
                value => panic!("expected alternatives, got {value:?}"),
            };
            assert_eq!(actual, expected);
        }
    });
}

#[test]
fn internal_sequence_fragments_do_not_choose_a_later_subsets_order() {
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let second = graph.intern_expr(ExprNode::Number(2)).unwrap();
        let third = graph.intern_expr(ExprNode::Number(3)).unwrap();
        let whole = graph.alternatives([first, second, third]).unwrap();
        let subset = graph.alternatives([second, first]).unwrap();
        assert_eq!(
            graph.raise_expr(subset),
            Expr::Alternatives(vec![Expr::Number(2), Expr::Number(1)])
        );
        assert_eq!(
            graph.raise_expr(whole),
            Expr::Alternatives(vec![Expr::Number(1), Expr::Number(2), Expr::Number(3)])
        );
        assert_eq!(graph.alternatives([first, second]).unwrap(), subset);
    });
}

#[hegel::test(print_blob = true)]
fn substituting_choice_members_preserves_order_while_collapsing_duplicates(tc: hegel::TestCase) {
    let values = tc.draw(hegel::generators::default::<Vec<u8>>());
    let mut model = Model::default();
    let expected = model.intern(values.iter().copied().map(u128::from));
    with_graph(|mut graph| {
        let members: Vec<_> = (0..values.len())
            .map(|index| graph.intern_expr(ExprNode::Argument(index)).unwrap())
            .collect();
        let root = graph.alternatives(members).unwrap();
        let arguments: Vec<_> = values
            .into_iter()
            .map(|value| {
                graph
                    .intern_expr(ExprNode::Number(u128::from(value)))
                    .unwrap()
            })
            .collect();
        let arguments = graph.expression_sequences.from_iter(arguments).unwrap();
        let invocation = Invocation::LOCAL;
        let actual = graph
            .substitute_expr(root, &arguments, &invocation)
            .unwrap();
        let expected = match expected.as_slice() {
            [value] => Expr::Number(*value),
            values => Expr::Alternatives(values.iter().copied().map(Expr::Number).collect()),
        };
        assert_eq!(graph.raise_expr(actual), expected);
        assert_eq!(
            graph
                .substitute_expr(root, &arguments, &invocation)
                .unwrap(),
            actual
        );
    });
}

#[test]
fn projected_growing_choice_prefixes_store_shared_structural_nodes() {
    with_graph(|mut graph| {
        let count = 4096usize;
        let mut root = graph.alternatives([]).unwrap();
        let mut projected = root;
        for index in 0..count {
            let value = graph.intern_expr(ExprNode::Number(index as u128)).unwrap();
            let fields = graph.expression_sequences.from_iter([value]).unwrap();
            let aggregate = graph.intern_expr(ExprNode::Aggregate(fields)).unwrap();
            root = graph.alternatives([root, aggregate]).unwrap();
            projected = graph.field(root, 0).unwrap();
            assert_eq!(graph.field(root, 0).unwrap(), projected);
        }
        let ExprNode::Alternatives(Some(projected)) = graph[projected] else {
            panic!("multiple projected values remain alternatives");
        };
        assert_eq!(
            graph.expression_sequences.len(graph[projected].values),
            count
        );
        let actual: Vec<_> = graph
            .expression_sequences
            .iter(graph[projected].values)
            .map(|value| match graph[*value] {
                ExprNode::Number(value) => value,
                ref value => panic!("expected projected number, got {value:?}"),
            })
            .collect();
        assert_eq!(actual, (0..count as u128).collect::<Vec<_>>());
        // Both input and projected ropes add at most three nodes per AVL level;
        // AVL height is bounded by twice the binary logarithm of the leaf count.
        let bound = 2 * count * (6 * (count.ilog2() as usize + 1) + 1);
        assert!(graph.choices().count() <= bound);
        assert!(bound < count * (count + 1) / 2);
    });
}

#[test]
fn summary_keeps_all_growing_roots_on_one_shared_choice_graph() {
    with_graph(|mut graph| {
        let count = 2048usize;
        let mut root = graph.alternatives([]).unwrap();
        let mut summary = Summary::default();
        for index in 0..count {
            let value = graph.intern_expr(ExprNode::Number(index as u128)).unwrap();
            root = graph.alternatives([root, value]).unwrap();
            summary.returns.push(Return {
                value: root,
                guards: Sequence::default(),
            });
        }
        let stored = graph.choices().count();
        {
            let summary = graph.freeze(summary).unwrap();
            let summary = graph.summaries[summary];
            assert_eq!(graph.summaries.returns.len(summary.returns), count);
            assert!(graph.choices().count() <= stored);
            let entries = graph.summaries.returns.iter(summary.returns).enumerate();
            for (index, returned) in entries {
                match graph[returned.value] {
                    ExprNode::Number(value) => assert_eq!((index, value), (0, 0)),
                    ExprNode::Alternatives(Some(root)) => {
                        assert_eq!(
                            graph.expression_sequences.len(graph[root].values),
                            index + 1
                        );
                        let Some(last) = graph
                            .expression_sequences
                            .iter(graph[root].values)
                            .next_back()
                        else {
                            panic!("an alternative root is nonempty");
                        };
                        match graph[*last] {
                            ExprNode::Number(value) => assert_eq!(value, index as u128),
                            ref node => panic!("expected final prefix member, got {node:?}"),
                        }
                    }
                    ref node => panic!("expected numeric prefix, got {node:?}"),
                }
            }
        }
    });
}

#[test]
fn projection_visits_left_members_before_interning_a_shared_result_set() {
    use shapelint_driver::calls::Type;

    with_graph(|mut graph| {
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let two = graph.intern_expr(ExprNode::Number(2)).unwrap();
        let three = graph.intern_expr(ExprNode::Number(3)).unwrap();
        let fields = graph.expression_sequences.from_iter([one, zero]).unwrap();
        let a = graph.intern_expr(ExprNode::Aggregate(fields)).unwrap();
        let fields = graph.expression_sequences.from_iter([two, one]).unwrap();
        let b = graph.intern_expr(ExprNode::Aggregate(fields)).unwrap();
        let fields = graph.expression_sequences.from_iter([two, two]).unwrap();
        let c = graph.intern_expr(ExprNode::Aggregate(fields)).unwrap();
        let fields = graph.expression_sequences.from_iter([one, three]).unwrap();
        let d = graph.intern_expr(ExprNode::Aggregate(fields)).unwrap();
        let left = graph.alternatives([a, b]).unwrap();
        let right = graph.alternatives([c, d]).unwrap();
        let boolean = graph.values.intern_type(&Type::Bool).unwrap();
        let character = graph.values.intern_type(&Type::Char).unwrap();
        let left = graph.typed(boolean, left).unwrap();
        let right = graph.typed(character, right).unwrap();
        let root = graph.alternatives([left, right]).unwrap();
        let projected = graph.field(root, 0).unwrap();
        assert_eq!(
            graph.raise_expr(projected),
            Expr::Alternatives(vec![Expr::Number(1), Expr::Number(2)])
        );
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Replacement {
    members: Vec<u8>,
    target: u8,
}

#[hegel::test(print_blob = true)]
fn sparse_invalidation_updates_only_members_reaching_the_replaced_input(tc: hegel::TestCase) {
    use shapelint_driver::contracts::graph::NodeId;
    use shapelint_driver::contracts::operations::GraphInvalidation;
    use shapelint_driver::states::facts::{Dependencies, with_dependencies};

    let Replacement { members, target } = tc.draw(hegel::generators::default::<Replacement>());
    let mut model = Model::default();
    let ordered = model.intern(members.iter().copied().map(u128::from));
    with_graph(|mut graph| {
        let values: Vec<_> = members
            .into_iter()
            .map(|value| {
                graph
                    .intern_expr(ExprNode::Argument(usize::from(value)))
                    .unwrap()
            })
            .collect();
        let root = graph.alternatives(values).unwrap();
        let target_id = graph
            .intern_expr(ExprNode::Argument(usize::from(target)))
            .unwrap();
        let replacement = graph.intern_expr(ExprNode::Number(19)).unwrap();
        let change = GraphInvalidation::Replace {
            target: target_id,
            value: replacement,
        };
        with_dependencies(|stores| {
            let mut dependencies = Dependencies::default();
            dependencies
                .insert(stores, (), NodeId::Expr(root), &graph)
                .unwrap();
            let affected = dependencies.affected(stores, change, &mut graph).unwrap();
            let actual = graph.invalidate_expr(root, change, affected).unwrap();
            let expected: Vec<_> = ordered
                .into_iter()
                .map(|value| match value == u128::from(target) {
                    true => Expr::Number(19),
                    false => Expr::Argument(value as usize),
                })
                .collect();
            let expected = match expected.as_slice() {
                [value] => value.clone(),
                _ => Expr::Alternatives(expected),
            };
            assert_eq!(graph.raise_expr(actual), expected);
        });
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
enum SetRelation {
    Disjoint {
        left: Vec<u8>,
        right: Vec<u8>,
    },
    Equal {
        values: Vec<u8>,
    },
    Nested {
        shared: Vec<u8>,
        extra: Vec<u8>,
    },
    Overlapping {
        shared: Vec<u8>,
        left: Vec<u8>,
        right: Vec<u8>,
    },
}

#[derive(Debug, hegel::DefaultGenerator)]
struct SetInputs {
    relation: SetRelation,
    noise: Vec<u8>,
}

#[hegel::test(print_blob = true)]
fn choice_joins_match_ordered_sets_across_identity_histories(tc: hegel::TestCase) {
    let SetInputs { relation, noise } = tc.draw(hegel::generators::default::<SetInputs>());
    let (left, right): (Vec<u128>, Vec<u128>) = match relation {
        SetRelation::Disjoint { left, right } => (
            left.into_iter()
                .map(|value| u128::from(value) * 3)
                .collect(),
            right
                .into_iter()
                .map(|value| u128::from(value) * 3 + 1)
                .collect(),
        ),
        SetRelation::Equal { values } => {
            let values: Vec<_> = values.into_iter().map(u128::from).collect();
            (values.clone(), values)
        }
        SetRelation::Nested { shared, extra } => {
            let shared: Vec<_> = shared
                .into_iter()
                .map(|value| u128::from(value) * 2)
                .collect();
            let mut whole = shared.clone();
            whole.extend(extra.into_iter().map(|value| u128::from(value) * 2 + 1));
            (whole, shared)
        }
        SetRelation::Overlapping {
            shared,
            left,
            right,
        } => {
            let shared: Vec<_> = shared
                .into_iter()
                .map(|value| u128::from(value) * 3)
                .collect();
            let mut first = shared.clone();
            first.extend(left.into_iter().map(|value| u128::from(value) * 3 + 1));
            let mut second = shared;
            second.extend(right.into_iter().map(|value| u128::from(value) * 3 + 2));
            (first, second)
        }
    };
    with_graph(|mut graph| {
        let mut model = Model::default();
        let left_values: Vec<_> = left
            .iter()
            .map(|value| graph.intern_expr(ExprNode::Number(*value)).unwrap())
            .collect();
        let left_root = graph.alternatives(left_values).unwrap();
        for value in noise {
            let value = graph
                .intern_expr(ExprNode::Number(1024 + u128::from(value)))
                .unwrap();
            graph.alternatives([value]).unwrap();
        }
        let right_values: Vec<_> = right
            .iter()
            .map(|value| graph.intern_expr(ExprNode::Number(*value)).unwrap())
            .collect();
        let right_root = graph.alternatives(right_values).unwrap();
        let left_expected = model.intern(left);
        let right_expected = model.intern(right);
        let expected = model.intern(left_expected.into_iter().chain(right_expected));
        let root = graph.alternatives([left_root, right_root]).unwrap();
        let reversed = graph.alternatives([right_root, left_root]).unwrap();
        assert_eq!(root, reversed);
        let actual = graph.raise_expr(root);
        let actual: Vec<_> = match &actual {
            Expr::Number(value) => vec![*value],
            Expr::Alternatives(values) => values
                .iter()
                .map(|value| match value {
                    Expr::Number(value) => *value,
                    value => panic!("expected numeric member, got {value:?}"),
                })
                .collect(),
            value => panic!("expected alternatives, got {value:?}"),
        };
        assert_eq!(actual, expected);
    });
}
