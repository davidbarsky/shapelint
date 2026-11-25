#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_middle;

use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::{DefId, DefIndex};
use shapelint_driver::calls::{Dispatch, Instance, Type};
use shapelint_driver::contracts::graph::{ExprNode, NodeId, with_graph};
use shapelint_driver::contracts::{Arithmetic, Interval, Join};
use shapelint_driver::sequence::Sequence;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Step {
    Input(u16),
    Function(u16),
    Closure(u16),
    Unknown,
    Arithmetic,
    Typed,
    Shared,
}

#[hegel::test(print_blob = true)]
fn shared_collector_summaries_match_flat_sets(tc: hegel::TestCase) {
    let steps = tc.draw(hegel::generators::default::<Vec<Step>>());
    with_graph(|mut graph| {
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let mut root = zero;
        let mut inputs = Some(FxHashSet::default());
        let mut functions = FxHashSet::default();
        for step in steps {
            let node = match step {
                Step::Input(index) => {
                    if let Some(inputs) = &mut inputs {
                        inputs.insert(usize::from(index));
                    }
                    let input = graph
                        .intern_expr(ExprNode::Argument(usize::from(index)))
                        .unwrap();
                    ExprNode::Aggregate(
                        graph.expression_sequences.from_iter([root, input]).unwrap(),
                    )
                }
                Step::Function(index) => {
                    let def = DefId::local(DefIndex::from_usize(usize::from(index)));
                    functions.insert(def);
                    let function = {
                        let instance = graph
                            .values
                            .intern_instance(&Instance {
                                def,
                                args: Vec::new(),
                                dispatch: Dispatch::Item,
                            })
                            .unwrap();
                        graph.intern_expr(ExprNode::Function(instance))
                    }
                    .unwrap();
                    ExprNode::Aggregate(
                        graph
                            .expression_sequences
                            .from_iter([root, function])
                            .unwrap(),
                    )
                }
                Step::Closure(index) => {
                    let def = DefId::local(DefIndex::from_usize(usize::from(index)));
                    functions.insert(def);
                    ExprNode::Closure(
                        def,
                        graph.expression_sequences.from_iter([root, root]).unwrap(),
                    )
                }
                Step::Unknown => {
                    inputs = None;
                    let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
                    ExprNode::Aggregate(
                        graph
                            .expression_sequences
                            .from_iter([root, unknown])
                            .unwrap(),
                    )
                }
                Step::Arithmetic => {
                    functions.clear();
                    ExprNode::Arithmetic(Arithmetic::Add(rustc_middle::ty::UintTy::U32), root, zero)
                }
                Step::Typed => {
                    ExprNode::Typed(graph.values.intern_type(&Type::Parameter(0)).unwrap(), root)
                }
                Step::Shared => {
                    ExprNode::Aggregate(graph.expression_sequences.from_iter([root, root]).unwrap())
                }
            };
            root = graph.intern_expr(node).unwrap();
            assert_eq!(
                graph.inputs(NodeId::Expr(root)).unwrap(),
                inputs,
                "{step:?}"
            );
            let mut actual = FxHashSet::default();
            graph.functions(root, &mut actual).unwrap();
            assert_eq!(actual, functions, "{step:?}");
            graph.functions(root, &mut actual).unwrap();
            assert_eq!(actual, functions, "repeated {step:?}");
            assert_eq!(
                graph.inputs(NodeId::Expr(root)).unwrap(),
                inputs,
                "repeated {step:?}"
            );
        }
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Shape {
    Aggregate,
    Typed,
    Variant,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Joins {
    left: u128,
    right: u128,
    shapes: Vec<Shape>,
}

#[hegel::test(print_blob = true)]
fn repeated_joins_keep_order_and_join_mode(tc: hegel::TestCase) {
    let Joins {
        left,
        right,
        shapes,
    } = tc.draw(hegel::generators::default::<Joins>());
    with_graph(|mut graph| {
        let (hull, widened, reversed) = match left == right {
            true => (
                ExprNode::Number(left),
                ExprNode::Number(left),
                ExprNode::Number(left),
            ),
            false => (
                ExprNode::Range(Interval {
                    lower: left.min(right),
                    upper: left.max(right),
                }),
                ExprNode::Range(Interval {
                    lower: match right < left {
                        true => 0,
                        false => left,
                    },
                    upper: match right > left {
                        true => u128::MAX,
                        false => left,
                    },
                }),
                ExprNode::Range(Interval {
                    lower: match left < right {
                        true => 0,
                        false => right,
                    },
                    upper: match left > right {
                        true => u128::MAX,
                        false => right,
                    },
                }),
            ),
        };
        let mut hull = graph.intern_expr(hull).unwrap();
        let mut widened = graph.intern_expr(widened).unwrap();
        let mut reversed = graph.intern_expr(reversed).unwrap();
        let mut left = graph.intern_expr(ExprNode::Number(left)).unwrap();
        let mut right = graph.intern_expr(ExprNode::Number(right)).unwrap();
        let entries = shapes.into_iter().chain(std::iter::once(Shape::Aggregate));
        for shape in entries {
            let def = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
            for value in [
                &mut left,
                &mut right,
                &mut hull,
                &mut widened,
                &mut reversed,
            ] {
                let node = match shape {
                    Shape::Aggregate => ExprNode::Aggregate(
                        graph
                            .expression_sequences
                            .from_iter([*value, *value])
                            .unwrap(),
                    ),
                    Shape::Typed => ExprNode::Typed(
                        graph.values.intern_type(&Type::Parameter(0)).unwrap(),
                        *value,
                    ),
                    Shape::Variant => ExprNode::Variant(
                        def,
                        0,
                        graph.expression_sequences.from_iter([*value]).unwrap(),
                    ),
                };
                *value = graph.intern_expr(node).unwrap();
            }
            assert_eq!(graph.join(left, right, Join::Hull).unwrap(), hull);
            assert_eq!(graph.join(left, right, Join::Widen).unwrap(), widened);
            assert_eq!(graph.join(right, left, Join::Widen).unwrap(), reversed);
            assert_eq!(graph.join(left, right, Join::Hull).unwrap(), hull);
        }
    });
}

#[test]
fn every_prefix_reuses_field_and_collector_summaries() {
    with_graph(|mut graph| {
        let def = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        let argument = graph.intern_expr(ExprNode::Argument(17)).unwrap();
        let function = {
            let instance = graph
                .values
                .intern_instance(&Instance {
                    def,
                    args: Vec::new(),
                    dispatch: Dispatch::Item,
                })
                .unwrap();
            graph.intern_expr(ExprNode::Function(instance))
        }
        .unwrap();
        let mut root = {
            let fields = graph
                .expression_sequences
                .from_iter([argument, function])
                .unwrap();
            graph.intern_expr(ExprNode::Aggregate(fields))
        }
        .unwrap();
        for _ in 0..100_000 {
            root = {
                let ty = graph.values.intern_type(&Type::Parameter(0)).unwrap();
                graph.intern_expr(ExprNode::Typed(ty, root))
            }
            .unwrap();
            assert_eq!(graph.field(root, 0).unwrap(), argument);
            assert_eq!(graph.field(root, 1).unwrap(), function);
            assert_eq!(
                graph.inputs(NodeId::Expr(root)).unwrap(),
                Some([17].into_iter().collect())
            );
            let mut functions = FxHashSet::default();
            graph.functions(root, &mut functions).unwrap();
            assert_eq!(functions, [def].into_iter().collect());
        }
    });
}

#[test]
fn capture_free_parameter_prefixes_reuse_completed_results() {
    with_graph(|mut graph| {
        let def = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        let mut root = {
            let instance = graph
                .values
                .intern_instance(&Instance {
                    def,
                    args: Vec::new(),
                    dispatch: Dispatch::Item,
                })
                .unwrap();
            graph.intern_expr(ExprNode::Function(instance))
        }
        .unwrap();
        let binding = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let mut values = Sequence::default();
        for _ in 0..100_000 {
            root = {
                let fields = graph.expression_sequences.from_iter([root, root]).unwrap();
                graph.intern_expr(ExprNode::Aggregate(fields))
            }
            .unwrap();
            assert_eq!(graph.parameter(root, binding, &mut values).unwrap(), root);
        }
        assert_eq!(graph.expression_sequences.len(values), 0);
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
struct InputSets {
    left: Vec<u16>,
    right: Vec<u16>,
}

#[hegel::test(print_blob = true)]
fn overlapping_input_sets_share_union_without_losing_members(tc: hegel::TestCase) {
    let InputSets { left, right } = tc.draw(hegel::generators::default::<InputSets>());
    with_graph(|mut graph| {
        let expected: FxHashSet<_> = left
            .iter()
            .chain(&right)
            .map(|index| usize::from(*index))
            .collect();
        let left: Vec<_> = left
            .into_iter()
            .map(|index| {
                graph
                    .intern_expr(ExprNode::Argument(usize::from(index)))
                    .unwrap()
            })
            .collect();
        let right: Vec<_> = right
            .into_iter()
            .map(|index| {
                graph
                    .intern_expr(ExprNode::Argument(usize::from(index)))
                    .unwrap()
            })
            .collect();
        let left = {
            let fields = graph.expression_sequences.from_iter(left).unwrap();
            graph.intern_expr(ExprNode::Aggregate(fields))
        }
        .unwrap();
        let right = {
            let fields = graph.expression_sequences.from_iter(right).unwrap();
            graph.intern_expr(ExprNode::Aggregate(fields))
        }
        .unwrap();
        let root = {
            let fields = graph.expression_sequences.from_iter([left, right]).unwrap();
            graph.intern_expr(ExprNode::Aggregate(fields))
        }
        .unwrap();
        let reversed = {
            let fields = graph.expression_sequences.from_iter([right, left]).unwrap();
            graph.intern_expr(ExprNode::Aggregate(fields))
        }
        .unwrap();
        assert_eq!(
            graph.inputs(NodeId::Expr(root)).unwrap(),
            Some(expected.clone())
        );
        assert_eq!(
            graph.inputs(NodeId::Expr(reversed)).unwrap(),
            Some(expected)
        );
    });
}

#[test]
fn invalidation_cache_includes_the_affected_nodes() {
    use shapelint_driver::contracts::operations::GraphInvalidation;
    with_graph(|mut graph| {
        let target = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let replacement = graph.intern_expr(ExprNode::Number(7)).unwrap();
        let root = graph.intern_expr(ExprNode::Length(target)).unwrap();
        let change = GraphInvalidation::Replace {
            target,
            value: replacement,
        };
        let empty = graph.intern_affected([]).unwrap();
        assert_eq!(graph.invalidate_expr(root, change, empty).unwrap(), root);
        let root_only = graph.intern_affected([NodeId::Expr(root)]).unwrap();
        assert_eq!(
            graph.invalidate_expr(root, change, root_only).unwrap(),
            root
        );
        let both = graph
            .intern_affected([NodeId::Expr(root), NodeId::Expr(target)])
            .unwrap();
        let expected = graph.intern_expr(ExprNode::Length(replacement)).unwrap();
        assert_eq!(graph.invalidate_expr(root, change, both).unwrap(), expected);
    });
}
