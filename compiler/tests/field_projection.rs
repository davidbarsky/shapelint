#![feature(rustc_private)]

extern crate rustc_hir;

use shapelint_driver::calls::Type;
use shapelint_driver::contracts::graph::{ExprNode, with_graph};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum AggregateShape {
    Aggregate,
    Variant,
    Closure,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Projection {
    shape: AggregateShape,
    fields: Vec<u128>,
}

#[hegel::test(print_blob = true)]
fn aggregate_fields_preserve_identity_without_creating_nodes(tc: hegel::TestCase) {
    let Projection { shape, fields } = tc.draw(hegel::generators::default::<Projection>());
    with_graph(|mut graph| {
        let fields: Vec<_> = fields
            .into_iter()
            .map(|value| graph.intern_expr(ExprNode::Number(value)).unwrap())
            .collect();
        let def = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        let field_ids = graph
            .expression_sequences
            .from_iter(fields.iter().copied())
            .unwrap();
        let node = match shape {
            AggregateShape::Aggregate => ExprNode::Aggregate(field_ids),
            AggregateShape::Variant => ExprNode::Variant(def, 0, field_ids),
            AggregateShape::Closure => ExprNode::Closure(def, field_ids),
        };
        let root = graph.intern_expr(node).unwrap();
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        let before = graph.expression_count();
        let entries = fields.iter().enumerate();
        for (index, expected) in entries {
            assert_eq!(graph.field(root, index).unwrap(), *expected);
        }
        assert_eq!(graph.field(root, fields.len()).unwrap(), unknown);
        assert_eq!(graph.field(root, usize::MAX).unwrap(), unknown);
        assert_eq!(graph.expression_count(), before);
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Wrapper {
    Typed,
    Select,
    Alternatives,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct WrappedProjection {
    fields: Vec<[u128; 2]>,
    wrappers: Vec<Wrapper>,
}

#[hegel::test(print_blob = true)]
fn nested_wrappers_project_each_branch(tc: hegel::TestCase) {
    let WrappedProjection { fields, wrappers } =
        tc.draw(hegel::generators::default::<WrappedProjection>());
    with_graph(|mut graph| {
        let mut expected = Vec::new();
        let mut otherwise = Vec::new();
        for [first, second] in fields {
            expected.push(graph.intern_expr(ExprNode::Number(first)).unwrap());
            otherwise.push(graph.intern_expr(ExprNode::Number(second)).unwrap());
        }
        let root_fields = graph
            .expression_sequences
            .from_iter(expected.iter().copied())
            .unwrap();
        let mut root = graph.intern_expr(ExprNode::Aggregate(root_fields)).unwrap();
        let alternate_fields = graph
            .expression_sequences
            .from_iter(otherwise.iter().copied())
            .unwrap();
        let alternative = graph
            .intern_expr(ExprNode::Aggregate(alternate_fields))
            .unwrap();
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        expected.push(unknown);
        otherwise.push(unknown);
        let entries = wrappers.into_iter().enumerate();
        for (index, wrapper) in entries {
            let input = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            let condition = graph.from_expr(input, 1).unwrap();
            root = match wrapper {
                Wrapper::Typed => {
                    let ty = graph.values.intern_type(&Type::Parameter(0)).unwrap();
                    graph.intern_expr(ExprNode::Typed(ty, root)).unwrap()
                }
                Wrapper::Select => graph
                    .intern_expr(ExprNode::Select(condition, root, alternative))
                    .unwrap(),
                Wrapper::Alternatives => graph.alternatives([root, alternative]).unwrap(),
            };
            let entries = expected.iter_mut().zip(&otherwise);
            for (expected, otherwise) in entries {
                *expected = match wrapper {
                    Wrapper::Typed => *expected,
                    Wrapper::Select => graph
                        .intern_expr(ExprNode::Select(condition, *expected, *otherwise))
                        .unwrap(),
                    Wrapper::Alternatives => graph.alternatives([*expected, *otherwise]).unwrap(),
                };
            }
        }
        let entries = expected.into_iter().enumerate();
        for (index, expected) in entries {
            assert_eq!(graph.field(root, index).unwrap(), expected);
        }
    });
}

#[test]
fn projecting_every_field_of_a_wide_aggregate_reuses_its_nodes() {
    with_graph(|mut graph| {
        let fields: Vec<_> = (0..100_000)
            .map(|index| graph.intern_expr(ExprNode::Argument(index)).unwrap())
            .collect();
        let field_ids = graph
            .expression_sequences
            .from_iter(fields.iter().copied())
            .unwrap();
        let root = graph.intern_expr(ExprNode::Aggregate(field_ids)).unwrap();
        let before = graph.expression_count();
        let entries = fields.into_iter().enumerate();
        for (index, expected) in entries {
            assert_eq!(graph.field(root, index).unwrap(), expected);
        }
        assert_eq!(graph.expression_count(), before);
    });
}

#[test]
fn deeply_nested_type_wrappers_project_without_recursion() {
    with_graph(|mut graph| {
        let field = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let fields = graph.expression_sequences.from_iter([field]).unwrap();
        let mut root = graph.intern_expr(ExprNode::Aggregate(fields)).unwrap();
        let ty = graph.values.intern_type(&Type::Parameter(0)).unwrap();
        for _ in 0..100_000 {
            root = graph.intern_expr(ExprNode::Typed(ty, root)).unwrap();
        }
        let before = graph.expression_count();
        assert_eq!(graph.field(root, 0).unwrap(), field);
        assert_eq!(graph.expression_count(), before);
    });
}
