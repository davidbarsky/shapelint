#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use shapelint_driver::calls::{Dispatch, Generic, Instance, Type};
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, NodeId, TargetNode, with_graph};
use shapelint_driver::contracts::operations::GraphInvalidation;
use shapelint_driver::contracts::{
    Arithmetic, Identity, Interval, Invocation, Join, Order, Origin, ProofGap, Relocation, Truth,
};
use shapelint_driver::sequence::Sequence;
use shapelint_driver::states::facts::{Dependencies, with_dependencies};

fn intern_aggregate<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    values: impl IntoIterator<Item = shapelint_driver::contracts::graph::ExprId<'g>>,
) -> Result<
    shapelint_driver::contracts::graph::ExprId<'g>,
    shapelint_driver::contracts::graph::CapacityError,
> {
    let values = graph.expression_sequences.from_iter(values)?;
    graph.intern_expr(ExprNode::Aggregate(values))
}

fn truth<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    condition: shapelint_driver::contracts::graph::ConditionId<'g>,
    guards: impl IntoIterator<Item = shapelint_driver::contracts::graph::ConditionId<'g>>,
) -> Result<Truth, shapelint_driver::contracts::graph::CapacityError> {
    let guards = graph.condition_sequences.from_iter(guards)?;
    graph.truth(condition, &guards)
}

fn typed<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    ty: Type,
    value: shapelint_driver::contracts::graph::ExprId<'g>,
) -> Result<
    shapelint_driver::contracts::graph::ExprId<'g>,
    shapelint_driver::contracts::graph::CapacityError,
> {
    let ty = graph.values.intern_type(&ty)?;
    graph.typed(ty, value)
}
fn substitute_expr<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    value: shapelint_driver::contracts::graph::ExprId<'g>,
    arguments: impl IntoIterator<Item = shapelint_driver::contracts::graph::ExprId<'g>>,
) -> Result<
    shapelint_driver::contracts::graph::ExprId<'g>,
    shapelint_driver::contracts::graph::CapacityError,
> {
    let arguments = graph.expression_sequences.from_iter(arguments)?;
    let scope = Invocation::LOCAL;
    graph.substitute_expr(value, &arguments, &scope)
}
fn substitute_condition<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    value: shapelint_driver::contracts::graph::ConditionId<'g>,
    arguments: impl IntoIterator<Item = shapelint_driver::contracts::graph::ExprId<'g>>,
) -> Result<
    shapelint_driver::contracts::graph::ConditionId<'g>,
    shapelint_driver::contracts::graph::CapacityError,
> {
    let arguments = graph.expression_sequences.from_iter(arguments)?;
    let scope = Invocation::LOCAL;
    graph.substitute_condition(value, &arguments, &scope)
}

fn intern_opaque<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    origin: Origin,
) -> Result<
    shapelint_driver::contracts::graph::ExprId<'g>,
    shapelint_driver::contracts::graph::CapacityError,
> {
    let origin = graph.values.intern_origin(&origin)?;
    graph.intern_expr(ExprNode::Opaque(origin))
}
fn intern_returned<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    target: TargetNode<'g>,
    arguments: impl IntoIterator<Item = shapelint_driver::contracts::graph::ExprId<'g>>,
) -> Result<
    shapelint_driver::contracts::graph::ConditionId<'g>,
    shapelint_driver::contracts::graph::CapacityError,
> {
    let arguments = graph.expression_sequences.from_iter(arguments)?;
    graph.intern_condition(ConditionNode::Returned(target, arguments))
}

fn intern_function<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    instance: Instance,
) -> Result<
    shapelint_driver::contracts::graph::ExprId<'g>,
    shapelint_driver::contracts::graph::CapacityError,
> {
    let instance = graph.values.intern_instance(&instance)?;
    graph.intern_expr(ExprNode::Function(instance))
}

fn intern_closure<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    def: rustc_hir::def_id::DefId,
    fields: impl IntoIterator<Item = shapelint_driver::contracts::graph::ExprId<'g>>,
) -> Result<
    shapelint_driver::contracts::graph::ExprId<'g>,
    shapelint_driver::contracts::graph::CapacityError,
> {
    let fields = graph.expression_sequences.from_iter(fields)?;
    graph.intern_expr(ExprNode::Closure(def, fields))
}
fn intern_variant<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    def: rustc_hir::def_id::DefId,
    variant: usize,
    fields: impl IntoIterator<Item = shapelint_driver::contracts::graph::ExprId<'g>>,
) -> Result<
    shapelint_driver::contracts::graph::ExprId<'g>,
    shapelint_driver::contracts::graph::CapacityError,
> {
    let fields = graph.expression_sequences.from_iter(fields)?;
    graph.intern_expr(ExprNode::Variant(def, variant, fields))
}
fn intern_call<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    target: TargetNode<'g>,
    args: impl IntoIterator<Item = shapelint_driver::contracts::graph::ExprId<'g>>,
    origin: Option<shapelint_driver::values::OriginId<'g>>,
) -> Result<
    shapelint_driver::contracts::graph::ExprId<'g>,
    shapelint_driver::contracts::graph::CapacityError,
> {
    let args = graph.expression_sequences.from_iter(args)?;
    graph.intern_expr(ExprNode::Call(target, args, origin))
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Relation {
    Less,
    LessEqual,
    Equal,
    NotEqual,
}

impl From<Relation> for Order {
    fn from(value: Relation) -> Self {
        match value {
            Relation::Less => Self::Less,
            Relation::LessEqual => Self::LessEqual,
            Relation::Equal => Self::Equal,
            Relation::NotEqual => Self::NotEqual,
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct Comparison {
    left: u128,
    right: u128,
    relation: Relation,
}

#[hegel::test(print_blob = true)]
fn concrete_comparisons_match_integer_order(tc: hegel::TestCase) {
    let Comparison {
        left,
        right,
        relation,
    } = tc.draw(hegel::generators::default::<Comparison>());
    let expected = match (relation, left.cmp(&right)) {
        (Relation::Less, std::cmp::Ordering::Less)
        | (Relation::LessEqual, std::cmp::Ordering::Less | std::cmp::Ordering::Equal)
        | (Relation::Equal, std::cmp::Ordering::Equal)
        | (Relation::NotEqual, std::cmp::Ordering::Less | std::cmp::Ordering::Greater) => {
            Truth::Proven
        }
        _ => Truth::Refuted,
    };
    with_graph(|mut graph| {
        let left = graph.intern_expr(ExprNode::Number(left)).unwrap();
        let right = graph.intern_expr(ExprNode::Number(right)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(relation.into(), left, right))
            .unwrap();
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            expected
        );
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ChoiceSource {
    Same,
    Opposite,
    Independent,
}

#[derive(Clone, Copy)]
enum Choice {
    First,
    Second,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct BranchComparison {
    left: [u8; 2],
    right: [u8; 2],
    relation: Relation,
    source: ChoiceSource,
}

#[hegel::test(print_blob = true)]
fn branch_comparisons_match_all_boolean_assignments(tc: hegel::TestCase) {
    let BranchComparison {
        left,
        right,
        relation,
        source,
    } = tc.draw(hegel::generators::default::<BranchComparison>());
    let mut outcomes = Vec::new();
    for first in [Choice::First, Choice::Second] {
        for second in [Choice::First, Choice::Second] {
            let left = match first {
                Choice::First => left[0],
                Choice::Second => left[1],
            };
            let right_choice = match (source, first) {
                (ChoiceSource::Same, choice) => choice,
                (ChoiceSource::Opposite, Choice::First) => Choice::Second,
                (ChoiceSource::Opposite, Choice::Second) => Choice::First,
                (ChoiceSource::Independent, _) => second,
            };
            let right = match right_choice {
                Choice::First => right[0],
                Choice::Second => right[1],
            };
            let outcome = match (relation, left.cmp(&right)) {
                (Relation::Less, std::cmp::Ordering::Less)
                | (Relation::LessEqual, std::cmp::Ordering::Less | std::cmp::Ordering::Equal)
                | (Relation::Equal, std::cmp::Ordering::Equal)
                | (Relation::NotEqual, std::cmp::Ordering::Less | std::cmp::Ordering::Greater) => {
                    Truth::Proven
                }
                _ => Truth::Refuted,
            };
            outcomes.push(outcome);
        }
    }
    let expected = match outcomes.as_slice() {
        [Truth::Proven, Truth::Proven, Truth::Proven, Truth::Proven] => Truth::Proven,
        [
            Truth::Refuted,
            Truth::Refuted,
            Truth::Refuted,
            Truth::Refuted,
        ] => Truth::Refuted,
        _ => Truth::Unknown(ProofGap::Comparison),
    };
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let second = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let first = graph.from_expr(first, 1).unwrap();
        let second = match source {
            ChoiceSource::Same => first,
            ChoiceSource::Opposite => graph.negate(first).unwrap(),
            ChoiceSource::Independent => graph.from_expr(second, 1).unwrap(),
        };
        let left_yes = graph
            .intern_expr(ExprNode::Number(u128::from(left[0])))
            .unwrap();
        let left_no = graph
            .intern_expr(ExprNode::Number(u128::from(left[1])))
            .unwrap();
        let right_yes = graph
            .intern_expr(ExprNode::Number(u128::from(right[0])))
            .unwrap();
        let right_no = graph
            .intern_expr(ExprNode::Number(u128::from(right[1])))
            .unwrap();
        let left = graph
            .intern_expr(ExprNode::Select(first, left_yes, left_no))
            .unwrap();
        let right = graph
            .intern_expr(ExprNode::Select(second, right_yes, right_no))
            .unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(relation.into(), left, right))
            .unwrap();
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            expected
        );
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct Bounds {
    left: u128,
    right: u128,
}

#[hegel::test(print_blob = true)]
fn join_contains_both_numeric_inputs(tc: hegel::TestCase) {
    let Bounds { left, right } = tc.draw(hegel::generators::default::<Bounds>());
    with_graph(|mut graph| {
        let left_id = graph.intern_expr(ExprNode::Number(left)).unwrap();
        let right_id = graph.intern_expr(ExprNode::Number(right)).unwrap();
        let joined = graph.join(left_id, right_id, Join::Hull).unwrap();
        let bounds = match &graph[joined] {
            ExprNode::Number(value) => (*value, *value),
            ExprNode::Range(Interval { lower, upper }) => (*lower, *upper),
            value => panic!("numeric join produced {value:?}"),
        };
        assert_eq!(bounds, (left.min(right), left.max(right)));
        assert_eq!(graph.join(right_id, left_id, Join::Hull).unwrap(), joined);
    });
}

#[test]
fn typed_branch_joins_keep_distinct_values_and_canonical_order() {
    with_graph(|mut graph| {
        let left = graph.intern_expr(ExprNode::Number(2)).unwrap();
        let right = graph.intern_expr(ExprNode::Number(9)).unwrap();
        let left = typed(&mut graph, Type::Bool, left).unwrap();
        let right = typed(&mut graph, Type::Char, right).unwrap();
        let forward = graph.join(left, right, Join::Hull).unwrap();
        let reverse = graph.join(right, left, Join::Hull).unwrap();
        assert_eq!(forward, reverse);
        match &graph[forward] {
            ExprNode::Alternatives(Some(root)) => assert_eq!(
                graph
                    .expression_sequences
                    .iter(graph[*root].values)
                    .copied()
                    .collect::<Vec<_>>(),
                [left, right]
            ),
            node => panic!("expected alternatives, got {node:?}"),
        }
    });
}

#[test]
fn equal_unknown_nodes_do_not_prove_equal_runtime_values() {
    with_graph(|mut graph| {
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, unknown, unknown))
            .unwrap();
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Value)
        );
    });
}

#[test]
fn join_of_unknown_branches_does_not_create_runtime_identity() {
    with_graph(|mut graph| {
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        let value = graph.intern_expr(ExprNode::Number(7)).unwrap();
        let joined = graph.join(unknown, value, Join::Hull).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, joined, joined))
            .unwrap();
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Value)
        );
    });
}

#[test]
fn deeply_shared_substitution_preserves_one_result_per_input_node() {
    with_graph(|mut graph| {
        let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let replacement = graph.intern_expr(ExprNode::Number(23)).unwrap();
        let mut root = argument;
        let mut prefixes = Vec::new();
        for _ in 0..100_000 {
            root = intern_aggregate(&mut graph, vec![root, root]).unwrap();
            prefixes.push(root);
        }
        let before = graph.expression_count();
        let substituted = substitute_expr(&mut graph, root, vec![replacement]).unwrap();
        assert_eq!(graph.expression_count() - before, 100_000);
        let mut value = substituted;
        let prefixes = prefixes.into_iter().rev();
        for prefix in prefixes {
            assert_eq!(
                substitute_expr(&mut graph, prefix, vec![replacement]).unwrap(),
                value
            );
            match &graph[value] {
                ExprNode::Aggregate(fields) => {
                    let left = *graph.expression_sequences.get(*fields, 0).unwrap();
                    let right = *graph.expression_sequences.get(*fields, 1).unwrap();
                    assert_eq!(left, right);
                    value = left;
                }
                node => panic!("expected shared aggregate, got {node:?}"),
            }
        }
        assert_eq!(value, replacement);
        assert_eq!(
            substitute_expr(&mut graph, root, vec![replacement]).unwrap(),
            substituted
        );
    });
}

#[test]
fn deeply_shared_memory_invalidation_preserves_sharing() {
    with_graph(|mut graph| {
        let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let mut root = argument;
        let mut prefixes = Vec::new();
        for _ in 0..100_000 {
            root = intern_aggregate(&mut graph, vec![root, root]).unwrap();
            prefixes.push(root);
        }
        with_dependencies(|stores| {
            let mut dependencies = Dependencies::default();
            dependencies
                .insert(stores, (), NodeId::Expr(root), &graph)
                .unwrap();
            let affected = dependencies
                .affected(stores, GraphInvalidation::Memory(argument), &mut graph)
                .unwrap();
            let before = graph.expression_count();
            let invalidated = graph
                .invalidate_expr(root, GraphInvalidation::Memory(argument), affected)
                .unwrap();
            assert_eq!(graph.expression_count() - before, 100_001);
            let mut value = invalidated;
            let prefixes = prefixes.into_iter().rev();
            for prefix in prefixes {
                assert_eq!(
                    graph
                        .invalidate_expr(prefix, GraphInvalidation::Memory(argument), affected)
                        .unwrap(),
                    value
                );
                match &graph[value] {
                    ExprNode::Aggregate(fields) => {
                        let left = *graph.expression_sequences.get(*fields, 0).unwrap();
                        let right = *graph.expression_sequences.get(*fields, 1).unwrap();
                        assert_eq!(left, right);
                        value = left;
                    }
                    node => panic!("expected shared aggregate, got {node:?}"),
                }
            }
            assert_eq!(graph.known(NodeId::Expr(value)), None);
            let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
            assert_eq!(value, unknown);
        });
    });
}

#[test]
fn identical_opaque_metadata_without_identity_does_not_prove_equality() {
    with_graph(|mut graph| {
        let value = intern_opaque(
            &mut graph,
            Origin {
                def: rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
                name: Some("untracked".to_owned()),
                adt: None,
                identity: None,
            },
        )
        .unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, value, value))
            .unwrap();
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Value)
        );
    });
}

#[test]
fn opaque_branch_join_does_not_gain_identity() {
    with_graph(|mut graph| {
        let opaque = intern_opaque(
            &mut graph,
            Origin {
                def: rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
                name: Some("untracked".to_owned()),
                adt: None,
                identity: None,
            },
        )
        .unwrap();
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        let joined = graph.join(opaque, unknown, Join::Hull).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, joined, joined))
            .unwrap();
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Value)
        );
    });
}

#[hegel::test(print_blob = true)]
fn interval_upper_bound_proves_every_member_is_bounded(tc: hegel::TestCase) {
    let Bounds { left, right } = tc.draw(hegel::generators::default::<Bounds>());
    with_graph(|mut graph| {
        let range = graph
            .intern_expr(ExprNode::Range(Interval {
                lower: left.min(right),
                upper: left.max(right),
            }))
            .unwrap();
        let maximum = graph
            .intern_expr(ExprNode::Number(left.max(right)))
            .unwrap();
        let bounded = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, range, maximum))
            .unwrap();
        assert_eq!(
            graph.truth(bounded, &Sequence::default()).unwrap(),
            Truth::Proven
        );
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct Decrement {
    amount: u8,
}

#[hegel::test(print_blob = true)]
fn guarded_positive_subtraction_is_strictly_below_the_upper_bound(tc: hegel::TestCase) {
    let Decrement { amount } = tc.draw(hegel::generators::default::<Decrement>());
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let upper = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let amount = graph
            .intern_expr(ExprNode::Number(u128::from(amount) + 1))
            .unwrap();
        let subtraction = graph
            .intern_expr(ExprNode::Arithmetic(
                Arithmetic::Subtract(rustc_middle::ty::UintTy::U128),
                value,
                amount,
            ))
            .unwrap();
        let nonnegative = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, amount, value))
            .unwrap();
        let bounded = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, value, upper))
            .unwrap();
        let strict = graph
            .intern_condition(ConditionNode::Compare(Order::Less, subtraction, upper))
            .unwrap();
        assert_eq!(
            truth(&mut graph, strict, vec![nonnegative, bounded]).unwrap(),
            Truth::Proven
        );
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Strength {
    Strict,
    Inclusive,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Chain {
    edges: Vec<Strength>,
}

#[hegel::test(print_blob = true)]
fn transitive_comparisons_preserve_the_strict_edge(tc: hegel::TestCase) {
    let Chain { edges } = tc.draw(hegel::generators::default::<Chain>());
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let mut last = first;
        let mut guards = Sequence::default();
        let mut relation = Order::LessEqual;
        let edges = edges.into_iter().enumerate();
        for (index, edge) in edges {
            let next = graph.intern_expr(ExprNode::Argument(index + 1)).unwrap();
            let order = match edge {
                Strength::Strict => {
                    relation = Order::Less;
                    Order::Less
                }
                Strength::Inclusive => Order::LessEqual,
            };
            let guard = graph
                .intern_condition(ConditionNode::Compare(order, last, next))
                .unwrap();
            guards = graph.condition_sequences.push(guards, guard).unwrap();
            last = next;
        }
        let condition = graph
            .intern_condition(ConditionNode::Compare(relation, first, last))
            .unwrap();
        assert_eq!(graph.truth(condition, &guards).unwrap(), Truth::Proven);
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct VariantCase {
    actual: u8,
    excluded: u8,
}

#[hegel::test(print_blob = true)]
fn negating_a_variant_excludes_exactly_that_discriminant(tc: hegel::TestCase) {
    let VariantCase { actual, excluded } = tc.draw(hegel::generators::default::<VariantCase>());
    let actual = usize::from(actual);
    let excluded = usize::from(excluded) + 2;
    let expected = match actual.cmp(&excluded) {
        std::cmp::Ordering::Equal => Truth::Refuted,
        std::cmp::Ordering::Less | std::cmp::Ordering::Greater => Truth::Proven,
    };
    with_graph(|mut graph| {
        let value = intern_variant(
            &mut graph,
            rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
            actual,
            Vec::new(),
        )
        .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Variant(value, excluded))
            .unwrap();
        let negated = graph.negate(required).unwrap();
        assert_eq!(
            graph.truth(negated, &Sequence::default()).unwrap(),
            expected
        );
        assert_eq!(graph.negate(negated).unwrap(), required);
    });
}

#[hegel::test(print_blob = true)]
fn excluding_a_variant_does_not_choose_another_variant(tc: hegel::TestCase) {
    let excluded = tc.draw(hegel::generators::integers::<u8>());
    let excluded = usize::from(excluded) + 2;
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let exclusion = graph
            .intern_condition(ConditionNode::NotVariant(value, excluded))
            .unwrap();
        let another = graph
            .intern_condition(ConditionNode::Variant(value, excluded + 1))
            .unwrap();
        assert_eq!(
            truth(&mut graph, another, vec![exclusion]).unwrap(),
            Truth::Unknown(ProofGap::Variant)
        );
    });
}

#[hegel::test(print_blob = true)]
fn boolean_selections_share_their_predicate(tc: hegel::TestCase) {
    let relation = tc.draw(hegel::generators::default::<Relation>());
    with_graph(|mut graph| {
        let left = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let right = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(relation.into(), left, right))
            .unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let selected = graph
            .intern_expr(ExprNode::Select(condition, one, zero))
            .unwrap();
        let tested = graph.intern_expr(ExprNode::Test(condition)).unwrap();
        assert_eq!(selected, tested);
        let negated = graph.negate(condition).unwrap();
        let opposite = graph
            .intern_expr(ExprNode::Select(condition, zero, one))
            .unwrap();
        let tested = graph.intern_expr(ExprNode::Test(negated)).unwrap();
        assert_eq!(opposite, tested);
    });
}

#[hegel::test(print_blob = true)]
fn complementary_paths_cover_every_assignment(tc: hegel::TestCase) {
    let relation = tc.draw(hegel::generators::default::<Relation>());
    with_graph(|mut graph| {
        let left = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let right = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(relation.into(), left, right))
            .unwrap();
        let negated = graph.negate(condition).unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let first = graph
            .intern_expr(ExprNode::Select(condition, one, zero))
            .unwrap();
        let second = graph
            .intern_expr(ExprNode::Select(negated, one, zero))
            .unwrap();
        let first = graph.from_expr(first, 1).unwrap();
        let union = graph
            .intern_expr(ExprNode::Select(first, one, second))
            .unwrap();
        let union = graph.from_expr(union, 1).unwrap();
        assert_eq!(
            graph.truth(union, &Sequence::default()).unwrap(),
            Truth::Proven
        );
    });
}

#[hegel::test(print_blob = true)]
fn numeric_selections_preserve_nonboolean_values(tc: hegel::TestCase) {
    let number = u128::from(tc.draw(hegel::generators::integers::<u64>())) + 2;
    with_graph(|mut graph| {
        let left = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let right = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, left, right))
            .unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let number = graph.intern_expr(ExprNode::Number(number)).unwrap();
        let selected = graph
            .intern_expr(ExprNode::Select(condition, number, zero))
            .unwrap();
        let required = graph.from_expr(selected, 1).unwrap();
        assert_eq!(
            graph.truth(required, &Sequence::default()).unwrap(),
            Truth::Refuted
        );
    });
}

#[test]
fn an_unresolved_call_does_not_prove_that_it_returns() {
    with_graph(|mut graph| {
        let target = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let returned =
            intern_returned(&mut graph, TargetNode::Indirect(target), Vec::new()).unwrap();
        assert_eq!(
            graph.truth(returned, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Return)
        );
    });
}

#[test]
fn complementary_paths_keep_their_shared_return_requirement() {
    with_graph(|mut graph| {
        let target = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let returned =
            intern_returned(&mut graph, TargetNode::Indirect(target), Vec::new()).unwrap();
        let left = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let right = graph.intern_expr(ExprNode::Argument(2)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, left, right))
            .unwrap();
        let negated = graph.negate(condition).unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let required = graph.intern_expr(ExprNode::Test(returned)).unwrap();
        let first = graph
            .intern_expr(ExprNode::Select(condition, required, zero))
            .unwrap();
        let second = graph
            .intern_expr(ExprNode::Select(negated, required, zero))
            .unwrap();
        let first = graph.from_expr(first, 1).unwrap();
        let union = graph
            .intern_expr(ExprNode::Select(first, required, second))
            .unwrap();
        let union = graph.from_expr(union, 1).unwrap();
        match graph.truth(union, &Sequence::default()).unwrap() {
            Truth::Unknown(_) => {}
            truth => panic!("unresolved return requirement became {truth:?}"),
        }
    });
}

#[hegel::test(print_blob = true)]
fn repeated_truth_queries_keep_guard_contexts_distinct(tc: hegel::TestCase) {
    let relation = tc.draw(hegel::generators::default::<Relation>());
    with_graph(|mut graph| {
        let left = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let right = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(relation.into(), left, right))
            .unwrap();
        let negated = graph.negate(condition).unwrap();
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
        assert_eq!(
            truth(&mut graph, condition, vec![condition]).unwrap(),
            Truth::Proven
        );
        assert_eq!(
            truth(&mut graph, condition, vec![negated]).unwrap(),
            Truth::Refuted
        );
        assert_eq!(
            truth(&mut graph, condition, vec![condition]).unwrap(),
            Truth::Proven
        );
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
        assert_eq!(
            truth(&mut graph, condition, vec![negated]).unwrap(),
            Truth::Refuted
        );
    });
}

#[hegel::test(print_blob = true)]
fn appended_nodes_preserve_completed_truth_queries(tc: hegel::TestCase) {
    let number = tc.draw(hegel::generators::integers::<u128>());
    with_graph(|mut graph| {
        let left = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let right = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Less, left, right))
            .unwrap();
        assert_eq!(
            graph.truth(required, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
        let number = graph.intern_expr(ExprNode::Number(number)).unwrap();
        let lower = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, left, number))
            .unwrap();
        let upper = graph
            .intern_condition(ConditionNode::Compare(Order::Less, number, right))
            .unwrap();
        assert_eq!(
            truth(&mut graph, required, vec![lower, upper]).unwrap(),
            Truth::Proven
        );
        assert_eq!(
            graph.truth(required, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
        assert_eq!(
            truth(&mut graph, required, vec![lower, upper]).unwrap(),
            Truth::Proven
        );
    });
}

#[hegel::test(print_blob = true)]
fn graph_input_inspection_collects_shared_argument_dependencies(tc: hegel::TestCase) {
    let arguments = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_graph(|mut graph| {
        let fields = arguments
            .iter()
            .map(|index| {
                graph
                    .intern_expr(ExprNode::Argument(usize::from(*index)))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let aggregate = intern_aggregate(&mut graph, fields).unwrap();
        let shared = intern_aggregate(&mut graph, vec![aggregate, aggregate]).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, shared, aggregate))
            .unwrap();
        let expected = arguments.into_iter().map(usize::from).collect();
        assert_eq!(
            graph
                .inputs(NodeId::Condition(condition))
                .expect("input summary"),
            Some(expected)
        );
    });
}

#[test]
fn graph_input_inspection_keeps_unsupported_dependencies_unknown() {
    with_graph(|mut graph| {
        let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        let aggregate = intern_aggregate(&mut graph, vec![argument, unknown]).unwrap();
        assert_eq!(
            graph
                .inputs(NodeId::Expr(aggregate))
                .expect("input summary"),
            None
        );
    });
}

#[test]
fn deeply_shared_function_values_are_inspected_without_expanding_paths() {
    with_graph(|mut graph| {
        let def = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        let mut value = intern_closure(&mut graph, def, Vec::new()).unwrap();
        for _ in 0..100_000 {
            value = intern_aggregate(&mut graph, vec![value, value]).unwrap();
        }
        let mut functions = rustc_data_structures::fx::FxHashSet::default();
        graph
            .functions(value, &mut functions)
            .expect("function summary");
        assert_eq!(functions, [def].into_iter().collect());
    });
}

#[test]
fn deeply_wrapped_serializations_retain_the_original_metadata_node() {
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let serialized = graph
            .intern_expr(ExprNode::Serialized {
                value,
                def: rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
                span: rustc_span::DUMMY_SP,
                encoding: shapelint_driver::transfers::Encoding::Value,
                ty: rustc_data_structures::fingerprint::Fingerprint::new(0, 0),
            })
            .unwrap();
        let mut value = serialized;
        for _ in 0..100_000 {
            value = intern_aggregate(&mut graph, vec![value]).unwrap();
        }
        assert_eq!(graph.serialization(value), Some(serialized));
    });
}

#[test]
fn serialization_inspection_does_not_unwrap_multiple_fields() {
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let serialized = graph
            .intern_expr(ExprNode::Serialized {
                value,
                def: rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
                span: rustc_span::DUMMY_SP,
                encoding: shapelint_driver::transfers::Encoding::Value,
                ty: rustc_data_structures::fingerprint::Fingerprint::new(0, 0),
            })
            .unwrap();
        let ambiguous = intern_aggregate(&mut graph, vec![serialized, serialized]).unwrap();
        assert_eq!(graph.serialization(ambiguous), None);
    });
}

#[hegel::test(print_blob = true)]
fn truth_contexts_preserve_the_order_of_guard_witnesses(tc: hegel::TestCase) {
    let first = usize::from(tc.draw(hegel::generators::integers::<u8>()));
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let first = graph
            .intern_condition(ConditionNode::Variant(value, first))
            .unwrap();
        let second = graph
            .intern_condition(ConditionNode::Variant(value, usize::from(u8::MAX) + 1))
            .unwrap();
        assert_eq!(
            truth(&mut graph, first, vec![first, second]).unwrap(),
            Truth::Proven
        );
        assert_eq!(
            truth(&mut graph, first, vec![second, first]).unwrap(),
            Truth::Refuted
        );
        assert_eq!(
            truth(&mut graph, first, vec![first, first, second]).unwrap(),
            Truth::Proven
        );
        assert_eq!(
            truth(&mut graph, first, vec![second, first]).unwrap(),
            Truth::Refuted
        );
        assert_eq!(
            truth(&mut graph, first, vec![first, second]).unwrap(),
            Truth::Proven
        );
    });
}

#[test]
fn repeated_branch_contexts_remain_stack_safe() {
    with_graph(|mut graph| {
        let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, argument, zero))
            .unwrap();
        let mut value = graph.intern_expr(ExprNode::Number(1)).unwrap();
        for _ in 0..100_000 {
            value = graph
                .intern_expr(ExprNode::Select(condition, value, zero))
                .unwrap();
        }
        let required = graph.from_expr(value, 1).unwrap();
        assert_eq!(
            truth(&mut graph, required, vec![condition]).unwrap(),
            Truth::Proven
        );
        let opposite = graph.negate(condition).unwrap();
        assert_eq!(
            truth(&mut graph, required, vec![opposite]).unwrap(),
            Truth::Refuted
        );
        assert_eq!(
            graph.truth(required, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
        assert_eq!(
            truth(&mut graph, required, vec![condition]).unwrap(),
            Truth::Proven
        );
    });
}

#[hegel::test(print_blob = true)]
fn rewrite_contexts_distinguish_invalidation_kinds_targets_and_values(tc: hegel::TestCase) {
    let number = u128::from(tc.draw(hegel::generators::integers::<u64>()));
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let other = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let first = graph.intern_expr(ExprNode::Number(number)).unwrap();
        let second = graph.intern_expr(ExprNode::Number(number + 1)).unwrap();
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        with_dependencies(|stores| {
            let mut dependencies = Dependencies::default();
            dependencies
                .insert(stores, (), NodeId::Expr(value), &graph)
                .unwrap();
            let replace_first = GraphInvalidation::Replace {
                target: value,
                value: first,
            };
            let replace_second = GraphInvalidation::Replace {
                target: value,
                value: second,
            };
            let replace_other = GraphInvalidation::Replace {
                target: other,
                value: first,
            };
            let affected = dependencies
                .affected(stores, replace_first, &mut graph)
                .unwrap();
            assert_eq!(
                graph
                    .invalidate_expr(value, replace_first, affected)
                    .unwrap(),
                first
            );
            let affected = dependencies
                .affected(stores, replace_second, &mut graph)
                .unwrap();
            assert_eq!(
                graph
                    .invalidate_expr(value, replace_second, affected)
                    .unwrap(),
                second
            );
            let affected = dependencies
                .affected(stores, replace_other, &mut graph)
                .unwrap();
            assert_eq!(
                graph
                    .invalidate_expr(value, replace_other, affected)
                    .unwrap(),
                value
            );
            let affected = dependencies
                .affected(stores, GraphInvalidation::Memory(value), &mut graph)
                .unwrap();
            assert_eq!(
                graph
                    .invalidate_expr(value, GraphInvalidation::Memory(value), affected)
                    .unwrap(),
                unknown
            );
            let affected = dependencies
                .affected(
                    stores,
                    GraphInvalidation::Local(rustc_middle::mir::Local::from_usize(0)),
                    &mut graph,
                )
                .unwrap();
            assert_eq!(
                graph
                    .invalidate_expr(
                        value,
                        GraphInvalidation::Local(rustc_middle::mir::Local::from_usize(0)),
                        affected,
                    )
                    .unwrap(),
                value
            );
            assert_eq!(graph.provenance(value).unwrap(), unknown);
            let affected = dependencies
                .affected(stores, replace_first, &mut graph)
                .unwrap();
            assert_eq!(
                graph
                    .invalidate_expr(value, replace_first, affected)
                    .unwrap(),
                first
            );
        });
    });
}

#[hegel::test(print_blob = true)]
fn rewrite_contexts_distinguish_retired_locals(tc: hegel::TestCase) {
    let local = usize::from(tc.draw(hegel::generators::integers::<u8>()));
    with_graph(|mut graph| {
        let local = rustc_middle::mir::Local::from_usize(local);
        let other = rustc_middle::mir::Local::from_usize(usize::from(u8::MAX) + 1);
        let value = graph
            .intern_expr(ExprNode::Cursor {
                def: rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
                local,
            })
            .unwrap();
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        with_dependencies(|stores| {
            let mut dependencies = Dependencies::default();
            dependencies
                .insert(stores, (), NodeId::Expr(value), &graph)
                .unwrap();
            let affected = dependencies
                .affected(stores, GraphInvalidation::Local(local), &mut graph)
                .unwrap();
            assert_eq!(
                graph
                    .invalidate_expr(value, GraphInvalidation::Local(local), affected)
                    .unwrap(),
                unknown
            );
            let affected = dependencies
                .affected(stores, GraphInvalidation::Local(other), &mut graph)
                .unwrap();
            assert_eq!(
                graph
                    .invalidate_expr(value, GraphInvalidation::Local(other), affected)
                    .unwrap(),
                value
            );
            let affected = dependencies
                .affected(stores, GraphInvalidation::Local(local), &mut graph)
                .unwrap();
            assert_eq!(
                graph
                    .invalidate_expr(value, GraphInvalidation::Local(local), affected)
                    .unwrap(),
                unknown
            );
        });
    });
}

#[hegel::test(print_blob = true)]
fn substitution_preserves_shared_sequence_values_across_contexts(tc: hegel::TestCase) {
    let number = u128::from(tc.draw(hegel::generators::integers::<u64>()));
    with_graph(|mut graph| {
        let left = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let right = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Less, left, right))
            .unwrap();
        let first = graph.intern_expr(ExprNode::Number(number)).unwrap();
        let second = graph.intern_expr(ExprNode::Number(number + 1)).unwrap();
        let values: Sequence<_> = graph
            .expression_sequences
            .from_iter([left, right, left])
            .unwrap();
        let guards: Sequence<_> = graph
            .condition_sequences
            .from_iter([condition, condition])
            .unwrap();
        let forward: Sequence<_> = graph
            .expression_sequences
            .from_iter([first, second])
            .unwrap();
        let backward: Sequence<_> = graph
            .expression_sequences
            .from_iter([second, first])
            .unwrap();
        let mapped = graph
            .substitute_arguments(&values, &forward, &Invocation::LOCAL)
            .unwrap();
        assert_eq!(
            graph
                .expression_sequences
                .iter(mapped)
                .copied()
                .collect::<Vec<_>>(),
            vec![first, second, first]
        );
        let mapped = graph
            .substitute_arguments(&values, &backward, &Invocation::LOCAL)
            .unwrap();
        assert_eq!(
            graph
                .expression_sequences
                .iter(mapped)
                .copied()
                .collect::<Vec<_>>(),
            vec![second, first, second]
        );
        let mapped = graph
            .substitute_arguments(&values, &forward, &Invocation::LOCAL)
            .unwrap();
        assert_eq!(
            graph
                .expression_sequences
                .iter(mapped)
                .copied()
                .collect::<Vec<_>>(),
            vec![first, second, first]
        );
        let forward_guards = graph
            .substitute_guards(&guards, &forward, &Invocation::LOCAL)
            .unwrap();
        let backward_guards = graph
            .substitute_guards(&guards, &backward, &Invocation::LOCAL)
            .unwrap();
        let rebuilt_guards: Sequence<_> = graph
            .condition_sequences
            .from_iter([condition, condition])
            .unwrap();
        let rebuilt_forward: Sequence<_> = graph
            .expression_sequences
            .from_iter([first, second])
            .unwrap();
        let repeated = graph
            .substitute_guards(&rebuilt_guards, &rebuilt_forward, &Invocation::LOCAL)
            .unwrap();
        let repeated_values = graph
            .condition_sequences
            .iter(repeated)
            .copied()
            .collect::<Vec<_>>();
        let forward_values = graph
            .condition_sequences
            .iter(forward_guards)
            .copied()
            .collect::<Vec<_>>();
        assert_eq!(repeated_values, forward_values);
        let backward_values = graph
            .condition_sequences
            .iter(backward_guards)
            .copied()
            .collect::<Vec<_>>();
        assert_eq!(forward_values.len(), 2);
        assert_eq!(forward_values[0], forward_values[1]);
        assert_eq!(backward_values.len(), 2);
        assert_eq!(backward_values[0], backward_values[1]);
        assert_eq!(
            graph
                .truth(forward_values[0], &Sequence::default())
                .unwrap(),
            Truth::Proven
        );
        assert_eq!(
            graph
                .truth(backward_values[0], &Sequence::default())
                .unwrap(),
            Truth::Refuted
        );
    });
}

#[hegel::test(print_blob = true)]
fn substitution_contexts_distinguish_argument_order_and_length(tc: hegel::TestCase) {
    let number = u128::from(tc.draw(hegel::generators::integers::<u64>()));
    with_graph(|mut graph| {
        let left = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let right = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let aggregate = intern_aggregate(&mut graph, vec![left, right]).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Less, left, right))
            .unwrap();
        let first = graph.intern_expr(ExprNode::Number(number)).unwrap();
        let second = graph.intern_expr(ExprNode::Number(number + 1)).unwrap();
        let forward = intern_aggregate(&mut graph, vec![first, second]).unwrap();
        let backward = intern_aggregate(&mut graph, vec![second, first]).unwrap();
        assert_eq!(
            substitute_expr(&mut graph, aggregate, vec![first, second]).unwrap(),
            forward
        );
        assert_eq!(
            substitute_expr(&mut graph, aggregate, vec![second, first]).unwrap(),
            backward
        );
        let increasing = substitute_condition(&mut graph, condition, vec![first, second]).unwrap();
        let decreasing = substitute_condition(&mut graph, condition, vec![second, first]).unwrap();
        assert_eq!(
            graph.truth(increasing, &Sequence::default()).unwrap(),
            Truth::Proven
        );
        assert_eq!(
            graph.truth(decreasing, &Sequence::default()).unwrap(),
            Truth::Refuted
        );
        let missing = substitute_condition(&mut graph, condition, vec![first]).unwrap();
        assert_eq!(
            graph.truth(missing, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Value)
        );
        assert_eq!(
            substitute_expr(&mut graph, aggregate, vec![first, second]).unwrap(),
            forward
        );
    });
}

#[test]
fn substitution_contexts_distinguish_generic_bindings() {
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let generic = typed(&mut graph, Type::Parameter(0), value).unwrap();
        let boolean = graph
            .values
            .intern_generic(&Generic::Type(Type::Bool))
            .unwrap();
        let boolean = Invocation {
            relocation: Relocation::Preserve,
            generics: graph
                .values
                .intern_list::<shapelint_driver::values::GenericsId<'_>>([boolean])
                .unwrap(),
        };
        let character = graph
            .values
            .intern_generic(&Generic::Type(Type::Char))
            .unwrap();
        let character = Invocation {
            relocation: Relocation::Preserve,
            generics: graph
                .values
                .intern_list::<shapelint_driver::values::GenericsId<'_>>([character])
                .unwrap(),
        };
        let expected_boolean = typed(&mut graph, Type::Bool, value).unwrap();
        let expected_character = typed(&mut graph, Type::Char, value).unwrap();
        assert_eq!(
            graph
                .substitute_expr(generic, &Sequence::default(), &boolean)
                .unwrap(),
            expected_boolean
        );
        assert_eq!(
            graph
                .substitute_expr(generic, &Sequence::default(), &character)
                .unwrap(),
            expected_character
        );
        assert_eq!(
            graph
                .substitute_expr(generic, &Sequence::default(), &boolean)
                .unwrap(),
            expected_boolean
        );
    });
}

#[test]
fn substitution_contexts_distinguish_preserved_and_lost_identity() {
    with_graph(|mut graph| {
        let value = graph
            .intern_expr(ExprNode::Cursor {
                def: rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
                local: rustc_middle::mir::Local::from_usize(0),
            })
            .unwrap();
        let relocated = Invocation {
            relocation: Relocation::Into(None),
            generics: shapelint_driver::values::GenericsId::EMPTY,
        };
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        assert_eq!(
            graph
                .substitute_expr(value, &Sequence::default(), &Invocation::LOCAL)
                .unwrap(),
            value
        );
        assert_eq!(
            graph
                .substitute_expr(value, &Sequence::default(), &relocated)
                .unwrap(),
            unknown
        );
        assert_eq!(
            graph
                .substitute_expr(value, &Sequence::default(), &Invocation::LOCAL)
                .unwrap(),
            value
        );
    });
}

#[hegel::test(print_blob = true)]
fn substitution_contexts_distinguish_invocation_call_paths(tc: hegel::TestCase) {
    let local = usize::from(tc.draw(hegel::generators::integers::<u8>()));
    with_graph(|mut graph| {
        let def = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        let original = Identity {
            origin: (def, rustc_middle::mir::Local::from_usize(0)),
            fields: Vec::new(),
            calls: Vec::new(),
        };
        let first_call = (def, rustc_middle::mir::Local::from_usize(local));
        let second_call = (
            def,
            rustc_middle::mir::Local::from_usize(usize::from(u8::MAX) + 1),
        );
        let scope_origin = (
            def,
            rustc_middle::mir::Local::from_usize(usize::from(u8::MAX) + 2),
        );
        let identity = graph
            .values
            .intern_identity(&Identity {
                origin: scope_origin,
                fields: Vec::new(),
                calls: vec![first_call],
            })
            .unwrap();
        let first = Invocation {
            relocation: Relocation::Into(Some(identity)),
            generics: shapelint_driver::values::GenericsId::EMPTY,
        };
        let identity = graph
            .values
            .intern_identity(&Identity {
                origin: scope_origin,
                fields: Vec::new(),
                calls: vec![second_call],
            })
            .unwrap();
        let second = Invocation {
            relocation: Relocation::Into(Some(identity)),
            generics: shapelint_driver::values::GenericsId::EMPTY,
        };
        let value = intern_opaque(
            &mut graph,
            Origin {
                def,
                name: None,
                adt: None,
                identity: Some(original.clone()),
            },
        )
        .unwrap();
        let first_expected = intern_opaque(
            &mut graph,
            Origin {
                def,
                name: None,
                adt: None,
                identity: Some(Identity {
                    calls: vec![first_call, scope_origin],
                    ..original.clone()
                }),
            },
        )
        .unwrap();
        let second_expected = intern_opaque(
            &mut graph,
            Origin {
                def,
                name: None,
                adt: None,
                identity: Some(Identity {
                    calls: vec![second_call, scope_origin],
                    ..original
                }),
            },
        )
        .unwrap();
        assert_eq!(
            graph
                .substitute_expr(value, &Sequence::default(), &first)
                .unwrap(),
            first_expected
        );
        assert_eq!(
            graph
                .substitute_expr(value, &Sequence::default(), &second)
                .unwrap(),
            second_expected
        );
        assert_eq!(
            graph
                .substitute_expr(value, &Sequence::default(), &first)
                .unwrap(),
            first_expected
        );
    });
}

#[hegel::test(print_blob = true)]
fn strict_integer_lower_bounds_include_their_successor(tc: hegel::TestCase) {
    let lower = tc.draw(hegel::generators::integers::<u128>().max_value(u128::MAX - 1));
    let successor = lower.checked_add(1).unwrap();
    with_graph(|mut graph| {
        let bound = graph.intern_expr(ExprNode::Number(lower)).unwrap();
        let adjacent = graph.intern_expr(ExprNode::Number(successor)).unwrap();
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let next = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let strict = graph
            .intern_condition(ConditionNode::Compare(Order::Less, bound, value))
            .unwrap();
        let bridge = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, value, next))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, adjacent, next))
            .unwrap();
        assert_eq!(
            truth(&mut graph, required, vec![strict, bridge]).unwrap(),
            Truth::Proven
        );
        let too_strong = graph
            .intern_condition(ConditionNode::Compare(Order::Less, adjacent, next))
            .unwrap();
        assert_ne!(
            truth(&mut graph, too_strong, vec![strict, bridge]).unwrap(),
            Truth::Proven
        );
    });
}

#[hegel::test(print_blob = true)]
fn strict_integer_upper_bounds_include_their_predecessor(tc: hegel::TestCase) {
    let upper = tc.draw(hegel::generators::integers::<u128>().min_value(1));
    let predecessor = upper.checked_sub(1).unwrap();
    with_graph(|mut graph| {
        let bound = graph.intern_expr(ExprNode::Number(upper)).unwrap();
        let adjacent = graph.intern_expr(ExprNode::Number(predecessor)).unwrap();
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let previous = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let strict = graph
            .intern_condition(ConditionNode::Compare(Order::Less, value, bound))
            .unwrap();
        let bridge = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, previous, value))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, previous, adjacent))
            .unwrap();
        assert_eq!(
            truth(&mut graph, required, vec![strict, bridge]).unwrap(),
            Truth::Proven
        );
        let too_strong = graph
            .intern_condition(ConditionNode::Compare(Order::Less, previous, adjacent))
            .unwrap();
        assert_ne!(
            truth(&mut graph, too_strong, vec![strict, bridge]).unwrap(),
            Truth::Proven
        );
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum KnowledgeStep {
    Pair,
    Length,
    Untracked,
    Returned,
}

#[hegel::test(print_blob = true)]
fn graph_knowledge_is_reused_without_losing_unknown_descendants(tc: hegel::TestCase) {
    let steps = tc.draw(hegel::generators::default::<Vec<KnowledgeStep>>());
    with_graph(|mut graph| {
        let mut value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let mut expected = Some(());
        let mut previous = vec![(value, expected)];
        for step in steps {
            let node = match step {
                KnowledgeStep::Pair => {
                    let fields = graph
                        .expression_sequences
                        .from_iter([value, value])
                        .unwrap();
                    ExprNode::Aggregate(fields)
                }
                KnowledgeStep::Length => ExprNode::Length(value),
                KnowledgeStep::Untracked => {
                    expected = None;
                    ExprNode::Unknown
                }
                KnowledgeStep::Returned => {
                    expected = Some(());
                    let condition =
                        intern_returned(&mut graph, TargetNode::Indirect(value), vec![value])
                            .unwrap();
                    assert_eq!(graph.known(NodeId::Condition(condition)), expected);
                    ExprNode::Test(condition)
                }
            };
            value = graph.intern_expr(node).unwrap();
            assert_eq!(graph.known(NodeId::Expr(value)), expected);
            let index =
                tc.draw(hegel::generators::integers::<usize>().max_value(previous.len() - 1));
            let (old, old_expected) = previous[index];
            assert_eq!(graph.known(NodeId::Expr(old)), old_expected);
            previous.push((value, expected));
        }
    });
}

#[test]
fn common_branch_proofs_reuse_a_deep_shared_diamond() {
    with_graph(|mut graph| {
        let mut left = graph.intern_expr(ExprNode::Number(5)).unwrap();
        let mut right = graph.intern_expr(ExprNode::Number(6)).unwrap();
        for index in 0..100_000 {
            let argument = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            let choice = graph.from_expr(argument, 1).unwrap();
            let next_left = graph
                .intern_expr(ExprNode::Select(choice, left, right))
                .unwrap();
            let next_right = graph
                .intern_expr(ExprNode::Select(choice, right, left))
                .unwrap();
            left = next_left;
            right = next_right;
        }
        let upper = graph.intern_expr(ExprNode::Number(7)).unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Less, left, upper))
            .unwrap();
        assert_eq!(
            graph.truth(required, &Sequence::default()).unwrap(),
            Truth::Proven
        );
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum GuardAssignment {
    Either,
    Chosen,
    Opposite,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct DiamondComparison {
    leaves: [u8; 2],
    relation: Relation,
    guards: [GuardAssignment; 3],
}

#[hegel::test(print_blob = true)]
fn shared_diamond_comparisons_match_all_boolean_assignments(tc: hegel::TestCase) {
    let DiamondComparison {
        leaves,
        relation,
        guards,
    } = tc.draw(hegel::generators::default::<DiamondComparison>());
    let mut outcomes = Vec::new();
    'assignments: for assignment in 0..(1 << guards.len()) {
        let [mut left, mut right] = leaves;
        let guards = guards.iter().enumerate();
        for (index, guard) in guards {
            let choice = (assignment >> index) & 1;
            match (guard, choice) {
                (GuardAssignment::Chosen, 0) | (GuardAssignment::Opposite, 1) => {
                    continue 'assignments;
                }
                _ => {}
            }
            match choice {
                0 => std::mem::swap(&mut left, &mut right),
                _ => {}
            }
        }
        let outcome = match (relation, left.cmp(&right)) {
            (Relation::Less, std::cmp::Ordering::Less)
            | (Relation::LessEqual, std::cmp::Ordering::Less | std::cmp::Ordering::Equal)
            | (Relation::Equal, std::cmp::Ordering::Equal)
            | (Relation::NotEqual, std::cmp::Ordering::Less | std::cmp::Ordering::Greater) => {
                Truth::Proven
            }
            _ => Truth::Refuted,
        };
        outcomes.push(outcome);
    }
    let expected = match outcomes.first() {
        Some(first) if outcomes.iter().all(|outcome| outcome == first) => *first,
        _ => Truth::Unknown(ProofGap::Comparison),
    };
    with_graph(|mut graph| {
        let mut left = graph
            .intern_expr(ExprNode::Number(u128::from(leaves[0])))
            .unwrap();
        let mut right = graph
            .intern_expr(ExprNode::Number(u128::from(leaves[1])))
            .unwrap();
        let mut assumptions = Sequence::default();
        let guards = guards.into_iter().enumerate();
        for (index, guard) in guards {
            let argument = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            let choice = graph.from_expr(argument, 1).unwrap();
            match guard {
                GuardAssignment::Either => {}
                GuardAssignment::Chosen => {
                    assumptions = graph.condition_sequences.push(assumptions, choice).unwrap()
                }
                GuardAssignment::Opposite => {
                    let negated = graph.negate(choice).unwrap();
                    assumptions = graph
                        .condition_sequences
                        .push(assumptions, negated)
                        .unwrap();
                }
            }
            let next_left = graph
                .intern_expr(ExprNode::Select(choice, left, right))
                .unwrap();
            let next_right = graph
                .intern_expr(ExprNode::Select(choice, right, left))
                .unwrap();
            left = next_left;
            right = next_right;
        }
        let required = graph
            .intern_condition(ConditionNode::Compare(relation.into(), left, right))
            .unwrap();
        assert_eq!(graph.truth(required, &assumptions).unwrap(), expected);
    });
}

#[test]
fn unresolved_common_context_proofs_keep_correlated_branch_refinement() {
    with_graph(|mut graph| {
        let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let choice = graph.from_expr(argument, 1).unwrap();
        let opposite = graph.negate(choice).unwrap();
        let yes = graph.intern_expr(ExprNode::Test(choice)).unwrap();
        let no = graph.intern_expr(ExprNode::Test(opposite)).unwrap();
        let value = graph
            .intern_expr(ExprNode::Select(choice, yes, no))
            .unwrap();
        let required = graph.from_expr(value, 1).unwrap();
        assert_eq!(
            graph.truth(required, &Sequence::default()).unwrap(),
            Truth::Proven
        );
    });
}

#[hegel::test(print_blob = true)]
fn unknown_guards_are_not_evidence_that_a_call_cannot_return(tc: hegel::TestCase) {
    let arguments = tc.draw(hegel::generators::default::<Vec<u128>>());
    with_graph(|mut graph| {
        let arguments = arguments
            .into_iter()
            .map(|value| graph.intern_expr(ExprNode::Number(value)).unwrap())
            .collect::<Vec<_>>();
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let second = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let returned =
            intern_returned(&mut graph, TargetNode::Indirect(first), arguments.clone()).unwrap();
        let other = intern_returned(&mut graph, TargetNode::Indirect(second), arguments).unwrap();
        let unknown = graph.intern_condition(ConditionNode::Unknown).unwrap();
        assert_eq!(
            truth(&mut graph, returned, vec![unknown]).unwrap(),
            Truth::Unknown(ProofGap::Return)
        );
        assert_eq!(
            truth(&mut graph, returned, vec![unknown, other]).unwrap(),
            Truth::Unknown(ProofGap::Return)
        );
        assert_eq!(
            truth(&mut graph, returned, vec![unknown, returned]).unwrap(),
            Truth::Proven
        );
    });
}

#[hegel::test(print_blob = true)]
fn composite_assumptions_are_used_before_reexpanding_their_branches(tc: hegel::TestCase) {
    let choices = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_graph(|mut graph| {
        let input = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let initial = graph.from_expr(input, 1).unwrap();
        let low = graph.intern_expr(ExprNode::Number(5)).unwrap();
        let high = graph.intern_expr(ExprNode::Number(6)).unwrap();
        let mut value = graph
            .intern_expr(ExprNode::Select(initial, low, high))
            .unwrap();
        for choice in choices {
            let argument = graph
                .intern_expr(ExprNode::Argument(usize::from(choice) + 1))
                .unwrap();
            let condition = graph.from_expr(argument, 1).unwrap();
            value = graph
                .intern_expr(ExprNode::Select(condition, value, high))
                .unwrap();
        }
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Less, value, high))
            .unwrap();
        let opposite = graph.negate(condition).unwrap();
        assert_eq!(
            truth(&mut graph, condition, vec![condition]).unwrap(),
            Truth::Proven
        );
        assert_eq!(
            truth(&mut graph, condition, vec![opposite]).unwrap(),
            Truth::Refuted
        );
        let impossible = graph
            .intern_condition(ConditionNode::Compare(Order::Less, high, low))
            .unwrap();
        assert_eq!(
            truth(&mut graph, impossible, vec![impossible]).unwrap(),
            Truth::Refuted
        );
    });
}

#[test]
fn unknown_shared_branches_keep_their_result_without_evaluating_every_path() {
    with_graph(|mut graph| {
        let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let choice = graph.from_expr(argument, 1).unwrap();
        let mut left = graph.intern_expr(ExprNode::Unknown).unwrap();
        let mut right = graph.intern_expr(ExprNode::Number(1)).unwrap();
        for _ in 0..100_000 {
            let next_left = graph
                .intern_expr(ExprNode::Select(choice, left, right))
                .unwrap();
            let next_right = graph
                .intern_expr(ExprNode::Select(choice, right, left))
                .unwrap();
            left = next_left;
            right = next_right;
        }
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, left, zero))
            .unwrap();
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
    });
}

fn unresolved_return_chain(arguments: impl IntoIterator<Item = u128>) {
    with_graph(|mut graph| {
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let mut value = one;
        let mut expected = Truth::Proven;
        let arguments = arguments.into_iter().enumerate();
        for (index, argument) in arguments {
            let target = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            let argument = graph.intern_expr(ExprNode::Number(argument)).unwrap();
            let returned =
                intern_returned(&mut graph, TargetNode::Indirect(target), vec![argument]).unwrap();
            value = graph
                .intern_expr(ExprNode::Select(returned, value, zero))
                .unwrap();
            expected = Truth::Unknown(ProofGap::Comparison);
        }
        let condition = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, value, one))
            .unwrap();
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            expected
        );
        assert_eq!(
            graph.truth(condition, &Sequence::default()).unwrap(),
            expected
        );
    });
}

#[hegel::test(print_blob = true)]
fn distinct_return_choices_reuse_unconditional_cofactor_results(tc: hegel::TestCase) {
    let arguments = tc.draw(hegel::generators::default::<Vec<u128>>());
    unresolved_return_chain(arguments);
}

#[test]
fn long_distinct_return_chains_do_not_enumerate_boolean_assignments() {
    unresolved_return_chain(0..128);
}

#[hegel::test(print_blob = true)]
fn returned_facts_remain_available_through_nested_boolean_expressions(tc: hegel::TestCase) {
    let arguments = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_graph(|mut graph| {
        let target = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let returned =
            intern_returned(&mut graph, TargetNode::Indirect(target), Vec::new()).unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let mut value = graph.intern_expr(ExprNode::Test(returned)).unwrap();
        let mut guards: Sequence<_> = graph.condition_sequences.from_iter([returned]).unwrap();
        let choices = arguments.iter().enumerate();
        for (index, argument) in choices {
            let input = graph.intern_expr(ExprNode::Argument(index + 1)).unwrap();
            let constant = graph
                .intern_expr(ExprNode::Number(u128::from(*argument)))
                .unwrap();
            let choice = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, input, constant))
                .unwrap();
            value = graph
                .intern_expr(ExprNode::Select(choice, value, zero))
                .unwrap();
            let comparison = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, value, one))
                .unwrap();
            value = graph.intern_expr(ExprNode::Test(comparison)).unwrap();
            guards = graph.condition_sequences.push(guards, choice).unwrap();
        }
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, value, one))
            .unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
        let len = graph.condition_sequences.len(guards);
        let tail = graph
            .condition_sequences
            .slice(guards, 1..len)
            .unwrap()
            .unwrap();
        let missing = graph.truth(required, &tail).unwrap();
        assert_eq!(missing, Truth::Unknown(ProofGap::Comparison));
        let other_target = graph
            .intern_expr(ExprNode::Argument(arguments.len() + 1))
            .unwrap();
        let other_return =
            intern_returned(&mut graph, TargetNode::Indirect(other_target), Vec::new()).unwrap();
        let mut prefixed: Sequence<_> =
            graph.condition_sequences.from_iter([other_return]).unwrap();
        prefixed = graph.condition_sequences.append(prefixed, guards).unwrap();
        guards = prefixed;
        guards = graph
            .condition_sequences
            .push(guards, other_return)
            .unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
    });
}

#[hegel::test(print_blob = true)]
fn returned_context_projection_keeps_transitive_comparison_guards(tc: hegel::TestCase) {
    let noise = tc.draw(hegel::generators::default::<Vec<u128>>());
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let middle = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let last = graph.intern_expr(ExprNode::Argument(2)).unwrap();
        let first_edge = graph
            .intern_condition(ConditionNode::Compare(Order::Less, first, middle))
            .unwrap();
        let second_edge = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, middle, last))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Less, first, last))
            .unwrap();
        let mut guards: Sequence<_> = graph.condition_sequences.from_iter([first_edge]).unwrap();
        for argument in noise {
            let argument = graph.intern_expr(ExprNode::Number(argument)).unwrap();
            let guard =
                intern_returned(&mut graph, TargetNode::Indirect(middle), vec![argument]).unwrap();
            guards = graph.condition_sequences.push(guards, guard).unwrap();
        }
        guards = graph.condition_sequences.push(guards, second_edge).unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
        let absent = truth(&mut graph, required, vec![first_edge]).unwrap();
        assert_eq!(absent, Truth::Unknown(ProofGap::Comparison));
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
    });
}

#[hegel::test(print_blob = true)]
fn indirect_return_targets_retain_nested_predicate_identity(tc: hegel::TestCase) {
    let argument = tc.draw(hegel::generators::integers::<u128>());
    with_graph(|mut graph| {
        let input = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let argument = graph.intern_expr(ExprNode::Number(argument)).unwrap();
        let inner =
            intern_returned(&mut graph, TargetNode::Indirect(input), vec![argument]).unwrap();
        let target = graph.intern_expr(ExprNode::Test(inner)).unwrap();
        let outer =
            intern_returned(&mut graph, TargetNode::Indirect(target), vec![argument]).unwrap();
        let value = graph.intern_expr(ExprNode::Test(outer)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, value, one))
            .unwrap();
        assert_eq!(
            truth(&mut graph, required, vec![inner, outer]).unwrap(),
            Truth::Proven
        );
        assert_eq!(
            truth(&mut graph, required, vec![inner]).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum BooleanAssumption {
    Set,
    Clear,
    NotSet,
    NotClear,
}

#[hegel::test(print_blob = true)]
fn isolated_boolean_guard_values_preserve_other_witness_order(tc: hegel::TestCase) {
    let assumptions = tc.draw(hegel::generators::default::<Vec<BooleanAssumption>>());
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let first = graph
            .intern_condition(ConditionNode::Variant(value, 0))
            .unwrap();
        let second = graph
            .intern_condition(ConditionNode::Variant(value, 1))
            .unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let mut guards = Sequence::default();
        let assumptions = assumptions.into_iter().enumerate();
        for (index, assumption) in assumptions {
            let input = graph.intern_expr(ExprNode::Argument(index + 1)).unwrap();
            let predicate = graph.from_expr(input, 1).unwrap();
            let composite = graph.intern_expr(ExprNode::Test(predicate)).unwrap();
            let (order, constant) = match assumption {
                BooleanAssumption::Set => (Order::Equal, one),
                BooleanAssumption::Clear => (Order::Equal, zero),
                BooleanAssumption::NotSet => (Order::NotEqual, one),
                BooleanAssumption::NotClear => (Order::NotEqual, zero),
            };
            let guard = graph
                .intern_condition(ConditionNode::Compare(order, composite, constant))
                .unwrap();
            guards = graph.condition_sequences.push(guards, guard).unwrap();
        }
        assert_eq!(
            graph.truth(first, &guards).unwrap(),
            Truth::Unknown(ProofGap::Variant)
        );
        let mut prefixed: Sequence<_> = graph.condition_sequences.from_iter([first]).unwrap();
        prefixed = graph.condition_sequences.append(prefixed, guards).unwrap();
        guards = prefixed;
        guards = graph.condition_sequences.push(guards, second).unwrap();
        assert_eq!(graph.truth(first, &guards).unwrap(), Truth::Proven);
        let reversed: Vec<_> = graph
            .condition_sequences
            .iter(guards)
            .rev()
            .copied()
            .collect();
        guards = graph.condition_sequences.from_iter(reversed).unwrap();
        assert_eq!(graph.truth(first, &guards).unwrap(), Truth::Refuted);
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum EqualityOrder {
    CompositeFirst,
    LiteralFirst,
}

#[hegel::test(print_blob = true)]
fn composite_equalities_shared_with_other_guards_retain_their_edges(tc: hegel::TestCase) {
    let order = tc.draw(hegel::generators::default::<EqualityOrder>());
    with_graph(|mut graph| {
        let destination = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let input = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let choice = graph.from_expr(input, 1).unwrap();
        let composite = graph.intern_expr(ExprNode::Test(choice)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let (left, right) = match order {
            EqualityOrder::CompositeFirst => (composite, one),
            EqualityOrder::LiteralFirst => (one, composite),
        };
        let equality = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, left, right))
            .unwrap();
        let bridge = graph
            .intern_condition(ConditionNode::Compare(
                Order::LessEqual,
                composite,
                destination,
            ))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, one, destination))
            .unwrap();
        assert_eq!(
            truth(&mut graph, required, vec![equality, bridge]).unwrap(),
            Truth::Proven
        );
        assert_eq!(
            truth(&mut graph, required, vec![bridge]).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
        assert_eq!(
            truth(&mut graph, required, vec![bridge, equality]).unwrap(),
            Truth::Proven
        );
        let opposite = graph.negate(equality).unwrap();
        assert_eq!(
            truth(&mut graph, equality, vec![equality, opposite]).unwrap(),
            Truth::Proven
        );
        assert_eq!(
            truth(&mut graph, equality, vec![opposite, equality]).unwrap(),
            Truth::Proven
        );
    });
}

#[test]
fn distinct_composite_boolean_choices_share_queries_for_unrelated_suffixes() {
    with_graph(|mut graph| {
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let mut value = one;
        for index in 0..128 {
            let input = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            let predicate = graph.from_expr(input, 1).unwrap();
            let boolean = graph.intern_expr(ExprNode::Test(predicate)).unwrap();
            let choice = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, boolean, one))
                .unwrap();
            value = graph
                .intern_expr(ExprNode::Select(choice, value, zero))
                .unwrap();
        }
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, value, one))
            .unwrap();
        assert_eq!(
            graph.truth(required, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
        assert_eq!(
            graph.truth(required, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
    });
}

#[hegel::test(print_blob = true)]
fn unusable_nested_facts_do_not_establish_identity_or_hide_usable_facts(tc: hegel::TestCase) {
    let values = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_graph(|mut graph| {
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let subject = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let fact = graph
            .intern_condition(ConditionNode::Compare(Order::Less, zero, subject))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, one, subject))
            .unwrap();
        let mut nested = unknown;
        let mut guards = Sequence::default();
        let values = values.into_iter().enumerate();
        for (index, value) in values {
            let input = graph.intern_expr(ExprNode::Argument(index + 1)).unwrap();
            let value = graph
                .intern_expr(ExprNode::Number(u128::from(value)))
                .unwrap();
            let choice = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, input, value))
                .unwrap();
            nested = graph
                .intern_expr(ExprNode::Select(choice, nested, value))
                .unwrap();
            let assumption = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, nested, value))
                .unwrap();
            match truth(&mut graph, assumption, vec![assumption]).unwrap() {
                Truth::Unknown(_) => {}
                truth => panic!("untracked nested assumption established {truth:?}"),
            }
            guards = graph.condition_sequences.push(guards, assumption).unwrap();
        }
        let identity = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, unknown, unknown))
            .unwrap();
        assert_eq!(
            graph.truth(identity, &guards).unwrap(),
            Truth::Unknown(ProofGap::Value)
        );
        guards = graph.condition_sequences.push(guards, fact).unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
        let reversed: Vec<_> = graph
            .condition_sequences
            .iter(guards)
            .rev()
            .copied()
            .collect();
        guards = graph.condition_sequences.from_iter(reversed).unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
        assert_eq!(
            graph.truth(identity, &guards).unwrap(),
            Truth::Unknown(ProofGap::Value)
        );
    });
}

#[test]
fn distinct_untrackable_choices_do_not_create_distinct_evidence_contexts() {
    with_graph(|mut graph| {
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let mut value = unknown;
        for index in 0..10_000 {
            let marker = graph.intern_expr(ExprNode::Number(index)).unwrap();
            let choice = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, unknown, marker))
                .unwrap();
            value = graph
                .intern_expr(ExprNode::Select(choice, value, one))
                .unwrap();
        }
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, value, zero))
            .unwrap();
        assert_eq!(
            graph.truth(required, &Sequence::default()).unwrap(),
            Truth::Unknown(ProofGap::Comparison)
        );
    });
}

#[test]
fn parameter_preserves_deeply_shared_binding_independent_aggregates() {
    with_graph(|mut graph| {
        let mut root = intern_function(
            &mut graph,
            Instance {
                def: rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
                args: vec![Generic::Parameter(0)],
                dispatch: Dispatch::Item,
            },
        )
        .unwrap();
        for _ in 0..100_000 {
            root = intern_aggregate(&mut graph, vec![root, root]).unwrap();
        }
        let binding = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let before = graph.expression_count();
        let mut values = Sequence::default();
        assert_eq!(graph.parameter(root, binding, &mut values).unwrap(), root);
        assert_eq!(graph.expression_count(), before);
        assert_eq!(values, Sequence::default());
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ParameterShape {
    Function,
    Scalar,
    TypedFunction,
    TypedScalar,
    Closure,
    Aggregate,
    Variant,
    Alternatives,
    ChoiceFunctions,
    ChoiceMixed,
    EmptyClosure,
    EmptyAggregate,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct ParameterField {
    shape: ParameterShape,
    number: u128,
}

#[hegel::test(print_blob = true)]
fn mixed_parameter_shapes_preserve_bindings_and_function_instances(tc: hegel::TestCase) {
    let fields = tc.draw(hegel::generators::default::<Vec<ParameterField>>());
    with_graph(|mut graph| {
        let def = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        let binding = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let marker = intern_function(
            &mut graph,
            Instance {
                def,
                args: Vec::new(),
                dispatch: Dispatch::Item,
            },
        )
        .unwrap();
        let mut sources = vec![marker];
        let mut expected = vec![marker];
        let fields = fields.into_iter().enumerate();
        for (index, ParameterField { shape, number }) in fields {
            let first = intern_function(
                &mut graph,
                Instance {
                    def,
                    args: vec![Generic::Const {
                        value: number,
                        ty: Type::Bool,
                    }],
                    dispatch: Dispatch::Item,
                },
            )
            .unwrap();
            let second = intern_function(
                &mut graph,
                Instance {
                    def,
                    args: vec![Generic::Const {
                        value: number,
                        ty: Type::Char,
                    }],
                    dispatch: Dispatch::Virtual,
                },
            )
            .unwrap();
            let scalar = graph.intern_expr(ExprNode::Number(number)).unwrap();
            let condition = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, scalar, binding))
                .unwrap();
            let source = match shape {
                ParameterShape::Function => first,
                ParameterShape::Scalar => scalar,
                ParameterShape::TypedFunction => {
                    typed(&mut graph, Type::Parameter(0), first).unwrap()
                }
                ParameterShape::TypedScalar => {
                    typed(&mut graph, Type::Parameter(0), scalar).unwrap()
                }
                ParameterShape::Closure => {
                    intern_closure(&mut graph, def, vec![first, scalar]).unwrap()
                }
                ParameterShape::Aggregate => {
                    intern_aggregate(&mut graph, vec![first, scalar]).unwrap()
                }
                ParameterShape::Variant => {
                    intern_variant(&mut graph, def, 0, vec![first, scalar]).unwrap()
                }
                ParameterShape::Alternatives => graph.alternatives([first, scalar]).unwrap(),
                ParameterShape::ChoiceFunctions => graph
                    .intern_expr(ExprNode::Select(condition, first, second))
                    .unwrap(),
                ParameterShape::ChoiceMixed => graph
                    .intern_expr(ExprNode::Select(condition, first, scalar))
                    .unwrap(),
                ParameterShape::EmptyClosure => {
                    intern_closure(&mut graph, def, Vec::new()).unwrap()
                }
                ParameterShape::EmptyAggregate => intern_aggregate(&mut graph, Vec::new()).unwrap(),
            };
            sources.push(intern_aggregate(&mut graph, vec![marker, source, source]).unwrap());
            let group_binding = graph
                .intern_expr(ExprNode::Field(binding, index + 1))
                .unwrap();
            let mut group = vec![marker];
            for field in 1..=2 {
                let field_binding = graph
                    .intern_expr(ExprNode::Field(group_binding, field))
                    .unwrap();
                let value = match shape {
                    ParameterShape::Function
                    | ParameterShape::TypedFunction
                    | ParameterShape::EmptyClosure => source,
                    ParameterShape::Scalar | ParameterShape::EmptyAggregate => field_binding,
                    ParameterShape::TypedScalar => {
                        typed(&mut graph, Type::Parameter(0), field_binding).unwrap()
                    }
                    ParameterShape::Closure
                    | ParameterShape::Aggregate
                    | ParameterShape::Variant => {
                        let scalar_binding = graph
                            .intern_expr(ExprNode::Field(field_binding, 1))
                            .unwrap();
                        let fields = graph
                            .expression_sequences
                            .from_iter([first, scalar_binding])
                            .unwrap();
                        let node = match shape {
                            ParameterShape::Closure => ExprNode::Closure(def, fields),
                            ParameterShape::Aggregate => ExprNode::Aggregate(fields),
                            ParameterShape::Variant => ExprNode::Variant(def, 0, fields),
                            _ => unreachable!("aggregate shape"),
                        };
                        graph.intern_expr(node).unwrap()
                    }
                    ParameterShape::Alternatives => {
                        graph.alternatives([first, field_binding]).unwrap()
                    }
                    ParameterShape::ChoiceFunctions | ParameterShape::ChoiceMixed => {
                        let captured = graph.intern_expr(ExprNode::Test(condition)).unwrap();
                        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
                        let condition = graph
                            .intern_condition(ConditionNode::Compare(Order::Equal, captured, one))
                            .unwrap();
                        let otherwise = match shape {
                            ParameterShape::ChoiceFunctions => second,
                            ParameterShape::ChoiceMixed => field_binding,
                            _ => unreachable!("select shape"),
                        };
                        graph
                            .intern_expr(ExprNode::Select(condition, first, otherwise))
                            .unwrap()
                    }
                };
                group.push(value);
            }
            expected.push(intern_aggregate(&mut graph, group).unwrap());
        }
        let source = intern_aggregate(&mut graph, sources).unwrap();
        let expected = intern_aggregate(&mut graph, expected).unwrap();
        let mut values: Sequence<_> = graph.expression_sequences.from_iter([binding]).unwrap();
        let parameter = graph.parameter(source, binding, &mut values).unwrap();
        let generic = graph
            .values
            .intern_generic(&Generic::Type(Type::Parameter(0)))
            .unwrap();
        let scope = Invocation {
            relocation: Relocation::Preserve,
            generics: graph
                .values
                .intern_list::<shapelint_driver::values::GenericsId<'_>>([generic])
                .unwrap(),
        };
        let actual = graph.substitute_expr(parameter, &values, &scope).unwrap();
        assert_eq!(actual, expected);
    });
}

#[test]
fn shared_parameter_selectors_capture_once_per_call_at_the_current_argument_offset() {
    with_graph(|mut graph| {
        let def = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        let first = intern_function(
            &mut graph,
            Instance {
                def,
                args: vec![Generic::Type(Type::Bool)],
                dispatch: Dispatch::Item,
            },
        )
        .unwrap();
        let second = intern_function(
            &mut graph,
            Instance {
                def,
                args: vec![Generic::Type(Type::Char)],
                dispatch: Dispatch::Item,
            },
        )
        .unwrap();
        let binding = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let condition = graph.from_expr(binding, 1).unwrap();
        let choice = graph
            .intern_expr(ExprNode::Select(condition, first, second))
            .unwrap();
        let mut root = choice;
        for _ in 0..100_000 {
            root = intern_aggregate(&mut graph, vec![root, root]).unwrap();
        }
        let captured = graph.intern_expr(ExprNode::Test(condition)).unwrap();
        let mut first_values = Sequence::default();
        let first_parameter = graph.parameter(root, binding, &mut first_values).unwrap();
        assert_eq!(first_parameter, root);
        assert_eq!(
            graph
                .expression_sequences
                .iter(first_values)
                .copied()
                .collect::<Vec<_>>(),
            vec![captured]
        );

        let mut second_values: Sequence<_> =
            graph.expression_sequences.from_iter([binding]).unwrap();
        let before = graph.expression_count();
        let second_parameter = graph.parameter(root, binding, &mut second_values).unwrap();
        assert_ne!(second_parameter, first_parameter);
        assert_eq!(
            graph
                .expression_sequences
                .iter(second_values)
                .copied()
                .collect::<Vec<_>>(),
            vec![binding, captured]
        );
        let after = graph.expression_count();
        // One replacement per aggregate, its select, and the new selector argument.
        assert_eq!(after - before, 100_002);
        let mut expected = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let selector = graph.from_expr(expected, 1).unwrap();
        expected = graph
            .intern_expr(ExprNode::Select(selector, first, second))
            .unwrap();
        for _ in 0..100_000 {
            expected = intern_aggregate(&mut graph, vec![expected, expected]).unwrap();
        }
        assert_eq!(second_parameter, expected);
    });
}

#[hegel::test(print_blob = true)]
fn shared_expression_tails_keep_return_guards_distinct(tc: hegel::TestCase) {
    let depth = tc.draw(hegel::generators::default::<u8>());
    with_graph(|mut graph| {
        let target = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let inner = intern_returned(&mut graph, TargetNode::Indirect(target), vec![]).unwrap();
        let other = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let unrelated = intern_returned(&mut graph, TargetNode::Indirect(other), vec![]).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let mut tail = inner;
        for _ in 0..depth {
            let tested = graph.intern_expr(ExprNode::Test(tail)).unwrap();
            tail = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, tested, one))
                .unwrap();
        }
        for width in 0..4 {
            let value = graph.intern_expr(ExprNode::Argument(width + 2)).unwrap();
            let guard = intern_returned(&mut graph, TargetNode::Indirect(value), vec![]).unwrap();
            assert_eq!(
                truth(&mut graph, tail, vec![unrelated, guard]).unwrap(),
                match depth {
                    0 => Truth::Unknown(ProofGap::Return),
                    _ => Truth::Unknown(ProofGap::Comparison),
                }
            );
            assert_eq!(
                truth(&mut graph, tail, vec![inner, guard]).unwrap(),
                Truth::Proven
            );
            assert_eq!(
                truth(&mut graph, tail, vec![unrelated, inner, guard]).unwrap(),
                Truth::Proven
            );
        }
    });
}

#[hegel::test(print_blob = true)]
fn graph_interning_preserves_expression_and_condition_structure(tc: hegel::TestCase) {
    let (left, right) = tc.draw(hegel::generators::default::<(u64, u64)>());
    with_graph(|mut graph| {
        let a = graph
            .intern_expr(ExprNode::Number(u128::from(left)))
            .unwrap();
        let b = graph
            .intern_expr(ExprNode::Number(u128::from(right)))
            .unwrap();
        let ab = intern_aggregate(&mut graph, vec![a, b]).unwrap();
        let ba = intern_aggregate(&mut graph, vec![b, a]).unwrap();
        let repeat = intern_aggregate(&mut graph, vec![a, b]).unwrap();
        assert_eq!(ab, repeat);
        assert_eq!(ab == ba, left == right);
        let field = graph.intern_expr(ExprNode::Field(ab, 0)).unwrap();
        let other_field = graph.intern_expr(ExprNode::Field(ab, 1)).unwrap();
        assert_ne!(field, other_field);
        let first = intern_returned(&mut graph, TargetNode::Indirect(field), vec![a, b]).unwrap();
        let repeat = intern_returned(&mut graph, TargetNode::Indirect(field), vec![a, b]).unwrap();
        let other =
            intern_returned(&mut graph, TargetNode::Indirect(other_field), vec![a, b]).unwrap();
        assert_eq!(first, repeat);
        assert_ne!(first, other);
        let call = intern_call(&mut graph, TargetNode::Indirect(field), vec![a, b], None).unwrap();
        let other_call = intern_call(
            &mut graph,
            TargetNode::Indirect(other_field),
            vec![a, b],
            None,
        )
        .unwrap();
        assert_ne!(call, other_call);
    });
}

#[hegel::test(print_blob = true)]
fn sequence_substitution_matches_elementwise_oracle_across_contexts(tc: hegel::TestCase) {
    let layout = tc.draw(hegel::generators::default::<Vec<bool>>());
    with_graph(|mut graph| {
        let parameter = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let unchanged = graph.intern_expr(ExprNode::Number(7)).unwrap();
        let first = graph.intern_expr(ExprNode::Number(11)).unwrap();
        let second = graph.intern_expr(ExprNode::Number(13)).unwrap();
        let original: Vec<_> = layout
            .iter()
            .map(|item| if *item { parameter } else { unchanged })
            .collect();
        let sequence: Sequence<_> = graph
            .expression_sequences
            .from_iter(original.iter().copied())
            .unwrap();
        let mut rebuilt = Sequence::default();
        for value in &original {
            rebuilt = graph.expression_sequences.push(rebuilt, *value).unwrap();
        }
        let first_args: Sequence<_> = graph.expression_sequences.from_iter([first]).unwrap();
        let second_args: Sequence<_> = graph.expression_sequences.from_iter([second]).unwrap();
        let expected_first: Vec<_> = layout
            .iter()
            .map(|item| if *item { first } else { unchanged })
            .collect();
        let expected_second: Vec<_> = layout
            .iter()
            .map(|item| if *item { second } else { unchanged })
            .collect();
        let mapped = graph
            .substitute_arguments(&sequence, &first_args, &Invocation::LOCAL)
            .unwrap();
        assert_eq!(
            graph
                .expression_sequences
                .iter(mapped)
                .copied()
                .collect::<Vec<_>>(),
            expected_first
        );
        let mapped = graph
            .substitute_arguments(&rebuilt, &second_args, &Invocation::LOCAL)
            .unwrap();
        assert_eq!(
            graph
                .expression_sequences
                .iter(mapped)
                .copied()
                .collect::<Vec<_>>(),
            expected_second
        );
        let mapped = graph
            .substitute_arguments(&rebuilt, &first_args, &Invocation::LOCAL)
            .unwrap();
        assert_eq!(
            graph
                .expression_sequences
                .iter(mapped)
                .copied()
                .collect::<Vec<_>>(),
            expected_first
        );
        let identity: Sequence<_> = graph.expression_sequences.from_iter([parameter]).unwrap();
        let mapped = graph
            .substitute_arguments(&sequence, &identity, &Invocation::LOCAL)
            .unwrap();
        assert_eq!(
            graph
                .expression_sequences
                .iter(mapped)
                .copied()
                .collect::<Vec<_>>(),
            original
        );
    });
}

#[hegel::test]
fn joining_shared_aggregate_fields_preserves_each_pair(tc: hegel::TestCase) {
    let tail = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_graph(|mut graph| {
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let mut numbers = vec![0, 1, 0, 7];
        numbers.extend(tail);
        let left = intern_aggregate(&mut graph, std::iter::repeat_n(zero, numbers.len())).unwrap();
        for _ in 0..2 {
            let mut right = Vec::new();
            let mut expected = Vec::new();
            for &number in &numbers {
                let number = u128::from(number);
                right.push(graph.intern_expr(ExprNode::Number(number)).unwrap());
                expected.push(match number {
                    0 => zero,
                    _ => graph
                        .intern_expr(ExprNode::Range(Interval {
                            lower: 0,
                            upper: number,
                        }))
                        .unwrap(),
                });
            }
            let right = intern_aggregate(&mut graph, right).unwrap();
            let expected = intern_aggregate(&mut graph, expected).unwrap();
            assert_eq!(graph.join(left, right, Join::Hull).unwrap(), expected);
            numbers.rotate_left(1);
        }
    });
}

#[test]
fn failed_parameter_capture_leaves_the_argument_sequence_unchanged() {
    use shapelint_driver::contracts::graph::CapacityError;

    with_graph(|mut graph| {
        let def = rustc_hir::def_id::CRATE_DEF_ID.to_def_id();
        let [yes, no] = [Type::Bool, Type::Char].map(|ty| {
            intern_function(
                &mut graph,
                Instance {
                    def,
                    args: vec![Generic::Type(ty)],
                    dispatch: Dispatch::Item,
                },
            )
            .unwrap()
        });
        let binding = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let tests = [0, 1].map(|index| {
            let argument = graph.intern_expr(ExprNode::Argument(index)).unwrap();
            graph.from_expr(argument, 1).unwrap()
        });
        let choices = tests.map(|test| graph.intern_expr(ExprNode::Select(test, yes, no)).unwrap());
        let root = intern_aggregate(&mut graph, choices).unwrap();
        let mut block = graph.expression_sequences.from_iter([binding]).unwrap();
        let mut prefix = Sequence::EMPTY;
        for _ in 1..usize::BITS {
            block = graph.expression_sequences.append(block, block).unwrap();
            prefix = graph.expression_sequences.append(prefix, block).unwrap();
        }
        assert_eq!(graph.expression_sequences.len(prefix), usize::MAX - 1);
        let mut values = prefix;
        for _ in 0..2 {
            assert_eq!(
                graph.parameter(root, binding, &mut values),
                Err(CapacityError::Sequences)
            );
            assert_eq!(values, prefix);
        }

        let mut shorter = Sequence::EMPTY;
        graph.parameter(root, binding, &mut shorter).unwrap();
        let expected = tests.map(|test| graph.intern_expr(ExprNode::Test(test)).unwrap());
        assert_eq!(
            graph
                .expression_sequences
                .iter(shorter)
                .copied()
                .collect::<Vec<_>>(),
            expected
        );
    });
}
