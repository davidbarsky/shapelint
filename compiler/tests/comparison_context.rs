#![feature(rustc_private)]

use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
use shapelint_driver::contracts::{Order, ProofGap, Truth};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Direction {
    Lower,
    Upper,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Relation {
    Strict,
    Inclusive,
    Equal,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Comparisons {
    bound: u64,
    direction: Direction,
    relation: Relation,
    thresholds: Vec<u64>,
    constants: Vec<u64>,
}

#[hegel::test(print_blob = true)]
fn cached_comparison_context_matches_integer_bound_oracle(tc: hegel::TestCase) {
    let Comparisons {
        bound,
        direction,
        relation,
        thresholds,
        constants,
    } = tc.draw(hegel::generators::default::<Comparisons>());
    let bound = u128::from(bound) + 1;
    let limit = match (direction, relation) {
        (Direction::Lower, Relation::Strict) => bound + 1,
        (Direction::Upper, Relation::Strict) => bound - 1,
        (_, Relation::Inclusive | Relation::Equal) => bound,
    };
    let thresholds: Vec<_> = [0, limit, limit + 1, bound, u128::MAX]
        .into_iter()
        .chain(thresholds.into_iter().map(u128::from))
        .collect();
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let last = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let constant = graph.intern_expr(ExprNode::Number(bound)).unwrap();
        let bridge = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, first, last))
            .unwrap();
        let (left, right) = match direction {
            Direction::Lower => (constant, first),
            Direction::Upper => (last, constant),
        };
        let order = match relation {
            Relation::Strict => Order::Less,
            Relation::Inclusive => Order::LessEqual,
            Relation::Equal => Order::Equal,
        };
        let boundary = graph
            .intern_condition(ConditionNode::Compare(order, left, right))
            .unwrap();
        let mut guards = {
            let values = [bridge, boundary];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        for value in constants {
            let value = u128::from(value);
            let before = graph.intern_expr(ExprNode::Number(value)).unwrap();
            let after = graph.intern_expr(ExprNode::Number(value + 1)).unwrap();
            {
                let value = graph
                    .intern_condition(ConditionNode::Compare(Order::Less, before, after))
                    .unwrap();
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
        }
        for threshold in thresholds {
            let expected = match direction {
                Direction::Lower => match threshold.cmp(&limit) {
                    std::cmp::Ordering::Less | std::cmp::Ordering::Equal => Truth::Proven,
                    std::cmp::Ordering::Greater => Truth::Unknown(ProofGap::Comparison),
                },
                Direction::Upper => match threshold.cmp(&limit) {
                    std::cmp::Ordering::Greater | std::cmp::Ordering::Equal => Truth::Proven,
                    std::cmp::Ordering::Less => Truth::Unknown(ProofGap::Comparison),
                },
            };
            let constant = graph.intern_expr(ExprNode::Number(threshold)).unwrap();
            let (left, right) = match direction {
                Direction::Lower => (constant, last),
                Direction::Upper => (first, constant),
            };
            let required = graph
                .intern_condition(ConditionNode::Compare(Order::LessEqual, left, right))
                .unwrap();
            assert_eq!(
                graph.truth(required, &guards).unwrap(),
                expected,
                "{direction:?}, {relation:?}, bound={bound}, threshold={threshold}"
            );
        }
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Context {
    Weaker,
    Stronger,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Contexts {
    value: u64,
    visits: Vec<Context>,
}

#[hegel::test(print_blob = true)]
fn comparison_caches_keep_guard_contexts_distinct(tc: hegel::TestCase) {
    let Contexts { value, visits } = tc.draw(hegel::generators::default::<Contexts>());
    let value = u128::from(value) + 1;
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let last = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let low = graph.intern_expr(ExprNode::Number(value)).unwrap();
        let high = graph.intern_expr(ExprNode::Number(value + 2)).unwrap();
        let middle = graph.intern_expr(ExprNode::Number(value + 1)).unwrap();
        let bridge = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, first, last))
            .unwrap();
        let weaker = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, low, first))
            .unwrap();
        let stronger = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, high, first))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, middle, last))
            .unwrap();
        let visits = [Context::Weaker, Context::Stronger, Context::Weaker]
            .into_iter()
            .chain(visits);
        for visit in visits {
            let (guard, expected) = match visit {
                Context::Weaker => (weaker, Truth::Unknown(ProofGap::Comparison)),
                Context::Stronger => (stronger, Truth::Proven),
            };
            let guards = graph
                .condition_sequences
                .from_iter([bridge, guard])
                .unwrap();
            assert_eq!(graph.truth(required, &guards).unwrap(), expected);
        }
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum IntegerEdge {
    Zero,
    Maximum,
}

#[hegel::test(print_blob = true)]
fn cached_integer_edges_do_not_wrap_adjacent_constants(tc: hegel::TestCase) {
    let edge = tc.draw(hegel::generators::default::<IntegerEdge>());
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let last = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let bridge = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, first, last))
            .unwrap();
        let (boundary, required) = match edge {
            IntegerEdge::Zero => {
                let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
                let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
                (
                    ConditionNode::Compare(Order::Less, last, zero),
                    ConditionNode::Compare(Order::LessEqual, first, one),
                )
            }
            IntegerEdge::Maximum => {
                let maximum = graph.intern_expr(ExprNode::Number(u128::MAX)).unwrap();
                let previous = graph.intern_expr(ExprNode::Number(u128::MAX - 1)).unwrap();
                (
                    ConditionNode::Compare(Order::Less, maximum, first),
                    ConditionNode::Compare(Order::LessEqual, previous, last),
                )
            }
        };
        let boundary = graph.intern_condition(boundary).unwrap();
        let required = graph.intern_condition(required).unwrap();
        let guards = graph
            .condition_sequences
            .from_iter([bridge, boundary])
            .unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
    });
}

#[hegel::test(print_blob = true)]
fn growing_guard_prefixes_preserve_integer_proofs_through_rotations(tc: hegel::TestCase) {
    let values = tc.draw(hegel::generators::default::<Vec<u64>>());
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let last = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let bridge = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, first, last))
            .unwrap();
        let mut guards = {
            let values = [bridge];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        let mut snapshots = Vec::new();
        let mut greatest = 0;
        for value in (1..=65).chain(values) {
            let value = u128::from(value) + 1;
            greatest = greatest.max(value + 1);
            let number = graph.intern_expr(ExprNode::Number(value)).unwrap();
            let guard = graph
                .intern_condition(ConditionNode::Compare(Order::Less, number, first))
                .unwrap();
            {
                let value = guard;
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
            let bound = graph.intern_expr(ExprNode::Number(greatest)).unwrap();
            let required = graph
                .intern_condition(ConditionNode::Compare(Order::LessEqual, bound, last))
                .unwrap();
            assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
            snapshots.push((guards.clone(), greatest));
        }
        let entries = snapshots.into_iter().rev();
        for (guards, greatest) in entries {
            let above = graph.intern_expr(ExprNode::Number(greatest + 1)).unwrap();
            let required = graph
                .intern_condition(ConditionNode::Compare(Order::LessEqual, above, last))
                .unwrap();
            assert_eq!(
                graph.truth(required, &guards).unwrap(),
                Truth::Unknown(ProofGap::Comparison)
            );
            let below = graph.intern_expr(ExprNode::Number(greatest - 1)).unwrap();
            let required = graph
                .intern_condition(ConditionNode::Compare(Order::Less, below, last))
                .unwrap();
            assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
        }
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum VariantOrder {
    FirstZero,
    FirstOne,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct VariantContext {
    order: VariantOrder,
    padding: Vec<u8>,
}

#[hegel::test(print_blob = true)]
fn first_positive_variant_guard_wins_in_conflicting_contexts(tc: hegel::TestCase) {
    let VariantContext { order, padding } = tc.draw(hegel::generators::default::<VariantContext>());
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let zero = graph
            .intern_condition(ConditionNode::Variant(value, 0))
            .unwrap();
        let one = graph
            .intern_condition(ConditionNode::Variant(value, 1))
            .unwrap();
        let excluded = graph
            .intern_condition(ConditionNode::NotVariant(value, 0))
            .unwrap();
        let (first, second) = match order {
            VariantOrder::FirstZero => (zero, one),
            VariantOrder::FirstOne => (one, zero),
        };
        let (expected, opposite) = match order {
            VariantOrder::FirstZero => (Truth::Proven, Truth::Refuted),
            VariantOrder::FirstOne => (Truth::Refuted, Truth::Proven),
        };
        let mut guards = {
            let values = [first];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        for index in padding {
            let other = graph
                .intern_expr(ExprNode::Argument(usize::from(index) + 1))
                .unwrap();
            {
                let value = graph
                    .intern_condition(ConditionNode::Variant(other, 0))
                    .unwrap();
                guards = graph.condition_sequences.push(guards, value).unwrap();
            };
        }
        {
            let value = second;
            guards = graph.condition_sequences.push(guards, value).unwrap();
        };
        assert_eq!(graph.truth(zero, &guards).unwrap(), expected);
        assert_eq!(graph.truth(excluded, &guards).unwrap(), opposite);
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum NonzeroOrder {
    Forward,
    Reverse,
}

#[hegel::test(print_blob = true)]
fn indexed_nonzero_guards_preserve_both_operand_orders(tc: hegel::TestCase) {
    let order = tc.draw(hegel::generators::default::<NonzeroOrder>());
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let (left, right) = match order {
            NonzeroOrder::Forward => (value, zero),
            NonzeroOrder::Reverse => (zero, value),
        };
        let nonzero = graph
            .intern_condition(ConditionNode::Compare(Order::NotEqual, left, right))
            .unwrap();
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::LessEqual, one, value))
            .unwrap();
        let guards = {
            let values = [nonzero];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
    });
}

#[test]
fn intrinsic_numeric_edges_connect_guarded_cycles() {
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let last = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let five = graph.intern_expr(ExprNode::Number(5)).unwrap();
        let six = graph.intern_expr(ExprNode::Number(6)).unwrap();
        let seven = graph.intern_expr(ExprNode::Number(7)).unwrap();
        let nine = graph.intern_expr(ExprNode::Number(9)).unwrap();
        let guards = {
            let values = [
                graph
                    .intern_condition(ConditionNode::Compare(Order::LessEqual, first, five))
                    .unwrap(),
                graph
                    .intern_condition(ConditionNode::Compare(Order::LessEqual, nine, first))
                    .unwrap(),
                graph
                    .intern_condition(ConditionNode::Compare(Order::LessEqual, six, last))
                    .unwrap(),
            ];
            graph.condition_sequences.from_iter(values).unwrap()
        };
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Less, seven, last))
            .unwrap();
        assert_eq!(graph.truth(required, &guards).unwrap(), Truth::Proven);
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum EqualityDirection {
    ValueFirst,
    ConstantFirst,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum EqualityCheck {
    Equal,
    NotEqual,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct StrictEquality {
    lower: u64,
    direction: EqualityDirection,
    check: EqualityCheck,
}

#[hegel::test(print_blob = true)]
fn strict_reverse_paths_decide_equality_with_the_original_evidence(tc: hegel::TestCase) {
    let StrictEquality {
        lower,
        direction,
        check,
    } = tc.draw(hegel::generators::default::<StrictEquality>());
    with_graph(|mut graph| {
        let value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let lower = u128::from(lower);
        let low = graph.intern_expr(ExprNode::Number(lower)).unwrap();
        let high = graph.intern_expr(ExprNode::Number(lower + 1)).unwrap();
        let witness = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, value, high))
            .unwrap();
        let (left, right) = match direction {
            EqualityDirection::ValueFirst => (value, low),
            EqualityDirection::ConstantFirst => (low, value),
        };
        let order = match check {
            EqualityCheck::Equal => Order::Equal,
            EqualityCheck::NotEqual => Order::NotEqual,
        };
        let condition = graph
            .intern_condition(ConditionNode::Compare(order, left, right))
            .unwrap();
        let guards = graph.condition_sequences.from_iter([witness]).unwrap();
        let proof = graph.prove(condition, &guards).unwrap();
        let evidence = match (check, proof) {
            (
                EqualityCheck::Equal,
                shapelint_driver::contracts::graph::evidence::Proof::Refuted(evidence),
            )
            | (
                EqualityCheck::NotEqual,
                shapelint_driver::contracts::graph::evidence::Proof::Proven(evidence),
            ) => evidence,
            (_, proof) => panic!("strict inequality must decide the comparison: {proof:?}"),
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
            vec![witness]
        );
    });
}
