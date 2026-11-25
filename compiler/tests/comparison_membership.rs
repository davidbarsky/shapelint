#![feature(rustc_private)]

use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
use shapelint_driver::contracts::{Order, Truth};
use shapelint_driver::sequence::Sequence;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Value {
    Plain,
    Selection,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Guards {
    Positive,
    Negative,
    Conflicting,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Case {
    value: Value,
    guards: Guards,
}

#[hegel::test(print_blob = true)]
fn indexed_membership_preserves_direct_and_branch_precedence(tc: hegel::TestCase) {
    let Case { value, guards } = tc.draw(hegel::generators::default::<Case>());
    with_graph(|mut graph| {
        let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let second = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let last = graph.intern_expr(ExprNode::Argument(2)).unwrap();
        let value = match value {
            Value::Plain => first,
            Value::Selection => {
                let choice = graph
                    .intern_condition(ConditionNode::Variant(last, 0))
                    .unwrap();
                graph
                    .intern_expr(ExprNode::Select(choice, first, second))
                    .unwrap()
            }
        };
        let required = graph
            .intern_condition(ConditionNode::Compare(Order::Less, value, last))
            .unwrap();
        let negated = graph.negate(required).unwrap();
        let (guards, expected): (Sequence<_>, _) = match guards {
            Guards::Positive => (
                graph.condition_sequences.from_iter([required]).unwrap(),
                Truth::Proven,
            ),
            Guards::Negative => (
                graph.condition_sequences.from_iter([negated]).unwrap(),
                Truth::Refuted,
            ),
            Guards::Conflicting => (
                graph
                    .condition_sequences
                    .from_iter([negated, required])
                    .unwrap(),
                Truth::Proven,
            ),
        };
        assert_eq!(graph.truth(required, &guards).unwrap(), expected);
    });
}
