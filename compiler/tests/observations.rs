#![feature(rustc_private)]

extern crate rustc_middle;
extern crate rustc_span;

use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, TargetNode, with_graph};
use shapelint_driver::contracts::{Arithmetic, Call, CheckBasis, Order, Summary};

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum SharedStep {
    Double,
    Offset(u8),
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Revisions {
    transient: Vec<Vec<SharedStep>>,
    result: u8,
}

#[hegel::test(print_blob = true)]
fn discarded_observations_keep_shared_values_until_convergence(tc: hegel::TestCase) {
    let Revisions { transient, result } = tc.draw(hegel::generators::default::<Revisions>());
    with_graph(|mut graph| {
        let base = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let target = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let mut summary = Summary::default();
        let mut value = base;
        for revision in transient {
            for step in revision {
                let right = match step {
                    SharedStep::Double => value,
                    SharedStep::Offset(amount) => graph
                        .intern_expr(ExprNode::Number(u128::from(amount)))
                        .unwrap(),
                };
                value = graph
                    .intern_expr(ExprNode::Arithmetic(
                        Arithmetic::Add(rustc_middle::ty::UintTy::U32),
                        value,
                        right,
                    ))
                    .unwrap();
            }
            let guard = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, value, base))
                .unwrap();
            let guards = graph.condition_sequences.from_iter([guard]).unwrap();
            let arguments = graph
                .expression_sequences
                .from_iter([value, value])
                .unwrap();
            summary.calls = vec![Call {
                basis: CheckBasis::ControlFlow(guards),
                target: TargetNode::Indirect(target),
                arguments,
                guards,
                span: rustc_span::DUMMY_SP,
            }];
        }
        let final_value = graph
            .intern_expr(ExprNode::Number(u128::from(result)))
            .unwrap();
        let guard = graph
            .intern_condition(ConditionNode::Compare(
                Order::Equal,
                final_value,
                final_value,
            ))
            .unwrap();
        let guards = graph.condition_sequences.from_iter([guard]).unwrap();
        let arguments = graph
            .expression_sequences
            .from_iter([final_value, final_value])
            .unwrap();
        summary.calls = vec![Call {
            basis: CheckBasis::ControlFlow(guards),
            target: TargetNode::Indirect(target),
            arguments,
            guards,
            span: rustc_span::DUMMY_SP,
        }];
        {
            let summary = graph.freeze(summary).unwrap();
            let summary = graph.summaries[summary];
            let calls: Vec<_> = graph.summaries.calls.iter(summary.calls).copied().collect();
            let [call] = calls.as_slice() else {
                panic!("converged summary must contain only the final call");
            };
            let value = graph
                .intern_expr(ExprNode::Number(u128::from(result)))
                .unwrap();
            let guard = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, value, value))
                .unwrap();
            assert_eq!(
                graph
                    .expression_sequences
                    .iter(call.arguments)
                    .copied()
                    .collect::<Vec<_>>(),
                vec![value; 2]
            );
            assert_eq!(
                graph
                    .condition_sequences
                    .iter(call.guards)
                    .copied()
                    .collect::<Vec<_>>(),
                vec![guard]
            );
            let CheckBasis::ControlFlow(basis) = &call.basis else {
                panic!("captured selection evidence survives freezing");
            };
            assert_eq!(
                graph
                    .condition_sequences
                    .iter(*basis)
                    .copied()
                    .collect::<Vec<_>>(),
                vec![guard]
            );
        }
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Observation {
    Once,
    Shared,
}

#[hegel::test(print_blob = true)]
fn revisited_loop_observations_preserve_guarded_subtraction(tc: hegel::TestCase) {
    let observations = tc.draw(hegel::generators::default::<Vec<Observation>>());
    let mut source = String::from(
        "pub fn run(mut remaining:u8, observe:fn(u8)){while remaining>0{observe(remaining);",
    );
    for observation in observations {
        let statement = match observation {
            Observation::Once => "observe(remaining);",
            Observation::Shared => "let shared=remaining;observe(shared);observe(shared);",
        };
        source.push_str(statement);
    }
    source.push_str("remaining-=1;}}");
    let output = support::analyze(&source, &["--show-analysis-gaps"]).unwrap();
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    assert!(
        !findings
            .iter()
            .any(|finding| finding["rule"] == "invalid-state-use"
                || finding["rule"] == "unproven-precondition"),
        "{source}\n{output}"
    );
}

#[test]
fn captured_repeated_children_remain_one_graph_after_linking() {
    let depth = 100_000;
    with_graph(|mut graph| {
        let mut value = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        for _ in 0..depth {
            let children = graph
                .expression_sequences
                .from_iter([value, value])
                .unwrap();
            value = graph.intern_expr(ExprNode::Aggregate(children)).unwrap();
        }
        let summary = Summary {
            returns: vec![shapelint_driver::contracts::Return {
                value,
                guards: Default::default(),
            }],
            ..Summary::default()
        };
        let summary = graph.freeze(summary).unwrap();
        let summary = graph.summaries[summary];
        assert_eq!(graph.expression_count(), depth + 1);
        let returns: Vec<_> = graph
            .summaries
            .returns
            .iter(summary.returns)
            .copied()
            .collect();
        let [returned] = returns.as_slice() else {
            panic!("one retained return");
        };
        let mut value = returned.value;
        for _ in 0..depth {
            let ExprNode::Aggregate(children) = &graph[value] else {
                panic!("shared aggregate");
            };
            let children: Vec<_> = graph
                .expression_sequences
                .iter(*children)
                .copied()
                .collect();
            let [left, right] = children.as_slice() else {
                panic!("two references to the shared child");
            };
            assert_eq!(left, right);
            value = *left;
        }
        assert_eq!(value, graph.intern_expr(ExprNode::Argument(0)).unwrap());
    });
}

#[hegel::test(print_blob = true)]
fn interprocedural_proofs_keep_caller_guard_contexts_separate(tc: hegel::TestCase) {
    let threshold = tc.draw(hegel::generators::default::<u8>());
    let required = u16::from(threshold) + 1;
    let source = format!(
        "fn consume(value:u16)->u16{{value-{required}}}
fn independent(value:u16)->u16{{value.wrapping_add(1)}}
pub fn guarded(value:u16)->u16{{if value>{threshold}{{consume(value).wrapping_add(independent(value))}}else{{independent(value)}}}}
pub fn unguarded(value:u16)->u16{{consume(value).wrapping_add(independent(value))}}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).unwrap();
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).unwrap())
        .collect();
    let obligations: Vec<_> = findings
        .iter()
        .filter(|finding| finding["rule"] == "unproven-precondition")
        .collect();
    assert_eq!(obligations.len(), 1, "{source}\n{output}");
    assert_eq!(obligations[0]["item"], "unguarded", "{source}\n{output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ControlFlow {
    Call,
    Diamond,
    Loop,
    UnreachableBranch,
    RepeatedGuard,
}

#[hegel::test(print_blob = true)]
fn outgoing_edges_preserve_guards_through_generated_control_flow(tc: hegel::TestCase) {
    let steps = tc.draw(hegel::generators::default::<Vec<ControlFlow>>());
    let mut source =
        String::from("pub fn guarded(value:u8, _branch:bool, observe:fn(u8)){if value>0{");
    for step in steps {
        source.push_str(match step {
            ControlFlow::Call => "observe(value);",
            ControlFlow::Diamond => {
                "if _branch{observe(value);}else{observe(value);observe(value);}"
            }
            ControlFlow::Loop => {
                "{let mut remaining=value;while remaining>0{observe(remaining);remaining-=1;}}"
            }
            ControlFlow::UnreachableBranch => "if value==0{observe(value-1);}",
            ControlFlow::RepeatedGuard => "if value>0{observe(value-1);}",
        });
    }
    source.push_str(
        "observe(value-1);}}pub fn unguarded(value:u8, observe:fn(u8)){observe(value-1);}",
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let obligations: Vec<_> = findings
        .iter()
        .filter(|finding| {
            finding["rule"] == "invalid-state-use"
                || finding["rule"] == "unproven-precondition"
                || finding["rule"] == "analysis-incomplete"
        })
        .collect();
    assert_eq!(obligations.len(), 1, "{source}\n{output}");
    assert_eq!(obligations[0]["item"], "unguarded", "{source}\n{output}");
    assert_eq!(
        obligations[0]["rule"], "unproven-precondition",
        "{source}\n{output}"
    );
}
