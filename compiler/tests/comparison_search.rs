#![feature(rustc_private)]

use shapelint_driver::contracts::graph::evidence::Proof;
use shapelint_driver::contracts::graph::{ConditionId, ConditionNode, ExprNode, Graph, with_graph};
use shapelint_driver::contracts::{Order, Truth};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Value {
    First,
    Second,
    Third,
    Fourth,
    Number(u64),
}

impl<'g> From<Value> for ExprNode<'g> {
    fn from(value: Value) -> Self {
        match value {
            Value::First => Self::Argument(0),
            Value::Second => Self::Argument(1),
            Value::Third => Self::Argument(2),
            Value::Fourth => Self::Argument(3),
            Value::Number(number) => Self::Number(u128::from(number)),
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Relation {
    Strict,
    Inclusive,
    Equal,
    NotEqual,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct Comparison {
    left: Value,
    right: Value,
    relation: Relation,
}

impl Comparison {
    fn intern<'g>(self, graph: &mut Graph<'g>) -> ConditionId<'g> {
        let Self {
            left,
            right,
            relation,
        } = self;
        let left = graph.intern_expr(left.into()).expect("small graph");
        let right = graph.intern_expr(right.into()).expect("small graph");
        let order = match relation {
            Relation::Strict => Order::Less,
            Relation::Inclusive => Order::LessEqual,
            Relation::Equal => Order::Equal,
            Relation::NotEqual => Order::NotEqual,
        };
        graph
            .intern_condition(ConditionNode::Compare(order, left, right))
            .expect("small graph")
    }
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Searches {
    guards: Vec<Comparison>,
    queries: Vec<Comparison>,
}

#[derive(Debug, PartialEq, Eq)]
struct Answer {
    truth: Truth,
    evidence: Vec<usize>,
}

fn answers(guards: &[Comparison], queries: &[Comparison]) -> Vec<Answer> {
    with_graph(|mut graph| {
        let conditions: Vec<_> = guards
            .iter()
            .map(|guard| guard.intern(&mut graph))
            .collect();
        let guards = graph
            .condition_sequences
            .from_iter(conditions.iter().copied())
            .expect("small context");
        queries
            .iter()
            .map(|query| {
                let query = query.intern(&mut graph);
                let proof = graph.prove(query, &guards).expect("small proof");
                let evidence = match proof {
                    Proof::Proven(evidence) | Proof::Refuted(evidence) => {
                        let sequence = graph.evidence_sequence(evidence).expect("small evidence");
                        graph
                            .condition_sequences
                            .iter(sequence)
                            .map(|condition| {
                                conditions
                                    .iter()
                                    .position(|guard| guard == condition)
                                    .expect("evidence identifies an original guard")
                            })
                            .collect()
                    }
                    Proof::Unknown(_) => Vec::new(),
                };
                let answer = Answer {
                    truth: Truth::from(proof),
                    evidence,
                };
                answer
            })
            .collect()
    })
}

#[hegel::test]
fn comparison_query_history_preserves_fresh_answers_and_evidence(tc: hegel::TestCase) {
    let Searches { guards, queries } = tc.draw(hegel::generators::default::<Searches>());
    let cached = answers(&guards, &queries);
    let fresh: Vec<_> = queries
        .iter()
        .flat_map(|query| answers(&guards, std::slice::from_ref(query)))
        .collect();
    assert_eq!(cached, fresh, "guards: {guards:?}; queries: {queries:?}");
}

#[test]
fn dropping_a_long_comparison_witness_uses_bounded_stack() {
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(|| {
            with_graph(|mut graph| {
                let first = graph.intern_expr(ExprNode::Argument(0)).unwrap();
                let mut last = first;
                let mut edges = Vec::new();
                for i in 1..=4096 {
                    let next = graph.intern_expr(ExprNode::Argument(i)).unwrap();
                    edges.push(
                        graph
                            .intern_condition(ConditionNode::Compare(Order::Less, last, next))
                            .unwrap(),
                    );
                    last = next;
                }
                let guards = graph.condition_sequences.from_iter(edges).unwrap();
                let query = graph
                    .intern_condition(ConditionNode::Compare(Order::Less, first, last))
                    .unwrap();
                let Proof::Proven(evidence) = graph.prove(query, &guards).unwrap() else {
                    panic!("every adjacent pair is strictly increasing");
                };
                let evidence = graph.evidence_sequence(evidence).unwrap();
                assert_eq!(graph.condition_sequences.len(evidence), 4096);
            });
        })
        .unwrap()
        .join()
        .unwrap();
}
