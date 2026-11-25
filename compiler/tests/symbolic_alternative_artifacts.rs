#![feature(rustc_private)]

mod summary_fixture;

use summary_fixture::Fixture;

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
enum Expression {
    Number(u128),
    Alternatives(Option<usize>),
}
#[derive(Serialize, Deserialize)]
enum Choice {
    Value(usize),
    Branch(usize, usize),
}
#[derive(Serialize, Deserialize)]
enum Kind {
    Expression(Expression),
    Choice(Choice),
}
#[derive(Serialize, Deserialize)]
struct Node {
    kind: Kind,
    expressions: Vec<usize>,
    conditions: Vec<usize>,
}
#[derive(Serialize, Deserialize)]
struct Return {
    value: usize,
    guards: Option<usize>,
}

#[test]
fn serialized_choice_prefixes_retain_shared_nodes_and_order() {
    let (fixture, bytes) = Fixture::produce();
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&bytes).expect("producer summary envelope");
    let definition = artifact["summaries"][0][0].clone();
    let mut nodes = Vec::new();
    let mut previous = None;
    let mut returns = Vec::new();
    let count = 128usize;
    for index in 0..count {
        let value = nodes.len();
        nodes.push(Node {
            kind: Kind::Expression(Expression::Number(index as u128)),
            expressions: Vec::new(),
            conditions: Vec::new(),
        });
        let leaf = nodes.len();
        nodes.push(Node {
            kind: Kind::Choice(Choice::Value(value)),
            expressions: Vec::new(),
            conditions: Vec::new(),
        });
        let root = match previous {
            None => leaf,
            Some(previous) => {
                let root = nodes.len();
                nodes.push(Node {
                    kind: Kind::Choice(Choice::Branch(previous, leaf)),
                    expressions: Vec::new(),
                    conditions: Vec::new(),
                });
                root
            }
        };
        previous = Some(root);
        let value = nodes.len();
        nodes.push(Node {
            kind: Kind::Expression(Expression::Alternatives(Some(root))),
            expressions: Vec::new(),
            conditions: Vec::new(),
        });
        returns.push(Return {
            value,
            guards: None,
        });
    }
    artifact["nodes"] = serde_json::to_value(nodes).unwrap();
    artifact["summaries"][0][1]["returns"] = serde_json::to_value(returns).unwrap();
    let output = fixture.import(&artifact);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let exported: serde_json::Value =
        serde_json::from_slice(&fixture.exported()).expect("consumer summary envelope");
    let summary = exported["summaries"]
        .as_array()
        .unwrap()
        .iter()
        .find(|summary| summary[0] == definition)
        .expect("the imported summary is retained");
    let returns: Vec<Return> = serde_json::from_value(summary[1]["returns"].clone()).unwrap();
    assert_eq!(returns.len(), count);
    let mut reached = std::collections::HashSet::new();
    let entries = returns.iter().enumerate();
    for (index, returned) in entries {
        let mut pending = vec![returned.value];
        let mut values = Vec::new();
        while let Some(id) = pending.pop() {
            reached.insert(id);
            let node: Node = serde_json::from_value(exported["nodes"][id].clone()).unwrap();
            assert!(node.expressions.is_empty());
            assert!(node.conditions.is_empty());
            match node.kind {
                Kind::Expression(Expression::Number(value)) => values.push(value),
                Kind::Expression(Expression::Alternatives(Some(root))) => {
                    assert!(root < id);
                    pending.push(root);
                }
                Kind::Expression(Expression::Alternatives(None)) => {
                    panic!("prefix roots are nonempty")
                }
                Kind::Choice(Choice::Value(value)) => {
                    assert!(value < id);
                    pending.push(value);
                }
                Kind::Choice(Choice::Branch(left, right)) => {
                    assert!(left < id && right < id);
                    pending.push(right);
                    pending.push(left);
                }
            }
        }
        assert_eq!(values, (0..=index as u128).collect::<Vec<_>>());
    }
    assert!(
        reached.len() < count * (count + 1) / 2,
        "the wire graph must share overlapping prefixes"
    );
}

#[test]
fn a_choice_reference_cannot_name_an_expression_node() {
    let (fixture, bytes) = Fixture::produce();
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&bytes).expect("producer summary envelope");
    artifact["nodes"] = serde_json::to_value([
        Node {
            kind: Kind::Expression(Expression::Number(1)),
            expressions: Vec::new(),
            conditions: Vec::new(),
        },
        Node {
            kind: Kind::Choice(Choice::Branch(0, 0)),
            expressions: Vec::new(),
            conditions: Vec::new(),
        },
    ])
    .unwrap();
    let output = fixture.import(&artifact);
    assert!(!output.status.success());
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("summary choice reference names another node kind")
    );
}
