#![feature(rustc_private)]

mod summary_fixture;

use summary_fixture::Fixture;

use serde::{Deserialize, Serialize};

#[derive(Serialize, Deserialize)]
enum SequenceNode {
    Leaf(usize),
    Branch(usize, usize),
}

#[derive(Serialize, Deserialize)]
struct Return {
    value: usize,
    guards: Option<usize>,
}

#[test]
fn sequence_import_rejects_a_forward_child_before_constructing_a_sequence() {
    let (fixture, bytes) = Fixture::produce();
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&bytes).expect("producer summary envelope");
    artifact["guard_sequences"] = serde_json::to_value([SequenceNode::Branch(0, 0)]).unwrap();
    let consumed = fixture.import(&artifact);
    assert!(!consumed.status.success());
    assert!(
        String::from_utf8_lossy(&consumed.stderr)
            .contains("sequence child 0 must precede its parent 0")
    );
}

#[test]
fn sequence_import_rejects_a_root_outside_its_typed_table() {
    let (fixture, bytes) = Fixture::produce();
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&bytes).expect("producer summary envelope");
    artifact["guard_sequences"] = serde_json::to_value(Vec::<SequenceNode>::new()).unwrap();
    let returned: Return =
        serde_json::from_value(artifact["summaries"][0][1]["returns"][0].clone()).unwrap();
    artifact["summaries"][0][1]["returns"] = serde_json::to_value([Return {
        guards: Some(0),
        ..returned
    }])
    .unwrap();
    let consumed = fixture.import(&artifact);
    assert!(!consumed.status.success());
    assert!(
        String::from_utf8_lossy(&consumed.stderr)
            .contains("sequence root 0 is outside its table of 0 nodes")
    );
}

#[test]
fn growing_guard_prefixes_export_shared_nodes_and_preserve_every_occurrence() {
    #[derive(Serialize)]
    enum Predicate {
        Variant(usize),
    }
    #[derive(Serialize)]
    enum Expression {
        Argument(usize),
    }
    #[derive(Serialize)]
    enum Kind {
        Expression(Expression),
        Predicate(Predicate),
    }
    #[derive(Serialize)]
    struct Node {
        kind: Kind,
        expressions: Vec<usize>,
        conditions: Vec<usize>,
    }

    let (fixture, bytes) = Fixture::produce();
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&bytes).expect("producer summary envelope");
    let definition = artifact["summaries"][0][0].clone();
    let returned: Return =
        serde_json::from_value(artifact["summaries"][0][1]["returns"][0].clone()).unwrap();
    let nodes = artifact["nodes"].as_array_mut().expect("node table");
    let mut sequences = Vec::new();
    let mut returns = Vec::new();
    let mut previous = None;
    for index in 0..128 {
        let argument = nodes.len();
        nodes.push(
            serde_json::to_value(Node {
                kind: Kind::Expression(Expression::Argument(index / 2)),
                expressions: Vec::new(),
                conditions: Vec::new(),
            })
            .unwrap(),
        );
        let condition = nodes.len();
        nodes.push(
            serde_json::to_value(Node {
                kind: Kind::Predicate(Predicate::Variant(0)),
                expressions: vec![argument],
                conditions: Vec::new(),
            })
            .unwrap(),
        );
        let leaf = sequences.len();
        sequences.push(SequenceNode::Leaf(condition));
        let root = match previous {
            None => leaf,
            Some(previous) => {
                let root = sequences.len();
                sequences.push(SequenceNode::Branch(previous, leaf));
                root
            }
        };
        previous = Some(root);
        returns.push(Return {
            value: returned.value,
            guards: Some(root),
        });
    }
    let flattened_length: usize = (1..=returns.len()).sum();
    artifact["guard_sequences"] = serde_json::to_value(sequences).unwrap();
    artifact["summaries"][0][1]["returns"] = serde_json::to_value(&returns).unwrap();
    let consumed = fixture.import(&artifact);
    assert!(
        consumed.status.success(),
        "{}",
        String::from_utf8_lossy(&consumed.stderr)
    );
    let exported: serde_json::Value =
        serde_json::from_slice(&fixture.exported()).expect("consumer summary envelope");
    assert_eq!(exported["format"], "shapelint-summary-8");
    let sequences: Vec<SequenceNode> =
        serde_json::from_value(exported["guard_sequences"].clone()).unwrap();
    assert!(
        sequences.len() < flattened_length,
        "growing prefixes must share exported nodes"
    );
    let mut lengths = Vec::new();
    let entries = sequences.iter().enumerate();
    for (index, node) in entries {
        let length = match node {
            SequenceNode::Leaf(_) => 1usize,
            SequenceNode::Branch(left, right) => {
                assert!(
                    *left < index && *right < index,
                    "sequence children must precede parents"
                );
                lengths[*left] + lengths[*right]
            }
        };
        lengths.push(length);
    }
    let imported = exported["summaries"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry[0] == definition)
        .expect("imported summary");
    let returned: Vec<Return> = serde_json::from_value(imported[1]["returns"].clone()).unwrap();
    assert_eq!(returned.len(), returns.len());
    let entries = returned.into_iter().enumerate();
    for (index, returned) in entries {
        let root = returned.guards.expect("each prefix contains a guard");
        assert_eq!(lengths[root], index + 1);
        let mut pending = vec![root];
        let mut order = Vec::new();
        while let Some(node) = pending.pop() {
            match sequences[node] {
                SequenceNode::Leaf(predicate) => {
                    let expression = exported["nodes"][predicate]["expressions"][0]
                        .as_u64()
                        .unwrap() as usize;
                    let argument = exported["nodes"][expression]["kind"]["Expression"]["Argument"]
                        .as_u64()
                        .unwrap() as usize;
                    order.push(argument);
                }
                SequenceNode::Branch(left, right) => {
                    pending.push(right);
                    pending.push(left);
                }
            }
        }
        assert_eq!(
            order,
            (0..=index).map(|position| position / 2).collect::<Vec<_>>()
        );
    }
}

#[test]
fn sequence_import_rejects_logical_length_overflow_without_expanding_the_dag() {
    #[derive(Serialize)]
    enum Predicate {
        Unknown,
    }
    #[derive(Serialize)]
    enum Kind {
        Predicate(Predicate),
    }
    #[derive(Serialize)]
    struct Node {
        kind: Kind,
        expressions: Vec<usize>,
        conditions: Vec<usize>,
    }

    let (fixture, bytes) = Fixture::produce();
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&bytes).expect("producer summary envelope");
    let nodes = artifact["nodes"].as_array_mut().expect("node table");
    let predicate = nodes.len();
    nodes.push(
        serde_json::to_value(Node {
            kind: Kind::Predicate(Predicate::Unknown),
            expressions: Vec::new(),
            conditions: Vec::new(),
        })
        .unwrap(),
    );
    let mut sequence = vec![SequenceNode::Leaf(predicate)];
    for child in 0..usize::BITS as usize {
        sequence.push(SequenceNode::Branch(child, child));
    }
    artifact["guard_sequences"] = serde_json::to_value(sequence).unwrap();
    let consumed = fixture.import(&artifact);
    assert!(!consumed.status.success());
    assert!(
        String::from_utf8_lossy(&consumed.stderr)
            .contains("ordered sequence graph exceeds its identity or length capacity")
    );
}
