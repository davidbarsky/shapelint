#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;

use rustc_data_structures::fx::FxHashSet;
use std::process::Command;

use serde::{Deserialize, Serialize};

#[test]
fn importing_and_exporting_a_shared_diamond_keeps_one_node_per_level() {
    #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
    struct Expression(usize);
    #[derive(Debug, Serialize, Deserialize)]
    enum ExpressionKind {
        Number(u128),
        Aggregate(usize),
    }
    #[derive(Debug, Serialize, Deserialize)]
    enum Kind {
        Expression(ExpressionKind),
    }
    #[derive(Debug, Serialize, Deserialize)]
    struct Node {
        kind: Kind,
        expressions: Vec<Expression>,
        conditions: Vec<usize>,
    }

    let directory = tempfile::tempdir().expect("source directory");
    let producer = directory.path().join("dependency.rs");
    let metadata = directory.path().join("libdependency.rmeta");
    let summary = directory.path().join("dependency.summary.json");
    std::fs::write(&producer, "pub fn value()->usize {7}").expect("producer source");
    let produced = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-name=dependency",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(&summary)
        .arg("-o")
        .arg(&metadata)
        .arg(&producer)
        .output()
        .expect("producer compilation");
    assert!(
        produced.status.success(),
        "{}",
        String::from_utf8_lossy(&produced.stderr)
    );
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&summary).expect("producer summary"))
            .expect("summary envelope");
    let definition = artifact["summaries"][0][0].clone();
    let consumer = directory.path().join("consumer.rs");
    let exported = directory.path().join("consumer.summary.json");
    std::fs::write(&consumer, "pub fn run() {}").expect("consumer source");
    let mut command = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"));
    command
        .args([
            "--format=json",
            "--crate-name=consumer",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-input",
        ])
        .arg(&summary)
        .arg("--summary-output")
        .arg(&exported)
        .arg("--extern")
        .arg(format!("dependency={}", metadata.display()))
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&consumer);
    let baseline = command.output().expect("baseline consumer compilation");
    assert!(
        baseline.status.success(),
        "{}",
        String::from_utf8_lossy(&baseline.stderr)
    );

    let mut nodes = vec![Node {
        kind: Kind::Expression(ExpressionKind::Number(7)),
        expressions: Vec::new(),
        conditions: Vec::new(),
    }];
    for _ in 0..100_000 {
        let child = Expression(nodes.len() - 1);
        nodes.push(Node {
            kind: Kind::Expression(ExpressionKind::Aggregate(2)),
            expressions: vec![child, child],
            conditions: Vec::new(),
        });
    }
    #[derive(Debug, Serialize, Deserialize)]
    enum FlowNode {
        Incoming,
        Alternatives(Option<usize>),
        Alternative {
            previous: Option<usize>,
            value: usize,
        },
    }
    #[derive(Serialize)]
    struct ProtocolReturn {
        name: &'static str,
        argument: usize,
        flow: usize,
    }
    let mut flows = vec![FlowNode::Incoming];
    for _ in 0..100_000 {
        let child = flows.len() - 1;
        flows.push(FlowNode::Alternative {
            previous: None,
            value: child,
        });
        flows.push(FlowNode::Alternative {
            previous: Some(flows.len() - 1),
            value: child,
        });
        flows.push(FlowNode::Alternatives(Some(flows.len() - 1)));
    }
    artifact["flows"] = serde_json::to_value(&flows).expect("shared flow table");
    artifact["summaries"][0][1]["protocol_returns"] = serde_json::to_value([
        ProtocolReturn {
            name: "durability",
            argument: 0,
            flow: flows.len() - 1,
        },
        ProtocolReturn {
            name: "durability",
            argument: 1,
            flow: flows.len() - 1,
        },
    ])
    .expect("shared flow roots");
    let root = Expression(nodes.len() - 1);
    artifact["nodes"] = serde_json::to_value(&nodes).expect("shared node table");
    artifact["summaries"][0][1]["returns"][0]["value"] =
        serde_json::to_value(root).expect("shared root");
    std::fs::write(
        &summary,
        serde_json::to_vec(&artifact).expect("shared summary bytes"),
    )
    .expect("shared summary input");
    let consumed = command.output().expect("shared consumer compilation");
    assert!(
        consumed.status.success(),
        "{}",
        String::from_utf8_lossy(&consumed.stderr)
    );
    assert_eq!(consumed.stdout, baseline.stdout);

    let exported: serde_json::Value =
        serde_json::from_slice(&std::fs::read(exported).expect("re-exported summary"))
            .expect("exported envelope");
    let imported = exported["summaries"]
        .as_array()
        .expect("exported summaries")
        .iter()
        .find(|entry| entry[0] == definition)
        .expect("imported definition remains exportable");
    let mut current: Expression =
        serde_json::from_value(imported[1]["returns"][0]["value"].clone())
            .expect("exported root reference");
    let mut reached = FxHashSet::default();
    loop {
        assert!(
            reached.insert(current),
            "the exported graph must be acyclic"
        );
        let node: Node = serde_json::from_value(exported["nodes"][current.0].clone())
            .expect("exported diamond node");
        assert!(node.conditions.is_empty());
        match node.kind {
            Kind::Expression(ExpressionKind::Aggregate(arity)) => {
                assert_eq!(arity, 2);
                let [left, right] = node.expressions.as_slice() else {
                    panic!("the shared pair retains both child references");
                };
                assert_eq!(left, right, "repeated children must retain one identity");
                assert!(left.0 < current.0, "children precede their parent");
                current = *left;
            }
            Kind::Expression(ExpressionKind::Number(value)) => {
                assert_eq!(value, 7);
                assert!(node.expressions.is_empty());
                break;
            }
        }
    }
    assert_eq!(reached.len(), nodes.len());
    assert_eq!(exported["flows"], artifact["flows"]);
    assert_eq!(
        imported[1]["protocol_returns"],
        artifact["summaries"][0][1]["protocol_returns"]
    );
}
