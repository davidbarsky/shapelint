#![feature(rustc_private)]

extern crate rustc_middle;

use shapelint_driver::calls::{Generic, Type};
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
use shapelint_driver::contracts::{Condition, Expr, Order};
use std::hash::{DefaultHasher, Hash, Hasher};

#[test]
fn deep_capture_traits_preserve_structure_and_drop_normally() {
    let mut value = Expr::Alternatives(vec![Expr::Number(1), Expr::Number(1)]);
    for index in 0..100_000 {
        value = Expr::Field(Box::new(value), index);
    }
    let condition = Condition::Compare(Order::Equal, value, Expr::Number(1));
    let cloned = condition.clone();
    assert_eq!(condition, cloned);
    let mut original_hash = DefaultHasher::new();
    condition.hash(&mut original_hash);
    let mut cloned_hash = DefaultHasher::new();
    cloned.hash(&mut cloned_hash);
    assert_eq!(original_hash.finish(), cloned_hash.finish());
    assert!(!format!("{condition:?}").is_empty());
    drop(condition);
    drop(cloned);
}

#[test]
fn deep_type_and_generic_traits_drop_normally() {
    let mut ty = Type::Bool;
    for _ in 0..100_000 {
        ty = Type::Array(
            Box::new(ty),
            Box::new(Generic::Const {
                value: 1,
                ty: Type::Uint(rustc_middle::ty::UintTy::Usize),
            }),
        );
    }
    let argument = Generic::Type(ty);
    let cloned = argument.clone();
    assert_eq!(argument, cloned);
    let mut original_hash = DefaultHasher::new();
    argument.hash(&mut original_hash);
    let mut cloned_hash = DefaultHasher::new();
    cloned.hash(&mut cloned_hash);
    assert_eq!(original_hash.finish(), cloned_hash.finish());
    assert!(!format!("{argument:?}").is_empty());
    drop(argument);
    drop(cloned);
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Alternatives {
    values: Vec<u8>,
}

#[hegel::test(print_blob = true)]
fn capture_clone_preserves_alternative_order_and_duplicates(tc: hegel::TestCase) {
    let Alternatives { values } = tc.draw(hegel::generators::default::<Alternatives>());
    let source = Expr::Alternatives(
        values
            .iter()
            .map(|value| Expr::Number(u128::from(*value)))
            .collect(),
    );
    let cloned = source.clone();
    let Expr::Alternatives(actual) = &cloned else {
        panic!("cloning preserves the alternatives constructor");
    };
    let actual = actual
        .iter()
        .map(|value| match value {
            Expr::Number(value) => *value,
            value => panic!("expected a captured number, got {value:?}"),
        })
        .collect::<Vec<_>>();
    assert_eq!(
        actual,
        values.into_iter().map(u128::from).collect::<Vec<_>>()
    );
}

#[test]
fn deeply_nested_artifact_trees_import_and_export_without_recursive_serde() {
    use std::process::Command;
    #[derive(serde::Serialize)]
    enum TypeToken {
        Slice,
        Bool,
    }
    #[derive(serde::Serialize)]
    enum ExpressionToken<'a> {
        Typed(&'a [TypeToken]),
        Field(usize),
        Number(u128),
        Test,
    }
    #[derive(serde::Serialize)]
    enum PredicateToken {
        NotVariant(usize),
    }
    #[derive(serde::Serialize)]
    enum Kind<'a> {
        Expression(ExpressionToken<'a>),
        Predicate(PredicateToken),
    }
    #[derive(serde::Serialize)]
    struct Node<'a> {
        kind: Kind<'a>,
        expressions: Vec<usize>,
        conditions: Vec<usize>,
    }
    #[derive(serde::Serialize)]
    enum FlowToken {
        Alternatives(Option<usize>),
        Alternative {
            previous: Option<usize>,
            value: usize,
        },
        Incoming,
    }
    #[derive(serde::Serialize)]
    struct ProtocolReturn<'a> {
        name: &'a str,
        argument: usize,
        flow: usize,
    }

    let directory = tempfile::tempdir().expect("source directory");
    let producer = directory.path().join("dependency.rs");
    let metadata = directory.path().join("libdependency.rmeta");
    let summary = directory.path().join("dependency.summary.json");
    std::fs::write(&producer, "pub fn value(_: &usize)->usize {7}").expect("producer source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
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
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&summary).expect("producer summary"))
            .expect("summary envelope");
    let mut types = (0..100_000).map(|_| TypeToken::Slice).collect::<Vec<_>>();
    types.push(TypeToken::Bool);
    let mut nodes = vec![Node {
        kind: Kind::Expression(ExpressionToken::Number(7)),
        expressions: Vec::new(),
        conditions: Vec::new(),
    }];
    for index in (0..100_000).rev() {
        nodes.push(Node {
            kind: Kind::Expression(ExpressionToken::Field(index)),
            expressions: vec![nodes.len() - 1],
            conditions: Vec::new(),
        });
    }
    nodes.push(Node {
        kind: Kind::Expression(ExpressionToken::Typed(&types)),
        expressions: vec![nodes.len() - 1],
        conditions: Vec::new(),
    });
    nodes.push(Node {
        kind: Kind::Predicate(PredicateToken::NotVariant(3)),
        expressions: vec![nodes.len() - 1],
        conditions: Vec::new(),
    });
    nodes.push(Node {
        kind: Kind::Expression(ExpressionToken::Test),
        expressions: Vec::new(),
        conditions: vec![nodes.len() - 1],
    });
    let payload = serde_json::to_value(&nodes).expect("flat wire fixture");
    artifact["nodes"] = payload.clone();
    artifact["summaries"][0][1]["returns"][0]["value"] =
        serde_json::to_value(nodes.len() - 1).expect("root reference");
    let mut flow = vec![FlowToken::Incoming];
    for _ in 0..100_000 {
        let value = flow.len() - 1;
        flow.push(FlowToken::Alternative {
            previous: None,
            value,
        });
        flow.push(FlowToken::Alternatives(Some(flow.len() - 1)));
    }
    artifact["flows"] = serde_json::to_value(&flow).expect("flow DAG");
    let protocol_returns = serde_json::to_value([ProtocolReturn {
        name: "durability",
        argument: 0,
        flow: flow.len() - 1,
    }])
    .expect("flat protocol fixture");
    artifact["summaries"][0][1]["protocol_returns"] = protocol_returns.clone();

    std::fs::write(
        &summary,
        serde_json::to_vec(&artifact).expect("deep summary"),
    )
    .expect("deep summary input");
    let consumer = directory.path().join("consumer.rs");
    let exported = directory.path().join("consumer.summary.json");
    std::fs::write(&consumer, "pub fn run() {}").expect("consumer source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
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
        .arg(&consumer)
        .output()
        .expect("consumer compilation");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let exported: serde_json::Value =
        serde_json::from_slice(&std::fs::read(exported).expect("consumer summary"))
            .expect("exported envelope");
    let summaries = exported["summaries"]
        .as_array()
        .expect("exported summaries");
    let imported = summaries
        .iter()
        .find(|entry| entry[0] == artifact["summaries"][0][0])
        .expect("imported definition remains exportable");
    let mut actual = imported[1]["returns"][0]["value"]
        .as_u64()
        .expect("exported expression reference") as usize;
    let expected = payload.as_array().expect("fixture nodes").iter().rev();
    for expected in expected {
        let node = &exported["nodes"][actual];
        assert_eq!(node["kind"], expected["kind"]);
        let expressions = node["expressions"]
            .as_array()
            .expect("expression references");
        let conditions = node["conditions"].as_array().expect("condition references");
        assert_eq!(
            expressions.len(),
            expected["expressions"].as_array().unwrap().len()
        );
        assert_eq!(
            conditions.len(),
            expected["conditions"].as_array().unwrap().len()
        );
        match (expressions.as_slice(), conditions.as_slice()) {
            ([child], []) | ([], [child]) => {
                actual = child.as_u64().expect("child reference") as usize
            }
            ([], []) => {}
            _ => panic!("deep fixture is a chain"),
        }
    }
    assert_eq!(imported[1]["protocol_returns"], protocol_returns);
    assert_eq!(exported["flows"], artifact["flows"]);
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum TreeDamage {
    MissingExpression,
    WrongChildKind,
    ExtraChild,
    ForwardReference,
    CyclicReference,
    MissingType,
    WrongTypeKind,
    MissingExcludedValue,
    WrongExcludedValueKind,
    MissingFlow,
    ForwardFlow,
    CyclicFlow,
    WrongFlowKind,
    WrongAlternativeKind,
    ForwardAlternative,
}

#[hegel::test(print_blob = true)]
fn malformed_flat_artifacts_report_the_broken_tree_contract(tc: hegel::TestCase) {
    use std::process::Command;
    #[derive(serde::Serialize)]
    enum TypeToken {
        Slice,
        Lifetime,
    }
    #[derive(serde::Serialize)]
    enum ExpressionToken {
        Field(usize),
        Number(u128),
        Typed(Vec<TypeToken>),
    }
    #[derive(serde::Serialize)]
    enum PredicateToken {
        Unknown,
        NotVariant(usize),
    }
    #[derive(serde::Serialize)]
    enum Kind {
        Expression(ExpressionToken),
        Predicate(PredicateToken),
    }
    #[derive(serde::Serialize)]
    struct Node {
        kind: Kind,
        expressions: Vec<usize>,
        conditions: Vec<usize>,
    }
    let damage = tc.draw(hegel::generators::default::<TreeDamage>());
    let (nodes, expected) = match damage {
        TreeDamage::WrongFlowKind => (
            vec![Node {
                kind: Kind::Expression(ExpressionToken::Number(1)),
                expressions: vec![],
                conditions: vec![],
            }],
            "summary flow reference names an alternative sequence",
        ),
        TreeDamage::WrongAlternativeKind => (
            vec![Node {
                kind: Kind::Expression(ExpressionToken::Number(1)),
                expressions: vec![],
                conditions: vec![],
            }],
            "summary alternative reference names a flow",
        ),
        TreeDamage::ForwardAlternative => (
            vec![Node {
                kind: Kind::Expression(ExpressionToken::Number(1)),
                expressions: vec![],
                conditions: vec![],
            }],
            "summary alternative reference is missing or forward",
        ),
        TreeDamage::MissingFlow | TreeDamage::ForwardFlow | TreeDamage::CyclicFlow => (
            vec![Node {
                kind: Kind::Expression(ExpressionToken::Number(1)),
                expressions: vec![],
                conditions: vec![],
            }],
            "summary flow reference is missing or forward",
        ),
        TreeDamage::MissingExcludedValue => (
            vec![Node {
                kind: Kind::Predicate(PredicateToken::NotVariant(3)),
                expressions: vec![],
                conditions: vec![],
            }],
            "summary expression has a missing child",
        ),
        TreeDamage::WrongExcludedValueKind => (
            vec![
                Node {
                    kind: Kind::Predicate(PredicateToken::Unknown),
                    expressions: vec![],
                    conditions: vec![],
                },
                Node {
                    kind: Kind::Predicate(PredicateToken::NotVariant(3)),
                    expressions: vec![0],
                    conditions: vec![],
                },
            ],
            "summary expression reference names a condition",
        ),
        TreeDamage::MissingExpression => (
            vec![Node {
                kind: Kind::Expression(ExpressionToken::Field(0)),
                expressions: vec![],
                conditions: vec![],
            }],
            "summary expression has a missing child",
        ),
        TreeDamage::WrongChildKind => (
            vec![
                Node {
                    kind: Kind::Predicate(PredicateToken::Unknown),
                    expressions: vec![],
                    conditions: vec![],
                },
                Node {
                    kind: Kind::Expression(ExpressionToken::Field(0)),
                    expressions: vec![0],
                    conditions: vec![],
                },
            ],
            "summary expression reference names a condition",
        ),
        TreeDamage::ForwardReference => (
            vec![
                Node {
                    kind: Kind::Expression(ExpressionToken::Field(0)),
                    expressions: vec![1],
                    conditions: vec![],
                },
                Node {
                    kind: Kind::Expression(ExpressionToken::Number(1)),
                    expressions: vec![],
                    conditions: vec![],
                },
            ],
            "summary expression reference is missing or forward",
        ),
        TreeDamage::CyclicReference => (
            vec![Node {
                kind: Kind::Expression(ExpressionToken::Field(0)),
                expressions: vec![0],
                conditions: vec![],
            }],
            "summary expression reference is missing or forward",
        ),
        TreeDamage::ExtraChild => (
            vec![
                Node {
                    kind: Kind::Expression(ExpressionToken::Number(1)),
                    expressions: vec![],
                    conditions: vec![],
                },
                Node {
                    kind: Kind::Expression(ExpressionToken::Number(2)),
                    expressions: vec![0],
                    conditions: vec![],
                },
            ],
            "summary graph node has extra children",
        ),
        TreeDamage::MissingType => (
            vec![
                Node {
                    kind: Kind::Expression(ExpressionToken::Number(1)),
                    expressions: vec![],
                    conditions: vec![],
                },
                Node {
                    kind: Kind::Expression(ExpressionToken::Typed(vec![TypeToken::Slice])),
                    expressions: vec![0],
                    conditions: vec![],
                },
            ],
            "type metadata has a missing child",
        ),
        TreeDamage::WrongTypeKind => (
            vec![
                Node {
                    kind: Kind::Expression(ExpressionToken::Number(1)),
                    expressions: vec![],
                    conditions: vec![],
                },
                Node {
                    kind: Kind::Expression(ExpressionToken::Typed(vec![
                        TypeToken::Slice,
                        TypeToken::Lifetime,
                    ])),
                    expressions: vec![0],
                    conditions: vec![],
                },
            ],
            "type metadata has a child of the wrong kind",
        ),
    };
    let directory = tempfile::tempdir().expect("source directory");
    let producer = directory.path().join("dependency.rs");
    let metadata = directory.path().join("libdependency.rmeta");
    let summary = directory.path().join("dependency.summary.json");
    std::fs::write(&producer, "pub fn value()->usize {7}").expect("producer source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
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
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&summary).expect("producer summary"))
            .expect("summary envelope");
    artifact["summaries"][0][1]["returns"][0]["value"] =
        serde_json::to_value(nodes.len() - 1).expect("root reference");
    artifact["nodes"] = serde_json::to_value(nodes).expect("malformed wire fixture");
    #[derive(serde::Serialize)]
    enum FlowNode {
        Incoming,
        Alternative {
            previous: Option<usize>,
            value: usize,
        },
        Alternatives(Option<usize>),
    }
    #[derive(serde::Serialize)]
    struct ProtocolReturn {
        name: &'static str,
        argument: usize,
        flow: usize,
    }
    let flow_root = match damage {
        TreeDamage::WrongFlowKind => 1,
        TreeDamage::MissingFlow
        | TreeDamage::ForwardFlow
        | TreeDamage::CyclicFlow
        | TreeDamage::WrongAlternativeKind
        | TreeDamage::ForwardAlternative
        | TreeDamage::MissingExpression
        | TreeDamage::WrongChildKind
        | TreeDamage::ExtraChild
        | TreeDamage::ForwardReference
        | TreeDamage::CyclicReference
        | TreeDamage::MissingType
        | TreeDamage::WrongTypeKind
        | TreeDamage::MissingExcludedValue
        | TreeDamage::WrongExcludedValueKind => 0,
    };
    let flows = match damage {
        TreeDamage::WrongFlowKind => Some(vec![
            FlowNode::Incoming,
            FlowNode::Alternative {
                previous: None,
                value: 0,
            },
        ]),
        TreeDamage::WrongAlternativeKind => {
            Some(vec![FlowNode::Incoming, FlowNode::Alternatives(Some(0))])
        }
        TreeDamage::ForwardAlternative => Some(vec![FlowNode::Alternatives(Some(1))]),
        TreeDamage::MissingFlow => Some(Vec::new()),
        TreeDamage::ForwardFlow => Some(vec![
            FlowNode::Alternative {
                previous: None,
                value: 1,
            },
            FlowNode::Incoming,
        ]),
        TreeDamage::CyclicFlow => Some(vec![FlowNode::Alternative {
            previous: None,
            value: 0,
        }]),
        TreeDamage::MissingExpression
        | TreeDamage::WrongChildKind
        | TreeDamage::ExtraChild
        | TreeDamage::ForwardReference
        | TreeDamage::CyclicReference
        | TreeDamage::MissingType
        | TreeDamage::WrongTypeKind
        | TreeDamage::MissingExcludedValue
        | TreeDamage::WrongExcludedValueKind => None,
    };
    if let Some(flows) = flows {
        artifact["flows"] = serde_json::to_value(flows).expect("invalid flow table");
        artifact["summaries"][0][1]["protocol_returns"] = serde_json::to_value([ProtocolReturn {
            name: "durability",
            argument: 0,
            flow: flow_root,
        }])
        .expect("invalid flow root");
    }

    std::fs::write(
        &summary,
        serde_json::to_vec(&artifact).expect("summary bytes"),
    )
    .expect("summary input");
    let consumer = directory.path().join("consumer.rs");
    std::fs::write(&consumer, "pub fn run() {}").expect("consumer source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-name=consumer",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-input",
        ])
        .arg(&summary)
        .arg("--extern")
        .arg(format!("dependency={}", metadata.display()))
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&consumer)
        .output()
        .expect("consumer compilation");
    assert!(
        !output.status.success(),
        "{damage:?}: invalid tree was accepted"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(expected),
        "{damage:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn deep_diagnostic_rendering_preserves_every_suffix() {
    extern crate rustc_driver;
    extern crate rustc_interface;
    extern crate rustc_hir;
    struct Render;
    impl rustc_driver::Callbacks for Render {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            with_graph(|mut graph| {
                let mut value = graph.intern_expr(ExprNode::Number(7)).expect("seven");
                for _ in 0..100_000 {
                    value = graph.intern_expr(ExprNode::Length(value)).expect("length");
                }
                let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                let condition = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, value, zero))
                    .expect("comparison");
                let restorer = std::cell::RefCell::new(graph.values.restorer(tcx));
                let actual = shapelint_driver::diagnostics::Condition {
                    restorer: &restorer,
                    tcx,
                    def: rustc_hir::def_id::LOCAL_CRATE.as_def_id(),
                    condition,
                    graph: &graph,
                }
                .to_string();
                let expected = format!("7{} == 0", ".len()".repeat(100_000));
                assert_eq!(actual, expected);
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("render.rs");
    std::fs::write(&source, "pub fn run() {}").expect("render source");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        source.display().to_string(),
    ];
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Render));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Exclusion {
    argument: u8,
    variant: usize,
}

#[hegel::test(print_blob = true)]
fn capture_clone_preserves_excluded_variant_indexes(tc: hegel::TestCase) {
    let Exclusion { argument, variant } = tc.draw(hegel::generators::default::<Exclusion>());
    let condition = Condition::NotVariant(Expr::Argument(usize::from(argument)), variant);
    let cloned = condition.clone();
    match &cloned {
        Condition::NotVariant(Expr::Argument(actual_argument), actual_variant) => {
            assert_eq!(*actual_argument, usize::from(argument));
            assert_eq!(*actual_variant, variant);
        }
        condition => panic!("cloning changed a variant exclusion: {condition:?}"),
    }
    assert_eq!(condition, cloned);
    assert_ne!(
        condition,
        Condition::Variant(Expr::Argument(usize::from(argument)), variant)
    );
    let mut original_hash = DefaultHasher::new();
    condition.hash(&mut original_hash);
    let mut cloned_hash = DefaultHasher::new();
    cloned.hash(&mut cloned_hash);
    assert_eq!(original_hash.finish(), cloned_hash.finish());
}

#[test]
fn excluded_variant_diagnostics_name_the_forbidden_variant() {
    extern crate rustc_driver;
    extern crate rustc_interface;
    struct Render;
    impl rustc_driver::Callbacks for Render {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let def = tcx
                .hir_body_owners()
                .find(|def| match tcx.opt_item_name(def.to_def_id()) {
                    Some(name) => name.as_str() == "run",
                    None => false,
                })
                .expect("the fixture declares run")
                .to_def_id();
            with_graph(|mut graph| {
                let value = graph.intern_expr(ExprNode::Argument(0)).expect("argument");
                let condition = graph
                    .intern_condition(ConditionNode::NotVariant(value, 3))
                    .expect("excluded variant");
                let restorer = std::cell::RefCell::new(graph.values.restorer(tcx));
                let actual = shapelint_driver::diagnostics::Condition {
                    restorer: &restorer,
                    tcx,
                    def,
                    condition,
                    graph: &graph,
                }
                .to_string();
                assert_eq!(actual, "value must not be State::Fourth");
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("render_exclusion.rs");
    std::fs::write(&source, "pub enum State { First=10, Second=20, Third=30, Fourth=40 } pub fn run(value:State) {let _=value;}").expect("render source");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        source.display().to_string(),
    ];
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Render));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[test]
fn malformed_artifact_drops_a_deep_partially_decoded_value() {
    use std::process::Command;
    #[derive(serde::Serialize)]
    enum ExpressionToken {
        Aggregate(usize),
        Field(usize),
        Number(u128),
    }
    #[derive(serde::Serialize)]
    enum PredicateToken {
        Unknown,
    }
    #[derive(serde::Serialize)]
    enum Kind {
        Expression(ExpressionToken),
        Predicate(PredicateToken),
    }
    #[derive(serde::Serialize)]
    struct Node {
        kind: Kind,
        expressions: Vec<usize>,
        conditions: Vec<usize>,
    }
    let directory = tempfile::tempdir().expect("source directory");
    let producer = directory.path().join("dependency.rs");
    let metadata = directory.path().join("libdependency.rmeta");
    let summary = directory.path().join("dependency.summary.json");
    std::fs::write(&producer, "pub fn value()->usize {7}").expect("producer source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
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
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let mut artifact: serde_json::Value =
        serde_json::from_slice(&std::fs::read(&summary).expect("producer summary"))
            .expect("summary envelope");
    let mut nodes = vec![Node {
        kind: Kind::Expression(ExpressionToken::Number(7)),
        expressions: vec![],
        conditions: vec![],
    }];
    for index in (0..100_000).rev() {
        nodes.push(Node {
            kind: Kind::Expression(ExpressionToken::Field(index)),
            expressions: vec![nodes.len() - 1],
            conditions: vec![],
        });
    }
    let value = nodes.len() - 1;
    nodes.push(Node {
        kind: Kind::Predicate(PredicateToken::Unknown),
        expressions: vec![],
        conditions: vec![],
    });
    nodes.push(Node {
        kind: Kind::Expression(ExpressionToken::Aggregate(2)),
        expressions: vec![value, nodes.len() - 1],
        conditions: vec![],
    });
    artifact["summaries"][0][1]["returns"][0]["value"] =
        serde_json::to_value(nodes.len() - 1).expect("root reference");
    artifact["nodes"] = serde_json::to_value(nodes).expect("malformed wire fixture");
    std::fs::write(
        &summary,
        serde_json::to_vec(&artifact).expect("summary bytes"),
    )
    .expect("summary input");
    let consumer = directory.path().join("consumer.rs");
    std::fs::write(&consumer, "pub fn run() {}").expect("consumer source");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--crate-name=consumer",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
            "--summary-input",
        ])
        .arg(&summary)
        .arg("--extern")
        .arg(format!("dependency={}", metadata.display()))
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&consumer)
        .output()
        .expect("consumer compilation");
    assert!(
        !output.status.success(),
        "invalid aggregate child was accepted"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("summary expression reference names a condition"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn returned_diagnostic_ignores_a_deep_shared_argument_graph() {
    extern crate rustc_driver;
    extern crate rustc_interface;
    use shapelint_driver::calls::{Dispatch, Instance};
    use shapelint_driver::contracts::graph::TargetNode;

    struct Render;
    impl rustc_driver::Callbacks for Render {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let def = tcx
                .hir_body_owners()
                .next()
                .expect("run function")
                .to_def_id();
            with_graph(|mut graph| {
                let mut value = graph.intern_expr(ExprNode::Number(7)).expect("seven");
                for _ in 0..100_000 {
                    let fields = graph
                        .expression_sequences
                        .from_iter([value, value])
                        .expect("fields");
                    value = graph
                        .intern_expr(ExprNode::Aggregate(fields))
                        .expect("shared aggregate");
                }
                let instance = graph
                    .values
                    .intern_instance(&Instance {
                        def,
                        args: Vec::new(),
                        dispatch: Dispatch::Item,
                    })
                    .expect("instance");
                let arguments = graph
                    .expression_sequences
                    .from_iter([value])
                    .expect("arguments");
                let condition = graph
                    .intern_condition(ConditionNode::Returned(
                        TargetNode::Direct(instance),
                        arguments,
                    ))
                    .expect("return condition");
                let restorer = std::cell::RefCell::new(graph.values.restorer(tcx));
                let actual = shapelint_driver::diagnostics::Condition {
                    restorer: &restorer,
                    tcx,
                    def,
                    condition,
                    graph: &graph,
                }
                .to_string();
                assert_eq!(actual, "run must return normally");
                assert_eq!(graph.expression_count(), 100_001);
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("render_returned.rs");
    std::fs::write(&source, "pub fn run() {}").expect("render source");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        source.display().to_string(),
    ];
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Render));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum TypeLayer {
    Slice,
    Tuple,
    Array(u8),
    GenericArray(u8),
}

#[hegel::test(print_blob = true)]
fn type_identity_matches_generated_structure(tc: hegel::TestCase) {
    let (left, right) = tc.draw(hegel::generators::default::<(Vec<TypeLayer>, Vec<TypeLayer>)>());
    let build = |layers: &[TypeLayer]| {
        let mut ty = Type::Bool;
        for layer in layers {
            ty = match layer {
                TypeLayer::Slice => Type::Slice(Box::new(ty)),
                TypeLayer::Tuple => Type::Tuple(vec![ty]),
                TypeLayer::Array(value) => Type::Array(
                    Box::new(ty),
                    Box::new(Generic::Const {
                        value: u128::from(*value),
                        ty: Type::Bool,
                    }),
                ),
                TypeLayer::GenericArray(index) => Type::Array(
                    Box::new(ty),
                    Box::new(Generic::Parameter(u32::from(*index))),
                ),
            };
        }
        ty
    };
    let a = build(&left);
    let b = build(&right);
    assert_eq!(a == b, left == right);
    let mut map = std::collections::HashMap::new();
    map.insert(Generic::Type(a), ());
    assert_eq!(
        map.get(&Generic::Type(b)).map(|_| ()),
        (left == right).then_some(())
    );
}
