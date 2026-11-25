#![feature(rustc_private)]

use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
use shapelint_driver::contracts::{Condition, Expr, Order};

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Alternatives {
    values: Vec<u8>,
}

#[hegel::test(print_blob = true)]
fn alternative_sets_share_identity_and_keep_first_written_order(tc: hegel::TestCase) {
    let Alternatives { values } = tc.draw(hegel::generators::default::<Alternatives>());
    with_graph(|mut graph| {
        let members = values
            .iter()
            .map(|value| {
                graph
                    .intern_expr(ExprNode::Number(u128::from(*value)))
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let forward = graph.alternatives(members.clone()).unwrap();
        let reverse = graph.alternatives(members.iter().rev().copied()).unwrap();
        let nested = graph.alternatives([forward, reverse, forward]).unwrap();
        assert_eq!(forward, reverse);
        assert_eq!(forward, nested);

        let mut expected = Vec::new();
        for value in values {
            if !expected.contains(&u128::from(value)) {
                expected.push(u128::from(value));
            }
        }
        let raised = graph.raise_expr(forward);
        let actual = match &raised {
            Expr::Alternatives(values) => values
                .iter()
                .map(|value| match value {
                    Expr::Number(value) => *value,
                    value => panic!("expected numeric alternative, got {value:?}"),
                })
                .collect::<Vec<_>>(),
            Expr::Number(value) => vec![*value],
            value => panic!("expected numeric alternatives, got {value:?}"),
        };
        assert_eq!(actual, expected);
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct Comparison {
    left: u8,
    right: u8,
}

#[hegel::test(print_blob = true)]
fn independently_lowered_conditions_share_their_expression_nodes(tc: hegel::TestCase) {
    let Comparison { left, right } = tc.draw(hegel::generators::default::<Comparison>());
    with_graph(|mut graph| {
        let left = Expr::Number(u128::from(left));
        let right = Expr::Number(u128::from(right));
        let condition = Condition::Compare(Order::Less, left.clone(), right.clone());
        let first = graph.lower_condition(&condition).unwrap();
        let second = graph.lower_condition(&condition).unwrap();
        assert_eq!(first, second);
        assert_eq!(graph.condition_count(), 1);
        let left_id = graph.lower_expr(&left).unwrap();
        let right_id = graph.lower_expr(&right).unwrap();
        match &graph[first] {
            ConditionNode::Compare(Order::Less, actual_left, actual_right) => {
                assert_eq!(*actual_left, left_id);
                assert_eq!(*actual_right, right_id);
            }
            actual => panic!("expected strict comparison, got {actual:?}"),
        }
        assert_eq!(graph.raise_condition(first), condition);
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
struct IndirectCalls {
    guard_arguments: Vec<u8>,
    value_arguments: Vec<u8>,
    offset: u8,
}

#[hegel::test(print_blob = true)]
fn tree_round_trips_preserve_guards_callees_and_argument_order(tc: hegel::TestCase) {
    use shapelint_driver::contracts::Target;

    let IndirectCalls {
        guard_arguments,
        value_arguments,
        offset,
    } = tc.draw(hegel::generators::default::<IndirectCalls>());
    let numbers = |values: Vec<u8>| {
        values
            .into_iter()
            .map(|value| Expr::Number(u128::from(value)))
            .collect()
    };
    let source = Expr::Select(
        Box::new(Condition::Returned(
            Target::Indirect(Box::new(Expr::Argument(0))),
            numbers(guard_arguments),
        )),
        Box::new(Expr::Call(
            Target::Indirect(Box::new(Expr::Argument(1))),
            numbers(value_arguments),
            None,
        )),
        Box::new(Expr::Test(Box::new(Condition::Boundary(
            Expr::Argument(2),
            Expr::Number(u128::from(offset)),
        )))),
    );

    assert_eq!(source.clone(), source);
    with_graph(|mut graph| {
        let id = graph.lower_expr(&source).unwrap();
        assert_eq!(graph.raise_expr(id), source);
    });
}

#[test]
fn shared_diamonds_allocate_one_node_per_distinct_expression() {
    with_graph(|mut graph| {
        let leaf = graph.intern_expr(ExprNode::Number(7)).unwrap();
        let mut current = leaf;
        // Each level doubles the unfolded tree while the graph grows by one node.
        for _ in 0..100_000 {
            let children = graph
                .expression_sequences
                .from_iter([current, current])
                .unwrap();
            let next = graph.intern_expr(ExprNode::Aggregate(children)).unwrap();
            let repeated = graph.intern_expr(ExprNode::Aggregate(children)).unwrap();
            assert_eq!(next, repeated);
            current = next;
        }
        assert_eq!(graph.expression_count(), 100_001);
        for _ in 0..100_000 {
            match &graph[current] {
                ExprNode::Aggregate(children) => {
                    assert_eq!(graph.expression_sequences.len(*children), 2);
                    let first = graph
                        .expression_sequences
                        .get(*children, 0)
                        .copied()
                        .unwrap();
                    let second = graph
                        .expression_sequences
                        .get(*children, 1)
                        .copied()
                        .unwrap();
                    assert_eq!(first, second);
                    current = first;
                }
                actual => panic!("expected shared aggregate, got {actual:?}"),
            }
        }
        assert_eq!(current, leaf);
    });
}

#[test]
fn deeply_nested_source_and_graph_traversals_preserve_every_field() {
    let mut source = Expr::Number(19);
    for field in 0..100_000 {
        source = Expr::Field(Box::new(source), field);
    }
    with_graph(|mut graph| {
        let id = graph.lower_expr(&source).unwrap();
        assert_eq!(graph.expression_count(), 100_001);
        let raised = graph.raise_expr(id);
        let mut raised = &raised;
        for expected in (0..100_000).rev() {
            match raised {
                Expr::Field(value, field) => {
                    assert_eq!(*field, expected);
                    raised = value;
                }
                _ => panic!("expected field at level {expected}"),
            }
        }
        assert_eq!(raised, &Expr::Number(19));
    });
    drop(source);
}

#[test]
fn expression_condition_edges_are_traversed_without_recursion() {
    with_graph(|mut graph| {
        let mut current = graph.intern_expr(ExprNode::Number(1)).unwrap();
        for _ in 0..100_000 {
            let condition = graph
                .intern_condition(ConditionNode::Variant(current, 0))
                .unwrap();
            current = graph.intern_expr(ExprNode::Test(condition)).unwrap();
        }
        assert_eq!(graph.expression_count(), 100_001);
        assert_eq!(graph.condition_count(), 100_000);
        let value = graph.raise_expr(current);
        let mut value = &value;
        for _ in 0..100_000 {
            match value {
                Expr::Test(condition) => match &**condition {
                    Condition::Variant(inner, 0) => value = inner,
                    _ => panic!("expected variant condition"),
                },
                _ => panic!("expected condition-valued expression"),
            }
        }
        assert_eq!(value, &Expr::Number(1));
    });
}

#[test]
fn deeply_nested_type_metadata_is_interned_without_recursive_hashing() {
    use shapelint_driver::calls::Type;

    let mut ty = Type::Bool;
    for _ in 0..100_000 {
        ty = Type::Slice(Box::new(ty));
    }
    let source = Expr::Typed(ty, Box::new(Expr::Number(3)));
    with_graph(|mut graph| {
        let first = graph.lower_expr(&source).unwrap();
        let second = graph.lower_expr(&source).unwrap();
        assert_eq!(first, second);
        assert_eq!(graph.expression_count(), 2);
        let raised = graph.raise_expr(first);
        let Expr::Typed(ty, value) = &raised else {
            panic!("expected typed expression");
        };
        assert_eq!(**value, Expr::Number(3));
        let mut ty = ty;
        for _ in 0..100_000 {
            match ty {
                Type::Slice(inner) => ty = inner,
                _ => panic!("expected slice type"),
            }
        }
        assert_eq!(ty, &Type::Bool);
    });
    drop(source);
}

fn compile_identity_probe(body: &str) -> std::process::Output {
    #[derive(serde::Deserialize)]
    struct Fingerprint {
        deps: Vec<Dependency>,
    }
    #[derive(serde::Deserialize)]
    #[serde(from = "(serde::de::IgnoredAny, String, serde::de::IgnoredAny, u64)")]
    struct Dependency {
        name: String,
        fingerprint: u64,
    }
    impl From<(serde::de::IgnoredAny, String, serde::de::IgnoredAny, u64)> for Dependency {
        fn from(value: (serde::de::IgnoredAny, String, serde::de::IgnoredAny, u64)) -> Self {
            Self {
                name: value.1,
                fingerprint: value.3,
            }
        }
    }

    let executable = std::env::current_exe().unwrap();
    let output = executable.parent().expect("Cargo test output directory");
    let artifact = output.parent().expect("Cargo test artifact directory");
    let package = artifact.parent().expect("Cargo package artifact directory");
    let build = package.parent().expect("Cargo build directory");
    let fingerprint: Fingerprint = serde_json::from_slice(
        &std::fs::read(artifact.join("fingerprint/test-integration-test-graph.json")).unwrap(),
    )
    .unwrap();
    let dependency = fingerprint
        .deps
        .into_iter()
        .find(|dependency| dependency.name == "shapelint_driver")
        .expect("the graph integration test links the driver library");
    let fingerprint = dependency
        .fingerprint
        .to_le_bytes()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    let library = std::fs::read_dir(package)
        .unwrap()
        .map(|entry| entry.unwrap())
        .filter(|entry| entry.file_type().unwrap().is_dir())
        .map(|entry| entry.path())
        .find(
            |path| match std::fs::read_to_string(path.join("fingerprint/lib-shapelint_driver")) {
                Ok(actual) => actual.trim() == fingerprint,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => false,
                Err(error) => panic!("cannot read library fingerprint: {error}"),
            },
        )
        .expect("the linked driver fingerprint identifies its library artifact");
    let hash = library.file_name().unwrap().to_str().unwrap();
    let library = library
        .join("out")
        .join(format!("libshapelint_driver-{hash}.rmeta"));
    let mut dependencies = Vec::new();
    for package in std::fs::read_dir(build).unwrap() {
        let package = package.unwrap();
        if !package.file_type().unwrap().is_dir() {
            continue;
        }
        for artifact in std::fs::read_dir(package.path()).unwrap() {
            let artifact = artifact.unwrap();
            if !artifact.file_type().unwrap().is_dir() {
                continue;
            }
            let output = artifact.path().join("out");
            if output.is_dir() {
                dependencies.push(output);
            }
        }
    }
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("identity.rs");
    std::fs::write(
        &source,
        format!(
            "#![feature(rustc_private)]\nuse shapelint_driver::contracts::graph::{{self, with_graph}};\nfn main() {{ {body} }}\n"
        ),
    )
    .unwrap();
    let mut command = std::process::Command::new("rustc");
    command
        .args(["--edition=2024", "--emit=metadata", "--error-format=json"])
        .arg("--extern")
        .arg(format!("shapelint_driver={}", library.display()));
    for dependency in dependencies {
        command
            .arg("-L")
            .arg(format!("dependency={}", dependency.display()));
    }
    command
        .arg("--out-dir")
        .arg(directory.path())
        .arg(source)
        .output()
        .unwrap()
}

#[test]
fn expression_id_cannot_enter_another_graph() {
    let valid = compile_identity_probe(
        "with_graph(|mut graph| { let id = graph.intern_expr(graph::ExprNode::Unknown).unwrap(); let _ = &graph[id]; });",
    );
    assert!(
        valid.status.success(),
        "{}",
        String::from_utf8_lossy(&valid.stderr)
    );
    let invalid = compile_identity_probe(
        "with_graph(|mut outer| { let id = outer.intern_expr(graph::ExprNode::Unknown).unwrap(); with_graph(|inner| { let _ = &inner[id]; }); });",
    );
    assert!(!invalid.status.success());
    let diagnostics = String::from_utf8(invalid.stderr).unwrap();
    assert!(diagnostics.contains("E0521"), "{diagnostics}");
}

#[test]
fn condition_id_cannot_enter_another_graph() {
    let valid = compile_identity_probe(
        "with_graph(|mut graph| { let id = graph.intern_condition(graph::ConditionNode::Unknown).unwrap(); let _ = &graph[id]; });",
    );
    assert!(
        valid.status.success(),
        "{}",
        String::from_utf8_lossy(&valid.stderr)
    );
    let invalid = compile_identity_probe(
        "with_graph(|mut outer| { let id = outer.intern_condition(graph::ConditionNode::Unknown).unwrap(); with_graph(|inner| { let _ = &inner[id]; }); });",
    );
    assert!(!invalid.status.success());
    let diagnostics = String::from_utf8(invalid.stderr).unwrap();
    assert!(diagnostics.contains("E0521"), "{diagnostics}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum TypeLayer {
    Slice,
    Tuple,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum TypeArgument {
    Character,
    SelfReference,
    WrongKind,
    Missing,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct TypeSubstitution {
    layers: Vec<TypeLayer>,
    argument: TypeArgument,
}

#[hegel::test(print_blob = true)]
fn metadata_substitution_preserves_structure_and_parameter_kinds(tc: hegel::TestCase) {
    use shapelint_driver::calls::{Generic, Type};
    use std::hash::{Hash, Hasher};

    let TypeSubstitution { layers, argument } =
        tc.draw(hegel::generators::default::<TypeSubstitution>());
    let mut input = Type::Parameter(0);
    for layer in &layers {
        input = match layer {
            TypeLayer::Slice => Type::Slice(Box::new(input)),
            TypeLayer::Tuple => Type::Tuple(vec![input]),
        };
    }
    let arguments = match argument {
        TypeArgument::Character => vec![Generic::Type(Type::Char)],
        TypeArgument::SelfReference => vec![Generic::Type(Type::Parameter(0))],
        TypeArgument::WrongKind => vec![Generic::Lifetime],
        TypeArgument::Missing => Vec::new(),
    };
    let cloned = input.clone();
    assert_eq!(input, cloned);
    let mut original_hash = std::hash::DefaultHasher::new();
    input.hash(&mut original_hash);
    let mut clone_hash = std::hash::DefaultHasher::new();
    cloned.hash(&mut clone_hash);
    assert_eq!(original_hash.finish(), clone_hash.finish());
    let substituted = shapelint_driver::contracts::graph::with_graph(|mut graph| {
        let input = graph.values.intern_type(&input).unwrap();
        let arguments = arguments
            .iter()
            .map(|argument| graph.values.intern_generic(argument))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();
        let arguments = graph
            .values
            .intern_list::<shapelint_driver::values::GenericsId<'_>>(arguments)
            .unwrap();
        let result = graph.values.substitute_type(input, arguments).unwrap();
        graph.values.export_type(result)
    });
    let (mut input, mut cloned, mut substituted) = (&input, &cloned, &substituted);
    let layers = layers.iter().rev();
    for layer in layers {
        match (layer, input, cloned, substituted) {
            (TypeLayer::Slice, Type::Slice(original), Type::Slice(copy), Type::Slice(result)) => {
                input = original;
                cloned = copy;
                substituted = result;
            }
            (TypeLayer::Tuple, Type::Tuple(original), Type::Tuple(copy), Type::Tuple(result)) => {
                assert_eq!(original.len(), 1);
                assert_eq!(copy.len(), 1);
                assert_eq!(result.len(), 1);
                input = &original[0];
                cloned = &copy[0];
                substituted = &result[0];
            }
            _ => panic!("substitution changed a type constructor"),
        }
    }
    assert_eq!(input, &Type::Parameter(0));
    assert_eq!(cloned, &Type::Parameter(0));
    match argument {
        TypeArgument::Character => assert_eq!(substituted, &Type::Char),
        TypeArgument::SelfReference | TypeArgument::WrongKind | TypeArgument::Missing => {
            assert_eq!(substituted, &Type::Parameter(0));
        }
    }
}

#[test]
fn choice_id_cannot_enter_another_graph() {
    let valid = compile_identity_probe(
        "with_graph(|mut graph| { let value = graph.intern_expr(graph::ExprNode::Unknown).unwrap(); let id = graph.intern_choice(graph::ChoiceNode::Value(value)).unwrap().unwrap(); let _ = &graph[id]; });",
    );
    assert!(
        valid.status.success(),
        "{}",
        String::from_utf8_lossy(&valid.stderr)
    );
    let invalid = compile_identity_probe(
        "with_graph(|mut outer| { let value = outer.intern_expr(graph::ExprNode::Unknown).unwrap(); let id = outer.intern_choice(graph::ChoiceNode::Value(value)).unwrap().unwrap(); with_graph(|inner| { let _ = &inner[id]; }); });",
    );
    assert!(!invalid.status.success());
    let diagnostics = String::from_utf8(invalid.stderr).unwrap();
    assert!(diagnostics.contains("E0521"), "{diagnostics}");
}
