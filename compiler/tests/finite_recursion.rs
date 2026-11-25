#![feature(rustc_private)]

use std::fmt::{self, Write};
use std::process::Command;

use hegel::generators::{self, BoxedPrintableGenerator, DefaultGenerator};
use hegel::{PrintableGenerator, TestCase};
use serde::Deserialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum Flag {
    Clear,
    Set,
}

impl fmt::Display for Flag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Clear => "false",
            Self::Set => "true",
        })
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Shape {
    Return(u8),
    Call(Flag),
}

#[derive(Clone, Copy, Debug)]
enum Step {
    Return(u8),
    Call { function: usize, flag: Flag },
}

impl fmt::Display for Step {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Return(value) => write!(f, "{value}"),
            Self::Call { function, flag } => write!(f, "node_{function}({flag})"),
        }
    }
}

#[derive(Debug)]
struct Model {
    nodes: Vec<[Step; 2]>,
}

impl DefaultGenerator for Model {
    type Generator = BoxedPrintableGenerator<'static, Self>;
    fn default_generator() -> Self::Generator {
        hegel::compose!(|tc| {
            let shapes =
                tc.draw(generators::vecs(generators::default::<(Shape, Shape)>()).min_size(1));
            let last = shapes.len() - 1;
            let nodes = shapes
                .into_iter()
                .map(|(clear, set)| {
                    [clear, set].map(|shape| match shape {
                        Shape::Return(value) => Step::Return(value),
                        Shape::Call(flag) => Step::Call {
                            function: tc.draw(generators::integers::<usize>().max_value(last)),
                            flag,
                        },
                    })
                })
                .collect();
            Self { nodes }
        })
        .boxed_printable()
    }
}

#[derive(Debug)]
enum Outcome {
    Return(u8),
    Diverges,
}

impl Model {
    fn outcome(&self, mut function: usize, mut flag: Flag) -> Outcome {
        let mut visited = Vec::new();
        loop {
            if visited.contains(&(function, flag)) {
                return Outcome::Diverges;
            }
            visited.push((function, flag));
            let step = match flag {
                Flag::Clear => self.nodes[function][0],
                Flag::Set => self.nodes[function][1],
            };
            match step {
                Step::Return(value) => return Outcome::Return(value),
                Step::Call {
                    function: next,
                    flag: next_flag,
                } => {
                    function = next;
                    flag = next_flag;
                }
            }
        }
    }
}

#[derive(Debug, Deserialize)]
struct Finding {
    rule: String,
    item: String,
}

struct RustSource<'a>(&'a str);

fn analyze(RustSource(source): RustSource<'_>) -> Vec<Finding> {
    let directory = tempfile::tempdir().expect("source directory");
    let path = directory.path().join("finite.rs");
    std::fs::write(&path, source).expect("source file");
    let output = Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--show-analysis-gaps",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
        ])
        .arg("--out-dir")
        .arg(directory.path())
        .arg(path)
        .output()
        .expect("run driver");
    assert!(
        output.status.success(),
        "{source}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{source}\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("diagnostic text")
        .lines()
        .map(|line| serde_json::from_str(line).expect("diagnostic"))
        .collect()
}

#[hegel::test(print_blob = true)]
fn finite_call_states_agree_with_independent_execution_and_cycle_detection(tc: TestCase) {
    let model = tc.draw(generators::default::<Model>());
    let mut source = String::new();
    let mut expected = Vec::new();
    let nodes = model.nodes.iter().enumerate();
    for (function, [clear, set]) in nodes {
        write!(source, "#[allow(unconditional_recursion)]fn node_{function}(flag:bool)->u8{{if flag{{{set}}}else{{{clear}}}}}").expect("source text");
        for (suffix, flag) in [("clear", Flag::Clear), ("set", Flag::Set)] {
            let item = format!("probe_{function}_{suffix}");
            write!(source, "pub fn {item}()->u8{{node_{function}({flag})-1}}")
                .expect("source text");
            match model.outcome(function, flag) {
                Outcome::Return(0) => expected.push(item),
                Outcome::Return(_) | Outcome::Diverges => {}
            }
        }
    }
    let findings = analyze(RustSource(&source));
    let mut actual = Vec::new();
    for finding in &findings {
        match (finding.item.starts_with("probe_"), finding.rule.as_str()) {
            (true, "invalid-state-use") => actual.push(finding.item.clone()),
            (true, "unproven-precondition" | "analysis-incomplete") => {
                panic!("finite state was not decided: {finding:?}\n{model:?}\n{source}")
            }
            _ => {}
        }
    }
    actual.sort();
    expected.sort();
    assert_eq!(actual, expected, "{model:?}\n{source}\n{findings:?}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Boundary {
    External,
    RecursiveExternal,
}

#[hegel::test(print_blob = true)]
fn an_unknown_external_return_is_not_proven_divergence(tc: TestCase) {
    let boundary = tc.draw(generators::default::<Boundary>());
    let body = match boundary {
        Boundary::External => "unsafe{external(flag)}",
        Boundary::RecursiveExternal => "if flag{unsafe{external(flag)}}else{value(true)}",
    };
    let source = format!(
        "unsafe extern \"Rust\"{{fn external(flag:bool)->u8;}}fn value(flag:bool)->u8{{{body}}}pub fn probe()->u8{{value(false)-1}}"
    );
    let findings = analyze(RustSource(&source));
    let rules: Vec<_> = findings
        .iter()
        .filter(|finding| finding.item == "probe")
        .map(|finding| finding.rule.as_str())
        .collect();
    assert!(
        rules.contains(&"unproven-precondition"),
        "{source}\n{findings:?}"
    );
    assert!(
        !rules.contains(&"invalid-state-use"),
        "{source}\n{findings:?}"
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Amount {
    Zero,
    Positive(u8),
}

#[hegel::test(print_blob = true)]
fn requirements_before_a_nonreturning_cycle_remain_reachable(tc: TestCase) {
    let amount = tc.draw(generators::default::<Amount>());
    let value = match amount {
        Amount::Zero => 0,
        Amount::Positive(value) => value.max(1),
    };
    let source = format!(
        "fn sample()->u8{{{value}}}fn cycle(flag:bool)->u8{{if flag{{let _=sample()-1;cycle(flag)}}else{{1}}}}pub fn probe()->u8{{cycle(true)-1}}"
    );
    let findings = analyze(RustSource(&source));
    let invalid: Vec<_> = findings
        .iter()
        .filter(|finding| finding.item == "probe" && finding.rule == "invalid-state-use")
        .collect();
    let expected = match amount {
        Amount::Zero => 1,
        Amount::Positive(_) => 0,
    };
    assert_eq!(invalid.len(), expected, "{source}\n{findings:?}");
    let gaps: Vec<_> = findings
        .iter()
        .filter(|finding| {
            finding.item == "probe"
                && (finding.rule == "unproven-precondition"
                    || finding.rule == "analysis-incomplete")
        })
        .collect();
    assert!(gaps.is_empty(), "{source}\n{findings:?}");
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum Variant {
    First,
    Second,
    Third,
}

impl Variant {
    fn index(self) -> usize {
        match self {
            Self::First => 0,
            Self::Second => 1,
            Self::Third => 2,
        }
    }
    fn name(self) -> &'static str {
        match self {
            Self::First => "First",
            Self::Second => "Second",
            Self::Third => "Third",
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum EnumShape {
    Return(u8),
    Call(Variant),
}

#[derive(Clone, Copy, Debug)]
enum EnumStep {
    Return(u8),
    Call { function: usize, variant: Variant },
}

#[derive(Debug)]
struct EnumModel {
    nodes: Vec<[EnumStep; 3]>,
}

impl DefaultGenerator for EnumModel {
    type Generator = BoxedPrintableGenerator<'static, Self>;
    fn default_generator() -> Self::Generator {
        hegel::compose!(|tc| {
            let shapes = tc.draw(
                generators::vecs(generators::default::<(EnumShape, EnumShape, EnumShape)>())
                    .min_size(1),
            );
            let last = shapes.len() - 1;
            let nodes = shapes
                .into_iter()
                .map(|(first, second, third)| {
                    [first, second, third].map(|shape| match shape {
                        EnumShape::Return(value) => EnumStep::Return(value),
                        EnumShape::Call(variant) => EnumStep::Call {
                            function: tc.draw(generators::integers::<usize>().max_value(last)),
                            variant,
                        },
                    })
                })
                .collect();
            Self { nodes }
        })
        .boxed_printable()
    }
}

impl EnumModel {
    fn outcome(&self, mut function: usize, mut variant: Variant) -> Outcome {
        let mut visited = Vec::new();
        loop {
            if visited.contains(&(function, variant)) {
                return Outcome::Diverges;
            }
            visited.push((function, variant));
            match self.nodes[function][variant.index()] {
                EnumStep::Return(value) => return Outcome::Return(value),
                EnumStep::Call {
                    function: next,
                    variant: next_variant,
                } => {
                    function = next;
                    variant = next_variant;
                }
            }
        }
    }
}

#[hegel::test(print_blob = true)]
fn enum_call_states_use_variant_identity_and_explicit_discriminants(tc: TestCase) {
    let model = tc.draw(generators::default::<EnumModel>());
    let mut source = String::from("#[repr(i8)]enum Flag{First=-7,Second=5,Third=101}");
    let mut expected = Vec::new();
    let nodes = model.nodes.iter().enumerate();
    for (function, steps) in nodes {
        write!(
            source,
            "#[allow(unconditional_recursion)]fn node_{function}(flag:Flag)->u8{{match flag{{"
        )
        .expect("source text");
        let cases = [Variant::First, Variant::Second, Variant::Third]
            .into_iter()
            .zip(steps);
        for (variant, step) in cases {
            write!(source, "Flag::{}=>", variant.name()).expect("source text");
            match step {
                EnumStep::Return(value) => write!(source, "{value},"),
                EnumStep::Call { function, variant } => {
                    write!(source, "node_{function}(Flag::{}),", variant.name())
                }
            }
            .expect("source text");
        }
        source.push_str("}}");
        for variant in [Variant::First, Variant::Second, Variant::Third] {
            let item = format!("probe_{function}_{}", variant.index());
            write!(
                source,
                "pub fn {item}()->u8{{node_{function}(Flag::{})-1}}",
                variant.name()
            )
            .expect("source text");
            match model.outcome(function, variant) {
                Outcome::Return(0) => expected.push(item),
                Outcome::Return(_) | Outcome::Diverges => {}
            }
        }
    }
    let findings = analyze(RustSource(&source));
    let mut actual = Vec::new();
    for finding in &findings {
        match (finding.item.starts_with("probe_"), finding.rule.as_str()) {
            (true, "invalid-state-use") => actual.push(finding.item.clone()),
            (true, "unproven-precondition" | "analysis-incomplete") => {
                panic!("finite enum state was not decided: {finding:?}\n{model:?}\n{source}")
            }
            _ => {}
        }
    }
    actual.sort();
    expected.sort();
    assert_eq!(actual, expected, "{model:?}\n{source}\n{findings:?}");
}

#[test]
fn an_unselected_recursive_arm_does_not_block_a_return() {
    let source = r#"
        enum Flag { First, Second, Third }
        fn a(flag: Flag) -> u8 {
            match flag {
                Flag::First => b(Flag::Third),
                Flag::Second => 0,
                Flag::Third => b(Flag::Second),
            }
        }
        #[allow(unconditional_recursion)]
        fn b(flag: Flag) -> u8 {
            match flag {
                Flag::First => a(Flag::Third),
                Flag::Second => a(Flag::First),
                Flag::Third => a(Flag::Second),
            }
        }
        pub fn probe() -> u8 { b(Flag::First) - 1 }
    "#;
    let findings = analyze(RustSource(source));
    let rules: Vec<_> = findings
        .iter()
        .filter(|finding| finding.item == "probe")
        .map(|finding| finding.rule.as_str())
        .collect();
    assert_eq!(rules, ["invalid-state-use"], "{findings:?}");
}

#[test]
fn finite_enum_self_cycle_propagates_divergence_to_callers() {
    let source = r#"#[repr(i8)]enum Flag{First=-7,Second=5,Third=101}#[allow(unconditional_recursion)]fn node_0(flag:Flag)->u8{match flag{Flag::First=>0,Flag::Second=>0,Flag::Third=>node_2(Flag::Second),}}pub fn probe_0_0()->u8{node_0(Flag::First)-1}pub fn probe_0_1()->u8{node_0(Flag::Second)-1}pub fn probe_0_2()->u8{node_0(Flag::Third)-1}#[allow(unconditional_recursion)]fn node_1(flag:Flag)->u8{match flag{Flag::First=>0,Flag::Second=>node_1(Flag::Second),Flag::Third=>node_0(Flag::First),}}pub fn probe_1_0()->u8{node_1(Flag::First)-1}pub fn probe_1_1()->u8{node_1(Flag::Second)-1}pub fn probe_1_2()->u8{node_1(Flag::Third)-1}#[allow(unconditional_recursion)]fn node_2(flag:Flag)->u8{match flag{Flag::First=>0,Flag::Second=>node_1(Flag::Second),Flag::Third=>node_1(Flag::First),}}pub fn probe_2_0()->u8{node_2(Flag::First)-1}pub fn probe_2_1()->u8{node_2(Flag::Second)-1}pub fn probe_2_2()->u8{node_2(Flag::Third)-1}"#;
    let findings = analyze(RustSource(source));
    let mut actual: Vec<_> = findings
        .iter()
        .filter_map(
            |finding| match (finding.item.starts_with("probe_"), finding.rule.as_str()) {
                (true, "invalid-state-use" | "unproven-precondition" | "analysis-incomplete") => {
                    Some((finding.item.as_str(), finding.rule.as_str()))
                }
                _ => None,
            },
        )
        .collect();
    actual.sort();
    assert_eq!(
        actual,
        vec![
            ("probe_0_0", "invalid-state-use"),
            ("probe_0_1", "invalid-state-use"),
            ("probe_1_0", "invalid-state-use"),
            ("probe_1_2", "invalid-state-use"),
            ("probe_2_0", "invalid-state-use"),
            ("probe_2_2", "invalid-state-use"),
        ],
        "{findings:?}"
    );
}

#[test]
fn finite_enum_cycle_propagates_divergence_to_its_callers() {
    let source = r#"#[repr(i8)]enum Flag{First=-7,Second=5,Third=101}#[allow(unconditional_recursion)]fn node_0(flag:Flag)->u8{match flag{Flag::First=>0,Flag::Second=>0,Flag::Third=>node_1(Flag::Second),}}pub fn probe_0_0()->u8{node_0(Flag::First)-1}pub fn probe_0_1()->u8{node_0(Flag::Second)-1}pub fn probe_0_2()->u8{node_0(Flag::Third)-1}#[allow(unconditional_recursion)]fn node_1(flag:Flag)->u8{match flag{Flag::First=>0,Flag::Second=>node_4(Flag::Third),Flag::Third=>0,}}pub fn probe_1_0()->u8{node_1(Flag::First)-1}pub fn probe_1_1()->u8{node_1(Flag::Second)-1}pub fn probe_1_2()->u8{node_1(Flag::Third)-1}#[allow(unconditional_recursion)]fn node_2(flag:Flag)->u8{match flag{Flag::First=>0,Flag::Second=>0,Flag::Third=>0,}}pub fn probe_2_0()->u8{node_2(Flag::First)-1}pub fn probe_2_1()->u8{node_2(Flag::Second)-1}pub fn probe_2_2()->u8{node_2(Flag::Third)-1}#[allow(unconditional_recursion)]fn node_3(flag:Flag)->u8{match flag{Flag::First=>0,Flag::Second=>0,Flag::Third=>0,}}pub fn probe_3_0()->u8{node_3(Flag::First)-1}pub fn probe_3_1()->u8{node_3(Flag::Second)-1}pub fn probe_3_2()->u8{node_3(Flag::Third)-1}#[allow(unconditional_recursion)]fn node_4(flag:Flag)->u8{match flag{Flag::First=>0,Flag::Second=>0,Flag::Third=>node_6(Flag::Third),}}pub fn probe_4_0()->u8{node_4(Flag::First)-1}pub fn probe_4_1()->u8{node_4(Flag::Second)-1}pub fn probe_4_2()->u8{node_4(Flag::Third)-1}#[allow(unconditional_recursion)]fn node_5(flag:Flag)->u8{match flag{Flag::First=>0,Flag::Second=>node_4(Flag::Third),Flag::Third=>node_0(Flag::First),}}pub fn probe_5_0()->u8{node_5(Flag::First)-1}pub fn probe_5_1()->u8{node_5(Flag::Second)-1}pub fn probe_5_2()->u8{node_5(Flag::Third)-1}#[allow(unconditional_recursion)]fn node_6(flag:Flag)->u8{match flag{Flag::First=>0,Flag::Second=>0,Flag::Third=>node_5(Flag::Second),}}pub fn probe_6_0()->u8{node_6(Flag::First)-1}pub fn probe_6_1()->u8{node_6(Flag::Second)-1}pub fn probe_6_2()->u8{node_6(Flag::Third)-1}"#;
    let findings = analyze(RustSource(source));
    let actual: Vec<_> = findings
        .iter()
        .filter(
            |finding| match (finding.item.starts_with("probe_"), finding.rule.as_str()) {
                (true, "invalid-state-use" | "unproven-precondition" | "analysis-incomplete") => {
                    true
                }
                _ => false,
            },
        )
        .map(|finding| (finding.item.as_str(), finding.rule.as_str()))
        .collect();
    let mut expected = vec![
        ("probe_0_0", "invalid-state-use"),
        ("probe_0_1", "invalid-state-use"),
        ("probe_1_0", "invalid-state-use"),
        ("probe_1_2", "invalid-state-use"),
        ("probe_2_0", "invalid-state-use"),
        ("probe_2_1", "invalid-state-use"),
        ("probe_2_2", "invalid-state-use"),
        ("probe_3_0", "invalid-state-use"),
        ("probe_3_1", "invalid-state-use"),
        ("probe_3_2", "invalid-state-use"),
        ("probe_4_0", "invalid-state-use"),
        ("probe_4_1", "invalid-state-use"),
        ("probe_5_0", "invalid-state-use"),
        ("probe_5_2", "invalid-state-use"),
        ("probe_6_0", "invalid-state-use"),
        ("probe_6_1", "invalid-state-use"),
    ];
    let mut actual = actual;
    actual.sort();
    expected.sort();
    assert_eq!(actual, expected, "{findings:?}");
}

#[test]
fn a_returning_call_before_a_recursive_branch_does_not_make_the_branch_return() {
    let source = "fn ready() -> u8 { 1 } fn repeat(flag: bool) -> u8 { if flag { let _ = ready(); repeat(flag) } else { 0 } } pub fn diverges() -> u8 { repeat(true) - 1 } pub fn returns() -> u8 { repeat(false) - 1 }";
    let findings = analyze(RustSource(source));
    let mut actual: Vec<_> = findings
        .iter()
        .filter_map(
            |finding| match (finding.item.as_str(), finding.rule.as_str()) {
                (
                    "diverges" | "returns",
                    "invalid-state-use" | "unproven-precondition" | "analysis-incomplete",
                ) => Some((finding.item.as_str(), finding.rule.as_str())),
                _ => None,
            },
        )
        .collect();
    actual.sort();
    assert_eq!(
        actual,
        vec![("returns", "invalid-state-use")],
        "{findings:?}"
    );
}

#[hegel::test(print_blob = true)]
fn discarded_recursive_results_still_gate_later_operations(tc: TestCase) {
    let amount = tc.draw(generators::default::<Amount>());
    let value = match amount {
        Amount::Zero => 0,
        Amount::Positive(value) => value.max(1),
    };
    let source = format!(
        "fn repeat(flag:bool)->u8{{if flag{{let _=repeat(flag);}}{value}}}pub fn probe()->u8{{repeat(true)-1}}pub fn base()->u8{{repeat(false)-1}}"
    );
    let findings = analyze(RustSource(&source));
    let probe: Vec<_> = findings
        .iter()
        .filter(|finding| {
            finding.item == "probe"
                && match finding.rule.as_str() {
                    "invalid-state-use" | "unproven-precondition" | "analysis-incomplete" => true,
                    _ => false,
                }
        })
        .collect();
    assert!(probe.is_empty(), "{source}\n{findings:?}");
    let invalid: Vec<_> = findings
        .iter()
        .filter(|finding| finding.item == "base" && finding.rule == "invalid-state-use")
        .collect();
    assert_eq!(
        invalid.len(),
        match amount {
            Amount::Zero => 1,
            Amount::Positive(_) => 0,
        },
        "{source}\n{findings:?}"
    );
    assert!(
        !findings.iter().any(|finding| finding.item == "base"
            && match finding.rule.as_str() {
                "unproven-precondition" | "analysis-incomplete" => true,
                _ => false,
            }),
        "{source}\n{findings:?}"
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum GenericRecursion {
    Direct,
    Mutual,
}

#[hegel::test(print_blob = true)]
fn fixed_generic_bindings_preserve_finite_recursive_proofs(tc: TestCase) {
    let (shape, amount) = tc.draw(generators::default::<(GenericRecursion, Amount)>());
    let value = match amount {
        Amount::Zero => 0,
        Amount::Positive(value) => value.max(1),
    };
    let functions = match shape {
        GenericRecursion::Direct => {
            format!("fn first<T>(flag:bool)->u8{{if flag{{first::<T>(false)}}else{{{value}}}}}")
        }
        GenericRecursion::Mutual => format!(
            "fn first<T>(flag:bool)->u8{{if flag{{second::<T>(false)}}else{{{value}}}}}fn second<T>(flag:bool)->u8{{first::<T>(flag)}}"
        ),
    };
    let source = format!("{functions}pub fn probe()->u8{{first::<()>(true)-1}}");
    let findings = analyze(RustSource(&source));
    let invalid: Vec<_> = findings
        .iter()
        .filter(|finding| finding.item == "probe" && finding.rule == "invalid-state-use")
        .collect();
    assert_eq!(
        invalid.len(),
        match amount {
            Amount::Zero => 1,
            Amount::Positive(_) => 0,
        },
        "{source}\n{findings:?}"
    );
    let gaps: Vec<_> = findings
        .iter()
        .filter(|finding| {
            finding.item == "probe"
                && (finding.rule == "unproven-precondition"
                    || finding.rule == "analysis-incomplete")
        })
        .collect();
    assert!(gaps.is_empty(), "{source}\n{findings:?}");
}

#[hegel::test(print_blob = true)]
fn expanding_generic_recursion_remains_explicitly_unsupported(tc: TestCase) {
    let shape = tc.draw(generators::default::<GenericRecursion>());
    let functions = match shape {
        GenericRecursion::Direct => {
            "fn first<T>(flag:bool)->u8{if flag{first::<Option<T>>(flag)}else{1}}"
        }
        GenericRecursion::Mutual => {
            "fn first<T>(flag:bool)->u8{if flag{second::<Option<T>>(flag)}else{1}}fn second<T>(flag:bool)->u8{first::<T>(flag)}"
        }
    };
    let source = format!("{functions}pub fn probe()->u8{{first::<()>(true)-1}}");
    let findings = analyze(RustSource(&source));
    let rules: Vec<_> = findings
        .iter()
        .filter(|finding| finding.item == "probe")
        .map(|finding| finding.rule.as_str())
        .collect();
    assert!(
        rules.contains(&"analysis-incomplete"),
        "{source}\n{findings:?}"
    );
    assert!(
        rules.contains(&"unproven-precondition"),
        "{source}\n{findings:?}"
    );
    assert!(
        !rules.contains(&"invalid-state-use"),
        "{source}\n{findings:?}"
    );
}
