#![feature(rustc_private)]

use std::fmt::{self, Write};
use std::process::Command;

use hegel::generators::{self, BoxedPrintableGenerator, DefaultGenerator};
use hegel::{PrintableGenerator, TestCase};
use serde::Deserialize;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Choice {
    First,
    Second,
}

impl Choice {
    fn index(self) -> usize {
        match self {
            Self::First => 0,
            Self::Second => 1,
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Argument {
    Keep,
    Flip,
    Set(Choice),
}

impl Argument {
    fn apply(self, input: Choice) -> Choice {
        match (self, input) {
            (Self::Keep, input) | (Self::Set(input), _) => input,
            (Self::Flip, Choice::First) => Choice::Second,
            (Self::Flip, Choice::Second) => Choice::First,
        }
    }
}

impl fmt::Display for Argument {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Keep => "flag",
            Self::Flip => "!flag",
            Self::Set(Choice::First) => "false",
            Self::Set(Choice::Second) => "true",
        })
    }
}

#[derive(Clone, Copy, Debug)]
struct Function(usize);

#[derive(Clone, Copy, Debug)]
struct Call {
    function: Function,
    argument: Argument,
}

fn calls(last: usize) -> impl PrintableGenerator<Call> {
    hegel::compose!(|tc| {
        Call {
            function: Function(tc.draw(generators::integers::<usize>().max_value(last))),
            argument: tc.draw(generators::default::<Argument>()),
        }
    })
}

impl fmt::Display for Call {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "node_{}({})", self.function.0, self.argument)
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Shape {
    Value(u8),
    Forward,
    Branch,
    Sequence,
}

#[derive(Clone, Copy, Debug)]
enum Node {
    Value(u8),
    Forward(Call),
    Branch { first: Call, second: Call },
    Sequence { first: Call, second: Call },
}

#[derive(Debug)]
struct Acyclic {
    base: u8,
    nodes: Vec<Node>,
}

impl DefaultGenerator for Acyclic {
    type Generator = BoxedPrintableGenerator<'static, Self>;

    fn default_generator() -> Self::Generator {
        hegel::compose!(|tc| {
            let base = tc.draw(generators::integers::<u8>());
            let shapes = tc.draw(generators::vecs(generators::default::<Shape>()));
            let nodes = shapes
                .into_iter()
                .enumerate()
                .map(|(last, shape)| match shape {
                    Shape::Value(value) => Node::Value(value),
                    Shape::Forward => Node::Forward(tc.draw(calls(last))),
                    Shape::Branch => Node::Branch {
                        first: tc.draw(calls(last)),
                        second: tc.draw(calls(last)),
                    },
                    Shape::Sequence => Node::Sequence {
                        first: tc.draw(calls(last)),
                        second: tc.draw(calls(last)),
                    },
                })
                .collect();
            Self { base, nodes }
        })
        .boxed_printable()
    }
}

impl Acyclic {
    fn values(&self) -> Vec<[u8; 2]> {
        let mut values = vec![[self.base; 2]];
        for node in &self.nodes {
            let evaluate = |choice: Choice| {
                let call =
                    |call: Call| values[call.function.0][call.argument.apply(choice).index()];
                match (node, choice) {
                    (Node::Value(value), _) => *value,
                    (Node::Forward(target), _) => call(*target),
                    (Node::Branch { first, .. }, Choice::First) => call(*first),
                    (Node::Branch { second, .. }, Choice::Second)
                    | (Node::Sequence { second, .. }, _) => call(*second),
                }
            };
            let result = [evaluate(Choice::First), evaluate(Choice::Second)];
            values.push(result);
        }
        values
    }

    fn declarations(&self) -> Vec<String> {
        let mut declarations = vec![format!("fn node_0(_flag:bool)->u8{{{}}}", self.base)];
        let nodes = self.nodes.iter().enumerate();
        for (index, node) in nodes {
            let body = match node {
                Node::Value(value) => value.to_string(),
                Node::Forward(call) => call.to_string(),
                Node::Branch { first, second } => format!("if flag {{{second}}}else{{{first}}}"),
                Node::Sequence { first, second } => format!("let _={first};{second}"),
            };
            declarations.push(format!(
                "fn node_{}(flag:bool)->u8{{let _=flag;{body}}}",
                index + 1
            ));
        }
        declarations
    }
}

#[derive(Debug)]
struct Recursive {
    values: Vec<u8>,
    successors: Vec<Function>,
}

impl DefaultGenerator for Recursive {
    type Generator = BoxedPrintableGenerator<'static, Self>;

    fn default_generator() -> Self::Generator {
        hegel::compose!(|tc| {
            let values = tc.draw(generators::vecs(generators::integers::<u8>()).min_size(1));
            let successors = tc.draw(
                generators::vecs(generators::integers::<usize>().max_value(values.len() - 1))
                    .min_size(values.len())
                    .max_size(values.len()),
            );
            Self {
                values,
                successors: successors.into_iter().map(Function).collect(),
            }
        })
        .boxed_printable()
    }
}

impl Recursive {
    fn values(&self) -> Vec<[u8; 2]> {
        self.values
            .iter()
            .zip(&self.successors)
            .map(|(value, successor)| [self.values[successor.0], *value])
            .collect()
    }

    fn declarations(&self) -> Vec<String> {
        self.values
            .iter()
            .zip(&self.successors)
            .enumerate()
            .map(|(index, (value, successor))| {
                format!(
                    "fn node_{index}(flag:bool)->u8{{if flag{{{value}}}else{{node_{}(true)}}}}",
                    successor.0
                )
            })
            .collect()
    }
}

#[derive(Debug, Deserialize)]
struct Finding {
    rule: String,
    item: String,
}

fn analyze(input: &shapelint::SourceInput) -> Vec<Finding> {
    let directory = tempfile::tempdir().expect("source directory");
    let path = directory.path().join(input.name.as_ref());
    std::fs::write(&path, input.as_ref()).expect("model source");
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
        "{}\n{}",
        input.as_ref(),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{}\n{}",
        input.as_ref(),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("diagnostic encoding")
        .lines()
        .map(|line| serde_json::from_str(line).expect("diagnostic"))
        .collect()
}

fn check_graph(declarations: Vec<String>, values: Vec<[u8; 2]>) {
    let mut probes = String::new();
    let mut expected = Vec::new();
    let cases = values.iter().enumerate();
    for (function, outcomes) in cases {
        let outcomes = outcomes.iter().enumerate();
        for (argument, value) in outcomes {
            let item = format!("probe_{function}_{argument}");
            let literal = match argument {
                0 => "false",
                1 => "true",
                _ => unreachable!("the model has two states"),
            };
            write!(
                probes,
                "pub fn {item}()->u8{{node_{function}({literal})-1}}"
            )
            .expect("write source");
            match value {
                0 => expected.push(item),
                _ => {}
            }
        }
    }
    expected.sort();
    let source = format!("{}{probes}", declarations.concat());
    let input = shapelint::SourceInput::try_new("model.rs", source.clone())
        .expect("model source fits compiler offsets");
    let findings = analyze(&input);
    let mut invalid = Vec::new();
    for finding in &findings {
        match (finding.item.starts_with("probe_"), finding.rule.as_str()) {
            (true, "invalid-state-use") => invalid.push(finding.item.clone()),
            (true, "unproven-precondition" | "analysis-incomplete") => {
                panic!("finite model must decide every probe: {finding:?}\n{source}")
            }
            _ => {}
        }
    }
    invalid.sort();
    assert_eq!(invalid, expected, "{source}\n{findings:#?}");
}

#[hegel::test(print_blob = true)]
fn generated_acyclic_calls_match_the_execution_model(tc: TestCase) {
    let graph = tc.draw(generators::default::<Acyclic>());
    check_graph(graph.declarations(), graph.values());
}

#[hegel::test(print_blob = true)]
fn declaration_order_does_not_change_finite_call_results(tc: TestCase) {
    let graph = tc.draw(generators::default::<Acyclic>());
    let mut declarations = graph.declarations();
    declarations.reverse();
    check_graph(declarations, graph.values());
}

#[hegel::test(print_blob = true)]
fn recursive_components_match_the_finite_execution_model(tc: TestCase) {
    let graph = tc.draw(generators::default::<Recursive>());
    check_graph(graph.declarations(), graph.values());
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Location {
    Subject,
    Other,
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Subject => "subject",
            Self::Other => "other",
        })
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Mutation {
    Write { location: Location, value: u8 },
    Call(Location),
    Alias(Location),
}

#[derive(Clone, Copy, Debug)]
enum Knowledge {
    Zero,
    Nonzero,
    Unknown,
}

#[hegel::test(print_blob = true)]
fn generated_mutation_histories_invalidate_only_the_affected_value(tc: TestCase) {
    let mutations = tc.draw(generators::vecs(generators::default::<Mutation>()));
    let mut subject_binding = "";
    let mut other_binding = "";
    for mutation in &mutations {
        let location = match mutation {
            Mutation::Write { location, .. }
            | Mutation::Call(location)
            | Mutation::Alias(location) => location,
        };
        match location {
            Location::Subject => subject_binding = "mut ",
            Location::Other => other_binding = "mut ",
        }
    }
    let mut knowledge = Knowledge::Nonzero;
    let mut source = format!(
        "pub fn run({subject_binding}subject:u8,{other_binding}other:u8,mutate:fn(&mut u8),observe:fn(u8))->u8{{\
         let _=mutate;observe(subject);observe(other);if subject>0{{",
    );
    for mutation in mutations {
        match mutation {
            Mutation::Write { location, value } => {
                write!(source, "{location}={value};").expect("write source");
                knowledge = match (location, value) {
                    (Location::Subject, 0) => Knowledge::Zero,
                    (Location::Subject, _) => Knowledge::Nonzero,
                    (Location::Other, _) => knowledge,
                };
            }
            Mutation::Call(location) => {
                write!(source, "mutate(&mut {location});").expect("write source");
                knowledge = match location {
                    Location::Subject => Knowledge::Unknown,
                    Location::Other => knowledge,
                };
            }
            Mutation::Alias(location) => {
                write!(source, "{{let alias=&mut {location};mutate(alias);}}")
                    .expect("write source");
                knowledge = match location {
                    Location::Subject => Knowledge::Unknown,
                    Location::Other => knowledge,
                };
            }
        }
        source.push_str("observe(subject);observe(other);");
    }
    source.push_str("if subject>0{1}else{0}}else{0}}");
    let input = shapelint::SourceInput::try_new("model.rs", source.clone())
        .expect("model source fits compiler offsets");
    let findings = analyze(&input);
    let redundant: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "redundant-check" && finding.item == "run")
        .collect();
    let expected = match knowledge {
        Knowledge::Zero | Knowledge::Nonzero => 1,
        Knowledge::Unknown => 0,
    };
    assert_eq!(redundant.len(), expected, "{source}\n{findings:#?}");
}
