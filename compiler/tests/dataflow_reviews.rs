#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ReturnShape {
    Direct,
    Branches,
    Helper,
}

#[hegel::test]
fn reports_result_functions_without_an_error_return(tc: hegel::TestCase) {
    let shape = tc.draw(hegel::generators::default::<ReturnShape>());
    let source = match shape {
        ReturnShape::Direct => "pub fn run(value: u32) -> Result<u32, ()> { Ok(value) }",
        ReturnShape::Branches => {
            "pub fn run(value: u32) -> Result<u32, ()> { if value > 0 { Ok(value) } else { Ok(1) } }"
        }
        ReturnShape::Helper => {
            "fn ready(value: u32) -> Result<u32, ()> { Ok(value) } pub fn run(value: u32) -> Result<u32, ()> { ready(value) }"
        }
    };
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unnecessary-fallibility" && finding["item"] == "run"
        })
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "{shape:?}: expected unnecessary-fallibility: {output}"
    );
}

#[test]
fn optional_parameters_keep_mixed_callers() {
    let source = "fn read(value: Option<u8>) -> u8 { match value { Some(value) => value, None => 0 } } pub fn checked(value: u8) -> u8 { read(Some(value)) } pub fn unchecked(value: Option<u8>) -> u8 { read(value) }";
    let output = support::analyze(source, &[]).expect("analysis");
    assert!(!output.contains("unnecessary-optionality"), "{output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Mutation {
    Argument,
    Field,
}

#[hegel::test]
fn connects_a_stale_check_to_the_mutation_and_consumer(tc: hegel::TestCase) {
    let mutation = tc.draw(hegel::generators::default::<Mutation>());
    let source = match mutation {
        Mutation::Argument => {
            "pub fn run(values: &mut Vec<u8>, index: usize) -> Option<u8> { if index < values.len() { values.clear(); Some(values[index]) } else { None } }"
        }
        Mutation::Field => {
            "pub struct State { pub values: Vec<u8> } pub fn run(state: &mut State, index: usize) -> Option<u8> { if index < state.values.len() { state.values.clear(); Some(state.values[index]) } else { None } }"
        }
    };
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "invalidated-validation")
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "{mutation:?}: expected invalidated-validation: {output}"
    );
    let message = findings[0]["primary"]["message"]
        .as_str()
        .expect("condition");
    assert!(
        message.contains("index") && message.contains("values") && !message.contains("unknown"),
        "{mutation:?}: {output}"
    );
    assert!(
        !findings[0]["related"]
            .as_array()
            .expect("mutation location")
            .is_empty(),
        "{output}"
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Construction {
    Concrete,
    Derived,
}

#[hegel::test]
fn reports_a_boolean_that_duplicates_option_presence(tc: hegel::TestCase) {
    let construction = tc.draw(hegel::generators::default::<Construction>());
    let constructor = match construction {
        Construction::Concrete => {
            "pub fn new(value: u8, ready: bool) -> Self { if ready { Self { ready: true, value: Some(value) } } else { Self { ready: false, value: None } } }"
        }
        Construction::Derived => {
            "pub fn new(value: Option<u8>) -> Self { Self { ready: value.is_some(), value } }"
        }
    };
    let source = format!(
        "pub struct State {{ ready: bool, value: Option<u8> }} impl State {{ {constructor} pub fn read(&self) -> Option<u8> {{ if self.ready {{ self.value }} else {{ None }} }} }}"
    );
    let output = support::analyze(&source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "duplicated-state")
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "{construction:?}: expected duplicated-state: {output}"
    );
    let message = findings[0]["primary"]["message"]
        .as_str()
        .expect("relation");
    assert!(
        message.contains("ready") && message.contains("value"),
        "{output}"
    );
}

#[test]
fn reports_an_unchanged_check_inside_a_loop() {
    let source = "pub fn run(values: &[u8], index: usize, mut remaining: usize, effect: fn(u8)) { while remaining > 0 { if index < values.len() { effect(values[index]); } remaining -= 1; } }";
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "loop-invariant-check")
        .collect();
    assert_eq!(findings.len(), 1, "expected loop-invariant-check: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Branch {
    Ordering,
    Equality,
    Tuple,
}

#[hegel::test]
fn reports_equivalent_results_from_different_control_flow(tc: hegel::TestCase) {
    let branch = tc.draw(hegel::generators::default::<Branch>());
    let source = match branch {
        Branch::Ordering => {
            "pub fn first(a: u32, b: u32) -> u32 { if a < b { a } else { b } } pub fn second(a: u32, b: u32) -> u32 { if b <= a { b } else { a } }"
        }
        Branch::Equality => {
            "pub fn first(a: u8, b: u8) -> u8 { if a != b { a } else { b } } pub fn second(a: u8, b: u8) -> u8 { if a == b { b } else { a } }"
        }
        Branch::Tuple => {
            "pub fn first(a: u64, b: u64) -> (u64, u64) { if a < b { (a, b) } else { (b, a) } } pub fn second(a: u64, b: u64) -> (u64, u64) { if b <= a { (b, a) } else { (a, b) } }"
        }
    };
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "equivalent-implementation")
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "expected equivalent-implementation: {output}"
    );
    assert_eq!(
        findings[0]["related"]
            .as_array()
            .expect("other implementation")
            .len(),
        1,
        "{output}"
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Uncertain {
    ErrorReturn,
    UnknownReturn,
    RecursiveReturn,
    TraitSignature,
    TailReturn,
    UnknownOption,
    FreshCheck,
    Rechecked,
    UnrelatedMutation,
    PublicState,
    MutableState,
    IndependentState,
    UnknownProducer,
    EscapedState,
    ChangingLoop,
    MutatingLoop,
    EffectfulEquivalent,
    PanickingEquivalent,
    LoopingEquivalent,
    RecursiveEquivalent,
    DifferentResults,
    DifferentTypes,
}

#[hegel::test]
fn uncertainty_and_different_behavior_do_not_justify_a_review(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Uncertain>());
    let (rule, source) = match case {
        Uncertain::ErrorReturn => (
            "unnecessary-fallibility",
            "pub fn run(value: u32) -> Result<u32, ()> { if value > 0 { Ok(value) } else { Err(()) } }",
        ),
        Uncertain::UnknownReturn => (
            "unnecessary-fallibility",
            "pub fn run(make: fn() -> Result<u32, ()>) -> Result<u32, ()> { make() }",
        ),
        Uncertain::RecursiveReturn => (
            "unnecessary-fallibility",
            "pub fn run(value: u32) -> Result<u32, ()> { if value > 0 { run(value - 1) } else { Ok(0) } }",
        ),
        Uncertain::TraitSignature => (
            "unnecessary-fallibility",
            "pub struct State; pub trait Read { fn read(&self) -> Result<u32, ()>; } impl Read for State { fn read(&self) -> Result<u32, ()> { Ok(0) } }",
        ),
        Uncertain::TailReturn => (
            "unnecessary-fallibility",
            "#![feature(explicit_tail_calls)] #![allow(incomplete_features)] fn finish(value: u32) -> Result<u32, ()> { if value > 0 { Err(()) } else { Ok(0) } } pub fn run(value: u32) -> Result<u32, ()> { if value == 0 { Ok(0) } else { become finish(value) } }",
        ),
        Uncertain::UnknownOption => (
            "unnecessary-optionality",
            "fn read(value: Option<u8>) -> u8 { match value { Some(value) => value, None => 0 } } pub fn run(value: Option<u8>) -> u8 { read(value) }",
        ),
        Uncertain::FreshCheck => (
            "invalidated-validation",
            "pub fn run(values: &mut Vec<u8>, index: usize) -> Option<u8> { values.clear(); if index < values.len() { Some(values[index]) } else { None } }",
        ),
        Uncertain::Rechecked => (
            "invalidated-validation",
            "pub fn run(values: &mut Vec<u8>, index: usize) -> Option<u8> { if index < values.len() { values.clear(); if index < values.len() { return Some(values[index]); } } None }",
        ),
        Uncertain::UnrelatedMutation => (
            "invalidated-validation",
            "pub fn run(values: &[u8], other: &mut Vec<u8>, index: usize) -> Option<u8> { if index < values.len() { other.clear(); Some(values[index]) } else { None } }",
        ),
        Uncertain::PublicState => (
            "duplicated-state",
            "pub struct State { pub ready: bool, pub value: Option<u8> } pub fn make(value: Option<u8>) -> State { State { ready: value.is_some(), value } }",
        ),
        Uncertain::MutableState => (
            "duplicated-state",
            "pub struct State { ready: bool, value: Option<u8> } impl State { pub fn new(value: Option<u8>) -> Self { Self { ready: value.is_some(), value } } pub fn set_ready(&mut self, ready: bool) { self.ready = ready; } pub fn read(&self) -> Option<u8> { if self.ready { self.value } else { None } } }",
        ),
        Uncertain::IndependentState => (
            "duplicated-state",
            "pub struct State { ready: bool, value: Option<u8> } impl State { pub fn new(ready: bool, value: Option<u8>) -> Self { Self { ready, value } } pub fn read(&self) -> Option<u8> { if self.ready { self.value } else { None } } }",
        ),
        Uncertain::UnknownProducer => (
            "duplicated-state",
            "pub struct State { ready: bool, value: Option<u8> } impl State { pub fn new(value: Option<u8>) -> Self { Self { ready: value.is_some(), value } } pub fn make(make: fn() -> Self) -> Self { make() } pub fn read(&self) -> Option<u8> { if self.ready { self.value } else { None } } }",
        ),
        Uncertain::EscapedState => (
            "duplicated-state",
            "pub struct State { ready: bool, value: Option<u8> } impl State { pub fn new(value: Option<u8>) -> Self { Self { ready: value.is_some(), value } } pub fn edit(&mut self, edit: fn(&mut bool)) { edit(&mut self.ready); } pub fn read(&self) -> Option<u8> { if self.ready { self.value } else { None } } }",
        ),
        Uncertain::MutatingLoop => (
            "loop-invariant-check",
            "pub fn run(values: &mut Vec<u8>, index: usize, mut remaining: usize, effect: fn(&mut Vec<u8>)) { while remaining > 0 { if index < values.len() { effect(values); } remaining -= 1; } }",
        ),
        Uncertain::ChangingLoop => (
            "loop-invariant-check",
            "pub fn run(values: &[u8], mut index: usize, mut remaining: usize, effect: fn(u8)) { while remaining > 0 { if index < values.len() { effect(values[index]); } index = index.wrapping_add(1); remaining -= 1; } }",
        ),
        Uncertain::EffectfulEquivalent => (
            "equivalent-implementation",
            "pub fn first(a: u32, b: u32, effect: fn()) -> u32 { effect(); if a < b { a } else { b } } pub fn second(a: u32, b: u32, effect: fn()) -> u32 { let _ = effect; if b <= a { b } else { a } }",
        ),
        Uncertain::PanickingEquivalent => (
            "equivalent-implementation",
            "pub fn first(a: u32, b: u32) -> u32 { assert!(a > 0); if a < b { a } else { b } } pub fn second(a: u32, b: u32) -> u32 { if b <= a { b } else { a } }",
        ),
        Uncertain::LoopingEquivalent => (
            "equivalent-implementation",
            "pub fn first(a: u32) -> u32 { if a > 0 { loop { std::hint::spin_loop(); } } a } pub fn second(a: u32) -> u32 { a }",
        ),
        Uncertain::RecursiveEquivalent => (
            "equivalent-implementation",
            "pub fn first(a: u32) -> u32 { if a > 0 { let _ = first(a); } a } pub fn second(a: u32) -> u32 { a }",
        ),
        Uncertain::DifferentResults => (
            "equivalent-implementation",
            "pub fn first(a: u32, b: u32) -> u32 { if a < b { a } else { b } } pub fn second(a: u32, b: u32) -> u32 { if b <= a { a } else { b } }",
        ),
        Uncertain::DifferentTypes => (
            "equivalent-implementation",
            "pub fn first(a: u32, b: u32) -> u32 { if a < b { a } else { b } } pub fn second(a: u64, b: u64) -> u64 { if b <= a { b } else { a } }",
        ),
    };
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == rule)
        .collect();
    assert!(findings.is_empty(), "{case:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Review {
    Fallibility,
    Optionality,
    Validation,
    State,
    Loop,
    Equivalence,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Boundary {
    Macro,
    Suppression,
}

#[hegel::test]
fn generated_and_suppressed_reviews_are_not_reported(tc: hegel::TestCase) {
    let (review, boundary) = tc.draw(hegel::generators::default::<(Review, Boundary)>());
    let (rule, source) = match review {
        Review::Fallibility => (
            "unnecessary-fallibility",
            "pub fn run(value: u32) -> Result<u32, ()> { Ok(value) }",
        ),
        Review::Optionality => (
            "unnecessary-optionality",
            "fn read(value: Option<u8>) -> u8 { match value { Some(value) => value, None => 0 } } pub fn run(value: u8) -> u8 { read(Some(value)) }",
        ),
        Review::Validation => (
            "invalidated-validation",
            "pub fn run(values: &mut Vec<u8>, index: usize) -> Option<u8> { if index < values.len() { values.clear(); Some(values[index]) } else { None } }",
        ),
        Review::State => (
            "duplicated-state",
            "pub struct State { ready: bool, value: Option<u8> } impl State { pub fn new(value: Option<u8>) -> Self { Self { ready: value.is_some(), value } } pub fn read(&self) -> Option<u8> { if self.ready { self.value } else { None } } }",
        ),
        Review::Loop => (
            "loop-invariant-check",
            "pub fn run(values: &[u8], index: usize, mut remaining: usize, effect: fn(u8)) { while remaining > 0 { if index < values.len() { effect(values[index]); } remaining -= 1; } }",
        ),
        Review::Equivalence => (
            "equivalent-implementation",
            "pub fn first(a: u32, b: u32) -> u32 { if a < b { a } else { b } } pub fn second(a: u32, b: u32) -> u32 { if b <= a { b } else { a } }",
        ),
    };
    let source = match boundary {
        Boundary::Macro => {
            format!("macro_rules! generate {{ () => {{ {source} }}; }} generate!();")
        }
        Boundary::Suppression => {
            format!("// shapelint: allow({rule}) Retain this boundary.\n{source}")
        }
    };
    let output = support::analyze(&source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == rule)
        .collect();
    assert!(findings.is_empty(), "{review:?}, {boundary:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum OptionalCallers {
    AllPresent,
    DeadPresent,
    DeadCall,
    Callback,
    IndirectArgument,
    Method,
    SometimesAbsent,
    Escaped,
    Exported,
    SameVariantName,
}

#[hegel::test]
fn optionality_requires_all_callers_of_a_private_option(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<OptionalCallers>());
    let read = "fn read(value: Option<u8>) -> u8 { match value { Some(n) => n, None => 0 } }";
    let calls = "pub fn one() -> u8 { read(Some(1)) } pub fn two() -> u8 { read(Some(2)) }";
    let (source, count) = match case {
        OptionalCallers::DeadPresent => (format!("{read}\npub fn run()->u8 {{ if false {{read(Some(1))}} else {{read(Some(2))}} }}"),1),
        OptionalCallers::DeadCall => (format!("{read}\n{calls}\npub fn dead() {{ if false {{read(None);}} }}"), 0),
        OptionalCallers::Callback => (format!("{read}\n{calls}\npub fn apply(f:fn(Option<u8>)->u8)->u8 {{ f(Some(2)) }} pub fn go()->u8 {{ apply(read) }}"), 0),
        OptionalCallers::IndirectArgument => (format!("{read}\n{calls}\npub trait Source {{ fn get()->Option<u8>; }} struct Item; impl Source for Item {{ fn get()->Option<u8>{{Some(1)}} }} pub fn go()->u8 {{ read(Item::get()) }}"), 0),
        OptionalCallers::Method => ("pub struct Input; impl Input { fn read(&self, value:Option<u8>)->u8 {match value { Some(n)=>n, None=>0 }} } pub fn one(v:&Input)->u8 {v.read(Some(1))} pub fn two(v:&Input)->u8 {Input::read(v, Some(2))}".into(),1),
        OptionalCallers::AllPresent => (format!("{read}\n{calls}"), 1),
        OptionalCallers::SometimesAbsent => (format!("{read}\n{calls}\npub fn zero()->u8 {{ read(None) }}"), 0),
        OptionalCallers::Escaped => (format!("{read}\n{calls}\npub fn escape()->fn(Option<u8>)->u8 {{read}}"), 0),
        OptionalCallers::Exported => (format!("pub {read}\n{calls}"), 0),
        OptionalCallers::SameVariantName => ("pub enum Choice { Some(u8), Other } fn read(value: Choice)->u8 { match value {Choice::Some(n)=>n, Choice::Other=>0} } pub fn run()->u8 {read(Choice::Some(1))}".into(), 0),
    };
    let output = support::analyze(&source, &[]).expect("driver analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("diagnostic"))
        .filter(|row: &serde_json::Value| row["rule"] == "unnecessary-optionality")
        .collect();
    assert_eq!(findings.len(), count, "{case:?}: {output}");
    for finding in findings {
        assert!(
            finding["item"]
                .as_str()
                .expect("function")
                .ends_with("read")
        );
        assert_eq!(finding["line"], 1);
        let wrappers: Vec<_> = finding["related"]
            .as_array()
            .expect("caller evidence")
            .iter()
            .map(|caller| {
                let span = &caller["label"]["span"];
                &source[span["start"].as_u64().expect("start") as usize
                    ..span["end"].as_u64().expect("end") as usize]
            })
            .collect();
        assert_eq!(wrappers, ["Some(1)", "Some(2)"]);
    }
}
