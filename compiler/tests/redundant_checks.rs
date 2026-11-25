#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Established {
    Repeated,
    Opposite,
    Transitive,
    HelperReturn,
    Variant,
    UnrelatedMutation,
    RecursiveArgument,
}

#[hegel::test]
fn reports_checks_decided_by_incoming_facts(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Established>());
    let source = match case {
        Established::Repeated => {
            "pub fn run(values: &[u8], index: usize) -> Option<u8> { if index >= values.len() { return None; } if index < values.len() { Some(values[index]) } else { None } }"
        }
        Established::Opposite => {
            "pub fn run(values: &[u8], index: usize) -> Option<u8> { if index >= values.len() { return None; } if index >= values.len() { None } else { Some(values[index]) } }"
        }
        Established::Transitive => {
            "pub fn run(a: usize, b: usize, c: usize) -> usize { if a <= b && b < c { if a < c { 1 } else { 2 } } else { 3 } }"
        }
        Established::Variant => {
            "pub fn run(value: Option<u8>) -> u8 { if value.is_some() { if value.is_none() { 1 } else { 2 } } else { 3 } }"
        }
        Established::HelperReturn => {
            "fn length(text: &str) -> usize { text.len() } pub fn run(text: &str) -> usize { let end = length(text); if end <= text.len() { end } else { 0 } }"
        }
        Established::UnrelatedMutation => {
            "pub fn run(values: &[u8], other: &mut Vec<u8>, index: usize) -> Option<u8> { if index < values.len() { other.clear(); if index < values.len() { Some(values[index]) } else { None } } else { None } }"
        }
        Established::RecursiveArgument => {
            "pub fn run(value:u32,next:fn(u32)->u32)->u32{if value>0{run(value,next)}else{next(value)}}"
        }
    };
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "redundant-check")
        .collect();
    assert_eq!(findings.len(), 1, "{case:?}: {output}");
    let expected = match case {
        Established::Opposite | Established::Variant => "always false",
        Established::Repeated
        | Established::Transitive
        | Established::HelperReturn
        | Established::UnrelatedMutation
        | Established::RecursiveArgument => "always true",
    };
    assert!(
        findings[0]["primary"]["message"]
            .as_str()
            .expect("label")
            .contains(expected),
        "{output}"
    );
    assert_eq!(findings[0]["kind"], "lint", "{output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Necessary {
    FirstCheck,
    Mutated,
    PartialJoin,
    Loop,
    Macro,
    CompilerBounds,
}

#[hegel::test]
fn does_not_use_the_check_or_missing_facts_as_its_proof(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Necessary>());
    let source = match case {
        Necessary::FirstCheck => {
            "pub fn run(values: &[u8], index: usize) -> Option<u8> { if index < values.len() { Some(values[index]) } else { None } }"
        }
        Necessary::Mutated => {
            "pub fn run(values: &mut Vec<u8>, index: usize) -> Option<u8> { if index < values.len() { values.clear(); if index < values.len() { Some(values[index]) } else { None } } else { None } }"
        }
        Necessary::PartialJoin => {
            "pub fn run(a: usize, b: usize, choose: bool) -> usize { if choose { if a >= b { return 0; } } if a < b { 1 } else { 2 } }"
        }
        Necessary::Loop => {
            "pub fn run(mut value: usize) -> usize { while value > 0 { value -= 1; } value }"
        }
        Necessary::Macro => {
            "macro_rules! choose { ($a:expr, $b:expr) => { if $a < $b { 1 } else { 2 } }; } pub fn run(a: usize, b: usize) -> usize { if a < b { choose!(a, b) } else { 0 } }"
        }
        Necessary::CompilerBounds => "pub fn run() -> u8 { [1, 2][0] }",
    };
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "redundant-check")
        .collect();
    assert!(findings.is_empty(), "{case:?}: {output}");
}

#[test]
fn caller_evidence_applies_only_to_that_call() {
    let source = "fn read(values: &[u8], index: usize) -> Option<u8> { if index < values.len() { Some(values[index]) } else { None } } pub fn checked(values: &[u8], index: usize) -> Option<u8> { if index < values.len() { read(values, index) } else { None } } pub fn unchecked(values: &[u8], index: usize) -> Option<u8> { read(values, index) }";
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "redundant-check")
        .collect();
    assert_eq!(findings.len(), 1, "{output}");
    assert_eq!(findings[0]["item"], "checked", "{output}");
    assert_eq!(
        findings[0]["related"]
            .as_array()
            .expect("callee check")
            .len(),
        1,
        "{output}"
    );
    assert!(
        findings[0]["footers"]
            .as_array()
            .expect("notes")
            .iter()
            .any(|footer| footer["message"]
                .as_str()
                .expect("message")
                .contains("Other callers")),
        "{output}"
    );
}

#[test]
fn suppression_applies_to_the_redundant_check() {
    let source = "// shapelint: allow(redundant-check) Retain the explicit invariant check here.\npub fn run(a: usize, b: usize) -> usize { if a < b { if a < b { 1 } else { 2 } } else { 0 } }";
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "redundant-check")
        .collect();
    assert!(findings.is_empty(), "{output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum CalleeBoundary {
    Mutation,
    ConditionalPath,
    Macro,
}

#[hegel::test]
fn caller_facts_do_not_cross_unknown_callee_effects_or_paths(tc: hegel::TestCase) {
    let boundary = tc.draw(hegel::generators::default::<CalleeBoundary>());
    let source = match boundary {
        CalleeBoundary::Mutation => {
            "fn read(values: &mut Vec<u8>, index: usize) -> Option<u8> { values.clear(); if index < values.len() { Some(values[index]) } else { None } } pub fn run(values: &mut Vec<u8>, index: usize) -> Option<u8> { if index < values.len() { read(values, index) } else { None } }"
        }
        CalleeBoundary::ConditionalPath => {
            "fn read(values: &[u8], index: usize, choose: bool) -> Option<u8> { if choose { if index < values.len() { return Some(values[index]); } } None } pub fn run(values: &[u8], index: usize, choose: bool) -> Option<u8> { if index < values.len() { read(values, index, choose) } else { None } }"
        }
        CalleeBoundary::Macro => {
            "macro_rules! generate { () => { fn read(values: &[u8], index: usize) -> Option<u8> { if index < values.len() { Some(values[index]) } else { None } } }; } generate!(); pub fn run(values: &[u8], index: usize) -> Option<u8> { if index < values.len() { read(values, index) } else { None } }"
        }
    };
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "redundant-check")
        .collect();
    assert!(findings.is_empty(), "{boundary:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum RecursiveValue {
    Predicate,
    Child,
    FreshLocal,
}

#[hegel::test]
fn recursive_calls_do_not_inherit_the_previous_invocations_local_facts(tc: hegel::TestCase) {
    let value = tc.draw(hegel::generators::default::<RecursiveValue>());
    let source = match value {
        RecursiveValue::Predicate => {
            "pub fn walk(probe:fn(u32)->bool,value:u32)->u32{if probe(value){walk(probe,value.wrapping_sub(1))}else{value}}"
        }
        RecursiveValue::Child => {
            "pub struct Node{pub name:String,pub child:Option<Box<Node>>}pub fn walk(node:&Node)->usize{if node.name==\"not\"{match &node.child{Some(child)=>walk(child),None=>0}}else{0}}"
        }
        RecursiveValue::FreshLocal => {
            "pub fn walk(next:fn()->u32)->u32{let generation=next();if generation==0{walk(next)}else{generation}}"
        }
    };
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "redundant-check")
        .collect();
    assert!(findings.is_empty(), "{value:?}: {output}");
}
