#![feature(rustc_private)]

mod support;

use std::error::Error;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Method {
    IsSome,
    IsNone,
    IsSomeAnd,
    IsNoneOr,
    IsOk,
    IsErr,
    IsOkAnd,
    OptionDefault,
    OptionOr,
    OptionElse,
    ResultDefault,
    ResultOr,
    ResultElse,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Form {
    Method,
    Associated,
    Alias,
    FunctionValue,
    Closure,
    Async,
    MacroArgument,
    Generated,
    DerivedImplementation,
    Suppressed,
}

struct Call {
    owner: &'static str,
    name: &'static str,
    arguments: &'static str,
    receiver: &'static str,
    rule: &'static str,
}

#[hegel::test]
fn method_identity_alone_does_not_imply_a_lost_payload_or_error(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let (method, form) = tc.draw(hegel::generators::default::<(Method, Form)>());
        let Call {
            owner,
            name,
            arguments,
            receiver,
            rule,
        } = match method {
            Method::IsSome => Call {
                owner: "Option<u8>",
                name: "is_some",
                arguments: "",
                receiver: "&value",
                rule: "option-result-predicate",
            },
            Method::IsNone => Call {
                owner: "Option<u8>",
                name: "is_none",
                arguments: "",
                receiver: "&value",
                rule: "option-result-predicate",
            },
            Method::IsSomeAnd => Call {
                owner: "Option<u8>",
                name: "is_some_and",
                arguments: "|v| v > 0",
                receiver: "value",
                rule: "option-result-predicate",
            },
            Method::IsNoneOr => Call {
                owner: "Option<u8>",
                name: "is_none_or",
                arguments: "|v| v > 0",
                receiver: "value",
                rule: "option-result-predicate",
            },
            Method::IsOk => Call {
                owner: "Result<u8, ()>",
                name: "is_ok",
                arguments: "",
                receiver: "&value",
                rule: "option-result-predicate",
            },
            Method::IsErr => Call {
                owner: "Result<u8, u8>",
                name: "is_err",
                arguments: "",
                receiver: "&value",
                rule: "option-result-predicate",
            },
            Method::IsOkAnd => Call {
                owner: "Result<u8, ()>",
                name: "is_ok_and",
                arguments: "|v| v > 0",
                receiver: "value",
                rule: "option-result-predicate",
            },
            Method::OptionDefault => Call {
                owner: "Option<u8>",
                name: "unwrap_or_default",
                arguments: "",
                receiver: "value",
                rule: "silent-default",
            },
            Method::OptionOr => Call {
                owner: "Option<u8>",
                name: "unwrap_or",
                arguments: "0",
                receiver: "value",
                rule: "silent-default",
            },
            Method::OptionElse => Call {
                owner: "Option<u8>",
                name: "unwrap_or_else",
                arguments: "|| 0",
                receiver: "value",
                rule: "silent-default",
            },
            Method::ResultDefault => Call {
                owner: "Result<u8, ()>",
                name: "unwrap_or_default",
                arguments: "",
                receiver: "value",
                rule: "silent-default",
            },
            Method::ResultOr => Call {
                owner: "Result<u8, ()>",
                name: "unwrap_or",
                arguments: "0",
                receiver: "value",
                rule: "silent-default",
            },
            Method::ResultElse => Call {
                owner: "Result<u8, ()>",
                name: "unwrap_or_else",
                arguments: "|_| 0",
                receiver: "value",
                rule: "silent-default",
            },
        };
        let call = format!("value.{name}({arguments})");
        let source = match form {
            Form::Method => format!("pub fn run(value: {owner}) {{ let _ = {call}; }}"),
            Form::Associated => format!(
                "pub fn run(value: {owner}) {{ let _ = <{owner}>::{name}({receiver}, {arguments}); }}"
            ),
            Form::Alias => format!(
                "pub type Input = {owner}; pub fn run(value: Input) {{ let _ = Input::{name}({receiver}, {arguments}); }}"
            ),
            Form::FunctionValue => format!(
                "pub fn run(value: {owner}) {{ let method = <{owner}>::{name}; let _ = method({receiver}, {arguments}); }}"
            ),
            Form::Closure => {
                format!("pub fn run(value: {owner}) {{ let run = || {call}; let _ = run(); }}")
            }
            Form::Async => format!("pub async fn run(value: {owner}) {{ let _ = {call}; }}"),
            Form::MacroArgument => {
                format!("pub fn run(value: {owner}) {{ assert!({{ let _ = {call}; true }}); }}")
            }
            Form::Generated => format!(
                "macro_rules! generated {{ ($value:expr) => {{ $value.{name}({arguments}) }} }} pub fn run(value: {owner}) {{ let _ = generated!(value); }}"
            ),
            Form::DerivedImplementation => format!(
                "pub trait Run {{ fn run(value: {owner}); }} pub struct Runner; #[automatically_derived] impl Run for Runner {{ fn run(value: {owner}) {{ let _ = {call}; }} }}"
            ),
            Form::Suppressed => format!(
                "// shapelint: allow({rule})\npub fn run(value: {owner}) {{ let _ = {call}; }}"
            ),
        };
        let output = support::analyze(&source, &[])?;
        let findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        let findings: Vec<_> = findings
            .iter()
            .filter(|finding| finding["rule"] == rule)
            .collect();
        assert!(findings.is_empty(), "{method:?} {form:?}: {findings:?}");
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[test]
fn presence_queries_can_discard_the_value_for_unit_and_non_unit_variants() {
    let source = "pub fn run(option: Option<()>, result: Result<(), u8>) { let _ = option.is_some(); let _ = option.is_none(); let _ = result.is_ok(); let _ = result.is_err(); }";
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "option-result-predicate")
        .collect();
    assert!(findings.is_empty(), "{output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Lookalike {
    Inherent,
    ShadowedOption,
    TraitOnOption,
}

#[hegel::test]
fn unrelated_methods_are_not_standard_library_operations(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let case = tc.draw(hegel::generators::default::<Lookalike>());
        let source = match case {
            Lookalike::Inherent => {
                "pub struct Custom; impl Custom { pub fn is_some(&self) -> u8 { 1 } pub fn unwrap_or_default(&self) -> u8 { 1 } } pub fn run(value: Custom) { let _ = value.is_some(); let _ = value.unwrap_or_default(); }"
            }
            Lookalike::ShadowedOption => {
                "pub struct Option; impl Option { pub fn is_some(&self) -> u8 { 1 } pub fn unwrap_or(&self, v: u8) -> u8 { v } } pub fn run(value: Option) { let _ = Option::is_some(&value); let _ = value.unwrap_or(0); }"
            }
            Lookalike::TraitOnOption => {
                "pub trait Inspect { fn is_some(&self) -> u8; fn unwrap_or_default(&self) -> u8; } impl Inspect for Option<u8> { fn is_some(&self) -> u8 { 1 } fn unwrap_or_default(&self) -> u8 { 1 } } pub fn run(value: Option<u8>) { let _ = Inspect::is_some(&value); let _ = Inspect::unwrap_or_default(&value); }"
            }
        };
        let output = support::analyze(source, &[])?;
        let findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        assert!(
            findings
                .iter()
                .all(|finding| finding["rule"] != "option-result-predicate"
                    && finding["rule"] != "silent-default"),
            "{case:?}: {findings:?}"
        );
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum GuardedUse {
    Method,
    FirstArgument,
    PointerArgument,
    LaterArgument,
    Qualified,
    Error,
    Negative,
    Mutated,
    DifferentLocal,
    PresenceOnly,
    PayloadClosure,
    Lookalike,
    Suppressed,
}

#[hegel::test]
fn a_predicate_and_extraction_must_use_the_same_variant_and_local(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<GuardedUse>());
    let (source, expected) = match case {
        GuardedUse::PointerArgument => (
            "pub fn read(v:Option<u8>, consume:fn(u8)) { if v.is_some() { consume(v.unwrap()); } }",
            Some("is_some"),
        ),
        GuardedUse::FirstArgument => (
            "fn consume(_: u8) {} pub fn read(v: Option<u8>) { if v.is_some() { consume(v.unwrap()); } }",
            Some("is_some"),
        ),
        GuardedUse::LaterArgument => (
            "fn consume(_: Option<u8>, _: u8) {} pub fn read(mut v: Option<u8>) { if v.is_some() { consume(v.take(), v.unwrap()); } }",
            None,
        ),
        GuardedUse::Method => (
            "pub fn read(v: Option<u8>) -> u8 { if v.is_some() { v.unwrap() } else { 0 } }",
            Some("is_some"),
        ),
        GuardedUse::Qualified => (
            "type Input = Option<u8>; pub fn read(v: Input) -> u8 { if Input::is_some(&v) { Input::unwrap(v) } else { 0 } }",
            Some("is_some"),
        ),
        GuardedUse::Error => (
            "pub fn read(v: Result<(), u8>) -> u8 { if v.is_err() { v.unwrap_err() } else { 0 } }",
            Some("is_err"),
        ),
        GuardedUse::Negative => (
            "pub fn read(v: Option<u8>) -> u8 { if !v.is_none() { v.expect(\"present\") } else { 0 } }",
            Some("is_none"),
        ),
        GuardedUse::Mutated => (
            "pub fn read(mut v: Option<u8>) -> u8 { if v.is_some() { v = Some(2); v.unwrap() } else { 0 } }",
            None,
        ),
        GuardedUse::DifferentLocal => (
            "pub fn read(v: Option<u8>, w: Option<u8>) -> u8 { if v.is_some() { w.unwrap() } else { 0 } }",
            None,
        ),
        GuardedUse::PresenceOnly => ("pub fn read(v: Option<u8>) -> bool { v.is_some() }", None),
        GuardedUse::PayloadClosure => (
            "pub fn read(v: Option<u8>) -> bool { v.is_some_and(|n| n > 0) }",
            None,
        ),
        GuardedUse::Lookalike => (
            "pub struct Input; impl Input { fn is_some(&self)->bool{true} fn unwrap(self)->u8{1} } pub fn read(v:Input)->u8 { if v.is_some() { v.unwrap() } else { 0 } }",
            None,
        ),
        GuardedUse::Suppressed => (
            "// shapelint: allow(option-result-predicate)\npub fn read(v: Option<u8>)->u8 { if v.is_some() { v.unwrap() } else {0} }",
            None,
        ),
    };
    let output = support::analyze(source, &[]).expect("driver analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|row: &serde_json::Value| row["rule"] == "option-result-predicate")
        .collect();
    let labels: Vec<_> = findings
        .iter()
        .map(|finding| {
            let span = &finding["primary"]["span"];
            &source[span["start"].as_u64().expect("start") as usize
                ..span["end"].as_u64().expect("end") as usize]
        })
        .collect();
    assert_eq!(
        labels,
        expected.into_iter().collect::<Vec<_>>(),
        "{case:?}: {output}"
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Fallback {
    Literal,
    Effect,
    Default,
    ConstantClosure,
    Panic,
    MappedError,
    EmptyCollection,
    OtherErrorType,
}

#[hegel::test]
fn silent_defaults_identify_errors_replaced_by_success(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Fallback>());
    let (source, count) = match case {
        Fallback::Effect => (
            "pub fn read(v: Result<u8, String>, log: fn()) -> Result<u8, String> { Ok(v.unwrap_or_else(|_| { log(); 0 })) }",
            0,
        ),
        Fallback::Literal => (
            "pub fn read(v: Result<u8, String>) -> Result<u8, String> { Ok(v.unwrap_or(0)) }",
            1,
        ),
        Fallback::Default => (
            "pub fn read(v: Result<u8, String>) -> Result<u8, String> { Ok(Result::unwrap_or_default(v)) }",
            1,
        ),
        Fallback::ConstantClosure => (
            "pub fn read(v: Result<u8, String>) -> Result<u8, String> { Ok(v.unwrap_or_else(|_| 0)) }",
            1,
        ),
        Fallback::Panic => (
            "pub fn read(v: Result<u8, String>) -> Result<u8, String> { Ok(v.unwrap_or_else(|_| panic!(\"one test session\"))) }",
            0,
        ),
        Fallback::MappedError => (
            "pub fn read(v: Result<u8, u8>) -> Result<u8, u8> { Ok(v.unwrap_or_else(|e| e + 1)) }",
            0,
        ),
        Fallback::EmptyCollection => (
            "pub fn callers(v: Option<Vec<u8>>) -> Vec<u8> { v.unwrap_or_default() }",
            0,
        ),
        Fallback::OtherErrorType => (
            "pub fn read(v: Result<u8, String>) -> Result<u8, u32> { Ok(v.unwrap_or(0)) }",
            0,
        ),
    };
    let output = support::analyze(source, &[]).expect("driver analysis");
    let findings = output
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).expect("finding"))
        .filter(|row| row["rule"] == "silent-default")
        .count();
    assert_eq!(findings, count, "{case:?}: {output}");
}
