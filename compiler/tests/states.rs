#![feature(rustc_private)]

mod support;

use std::error::Error;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Access {
    None,
    Some,
    ResultError,
    ResultSuccess,
    Guarded,
    OppositeGuard,
    Reassigned,
    Joined,
    UnknownCall,
    CopiedBeforeMutation,
    TakeUnknown,
    TakeKnown,
    NegatedGuard,
    ImpossibleBranch,
    MatchGuard,
    ErrorPayload,
    RawWrite,
    UnionWrite,
}

#[hegel::test]
fn variant_facts_follow_branches_and_invalidation(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let access = tc.draw(hegel::generators::default::<Access>());
        let (text, expected) = match access {
            Access::TakeKnown => (
                "pub fn run() -> u32 { let mut value = Some(3); value.take().unwrap() }",
                0,
            ),
            Access::NegatedGuard => (
                "pub fn run(value: Option<u32>) -> u32 { if !value.is_some() { value.unwrap() } else { 0 } }",
                1,
            ),
            Access::ImpossibleBranch => (
                "pub fn run() -> u32 { let value = Some(3); if value.is_none() { value.unwrap() } else { 0 } }",
                0,
            ),
            Access::MatchGuard => (
                "pub fn run(value: Option<u32>) -> u32 { if let Some(_) = value { value.unwrap() } else { 0 } }",
                0,
            ),
            Access::ErrorPayload => (
                "pub fn run() -> u32 { let value: Result<u8, u32> = Ok(3); value.unwrap_err() }",
                1,
            ),
            Access::RawWrite => (
                "pub fn run() -> u32 { let mut value = None; let ptr = &mut value as *mut Option<u32>; unsafe { *ptr = Some(3); } value.unwrap() }",
                0,
            ),
            Access::UnionWrite => (
                "pub union U { first: Option<u32>, second: Option<u32> } pub fn run() -> u32 { let mut value = U { first: None }; value.second = Some(3); unsafe { value.first.unwrap() } }",
                0,
            ),
            Access::None => (
                "pub fn run() -> u32 { let value: Option<u32> = None; value.unwrap() }",
                1,
            ),
            Access::Some => (
                "pub fn run() -> u32 { let value = Some(4); value.unwrap() }",
                0,
            ),
            Access::ResultError => (
                "pub fn run() -> u32 { let value: Result<u32, u8> = Err(3); value.unwrap() }",
                1,
            ),
            Access::ResultSuccess => (
                "pub fn run() -> u32 { let value: Result<u32, u8> = Ok(3); value.unwrap() }",
                0,
            ),
            Access::Guarded => (
                "pub fn run(value: Option<u32>) -> u32 { if value.is_some() { value.unwrap() } else { 0 } }",
                0,
            ),
            Access::OppositeGuard => (
                "pub fn run(value: Option<u32>) -> u32 { if value.is_none() { value.unwrap() } else { 0 } }",
                1,
            ),
            Access::Reassigned => (
                "pub fn run(mut value: Option<u32>) -> u32 { if value.is_some() { value = None; value.unwrap() } else { 0 } }",
                1,
            ),
            Access::Joined => (
                "pub fn run(flag: bool) -> u32 { let value = if flag { Some(3) } else { None }; value.unwrap() }",
                0,
            ),
            Access::UnknownCall => (
                "pub fn run(value: &mut Option<u32>, change: fn(&mut Option<u32>)) -> u32 { if value.is_none() { change(value); value.unwrap() } else { 0 } }",
                0,
            ),
            Access::CopiedBeforeMutation => (
                "pub fn run(mut value: Option<u32>) -> (u32, Option<u32>) { let old = value; value = None; (old.unwrap(), value) }",
                0,
            ),
            Access::TakeUnknown => (
                "pub fn run(value: &mut Option<u32>) -> u32 { value.take().unwrap() }",
                0,
            ),
        };
        let output = support::analyze(text, &[])?;
        let findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        let invalid = findings
            .iter()
            .filter(|finding| finding["rule"] == "invalid-variant-access")
            .count();
        assert_eq!(invalid, expected, "{access:?}: {findings:?}");
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Representation {
    ContradictoryConstructor,
    ConsistentConstructor,
    PayloadGuard,
    ExternalGuard,
    Enum,
    Suppressed,
    EnumDiscriminator,
    ConjunctiveGuard,
    DeadConstructor,
    DifferentInstantiation,
    DifferentBounds,
}

#[hegel::test]
fn consumer_assumptions_are_separate_from_constructor_evidence(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let representation = tc.draw(hegel::generators::default::<Representation>());
        let base = "pub struct State { pub ready: bool, pub payload: Option<u32> }
            impl State {
                pub fn read(&self) -> u32 { if self.ready { self.payload.unwrap() } else { 0 } }
                pub fn make() -> Self { Self { ready: true, payload: None } }
            }";
        let (text, assumptions, constructions) = match representation {
            Representation::DifferentBounds => (
                "pub trait Marker {} pub struct State<T> { pub ready: bool, pub payload: Option<T> } impl<T: Marker + Copy> State<T> { pub fn read(&self) -> Option<T> { if self.ready { Some(self.payload.unwrap()) } else { None } } } impl<T> State<T> { pub fn make() -> Self { Self { ready: true, payload: None } } }".into(), 1, 0,
            ),
            Representation::DifferentInstantiation => (
                "pub struct State<T> { pub ready: bool, pub payload: Option<T> } impl State<u32> { pub fn read(&self) -> u32 { if self.ready { self.payload.unwrap() } else { 0 } } } impl State<String> { pub fn make() -> Self { Self { ready: true, payload: None } } }".into(), 1, 0,
            ),
            Representation::EnumDiscriminator => (
                "pub enum Phase { Waiting, Ready } pub struct State { pub phase: Phase, pub payload: Option<u32> } impl State { pub fn read(&self) -> u32 { match self.phase { Phase::Ready => self.payload.unwrap(), Phase::Waiting => 0 } } pub fn make() -> Self { Self { phase: Phase::Ready, payload: None } } }".into(), 1, 1,
            ),
            Representation::ConjunctiveGuard => (
                base.replace("pub ready: bool,", "pub ready: bool, pub allowed: bool,").replace("if self.ready", "if self.ready && self.allowed").replace("ready: true,", "ready: true, allowed: false,"), 1, 0,
            ),
            Representation::DeadConstructor => (
                base.replace("Self { ready: true", "let value: Option<u32> = None; let _ = value.unwrap(); Self { ready: true"), 1, 0,
            ),
            Representation::ContradictoryConstructor => (base.to_owned(), 1, 1),
            Representation::ConsistentConstructor => (base.replace("payload: None", "payload: Some(3)"), 1, 0),
            Representation::PayloadGuard => (base.replace("if self.ready", "if self.ready && self.payload.is_some()"), 0, 0),
            Representation::ExternalGuard => (base.replace("read(&self)", "read(&self, external: bool)").replace("if self.ready", "if self.ready && external"), 1, 0),
            Representation::Enum => ("pub enum State { Waiting, Ready(u32) } impl State { pub fn read(&self) -> u32 { match self { Self::Waiting => 0, Self::Ready(value) => *value } } }".into(), 0, 0),
            Representation::Suppressed => (base.replace("pub fn read", "// shapelint: allow(unencoded-state-invariant)\n pub fn read").replace("pub fn make", "// shapelint: allow(inconsistent-state-construction)\n pub fn make"), 0, 0),
        };
        let output = support::analyze(&text, &[])?;
        let findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        assert_eq!(
            findings
                .iter()
                .filter(|finding| finding["rule"] == "unencoded-state-invariant")
                .count(),
            assumptions,
            "{representation:?}: {findings:?}"
        );
        assert_eq!(
            findings
                .iter()
                .filter(|finding| finding["rule"] == "inconsistent-state-construction")
                .count(),
            constructions,
            "{representation:?}: {findings:?}"
        );
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}
