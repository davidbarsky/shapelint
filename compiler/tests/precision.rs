#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Boundary {
    Local,
    Helper,
}

#[hegel::test]
fn guarded_wrapping_subtraction_preserves_the_index_bound(tc: hegel::TestCase) {
    let boundary = tc.draw(hegel::generators::default::<Boundary>());
    let source = match boundary {
        Boundary::Local => {
            "pub fn run(values: &[u8]) -> Option<u8> { if values.len() >= 1 { let last = values.len().wrapping_sub(1); Some(values[last]) } else { None } }"
        }
        Boundary::Helper => {
            "fn last(length: usize) -> usize { length.wrapping_sub(1) } pub fn run(values: &[u8]) -> Option<u8> { if values.len() >= 1 { Some(values[last(values.len())]) } else { None } }"
        }
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    assert!(obligations.is_empty(), "{boundary:?}: {output}");
}

#[hegel::test]
fn both_branch_results_retain_their_common_upper_bound(tc: hegel::TestCase) {
    let boundary = tc.draw(hegel::generators::default::<Boundary>());
    let source = match boundary {
        Boundary::Local => {
            "pub fn run(values: &[u8], choose: bool) -> Option<u8> { if values.len() >= 2 { let index = if choose { 0 } else { 1 }; Some(values[index]) } else { None } }"
        }
        Boundary::Helper => {
            "fn index(choose: bool) -> usize { if choose { 0 } else { 1 } } pub fn run(values: &[u8], choose: bool) -> Option<u8> { if values.len() >= 2 { Some(values[index(choose)]) } else { None } }"
        }
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    assert!(obligations.is_empty(), "{boundary:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Mutation {
    SeparateArgument,
    SeparateField,
}

#[hegel::test]
fn unrelated_mutation_preserves_the_checked_collection(tc: hegel::TestCase) {
    let mutation = tc.draw(hegel::generators::default::<Mutation>());
    let source = match mutation {
        Mutation::SeparateArgument => {
            "pub fn run(values: &[u8], other: &mut Vec<u8>, index: usize) -> Option<u8> { if index < values.len() { other.clear(); Some(values[index]) } else { None } }"
        }
        Mutation::SeparateField => {
            "pub struct State { pub values: Vec<u8>, pub other: Vec<u8> } pub fn run(state: &mut State, index: usize) -> Option<u8> { if index < state.values.len() { state.other.clear(); Some(state.values[index]) } else { None } }"
        }
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    assert!(obligations.is_empty(), "{mutation:?}: {output}");
}

#[hegel::test]
fn a_returned_value_and_its_length_keep_their_relationship(tc: hegel::TestCase) {
    let boundary = tc.draw(hegel::generators::default::<Boundary>());
    let source = match boundary {
        Boundary::Local => {
            "pub fn run(make: fn() -> String) -> usize { let text = make(); let end = text.len(); text[..end].len() }"
        }
        Boundary::Helper => {
            "fn prepare(make: fn() -> String) -> (String, usize) { let text = make(); let end = text.len(); (text, end) } pub fn run(make: fn() -> String) -> usize { let (text, end) = prepare(make); text[..end].len() }"
        }
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    assert!(obligations.is_empty(), "{boundary:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum MissingGuarantee {
    EmptyCollection,
    UnboundedBranch,
    MutatedCollection,
    SeparateCalls,
}

#[hegel::test]
fn missing_guarantees_still_require_review(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<MissingGuarantee>());
    let source = match case {
        MissingGuarantee::EmptyCollection => {
            "pub fn run(values: &[u8]) -> u8 { values[values.len().wrapping_sub(1)] }"
        }
        MissingGuarantee::UnboundedBranch => {
            "pub fn run(values: &[u8], choose: bool, other: usize) -> Option<u8> { if values.len() >= 2 { let index = if choose { 0 } else { other }; Some(values[index]) } else { None } }"
        }
        MissingGuarantee::MutatedCollection => {
            "pub fn run(values: &mut Vec<u8>, index: usize) -> Option<u8> { if index < values.len() { values.clear(); Some(values[index]) } else { None } }"
        }
        MissingGuarantee::SeparateCalls => {
            "fn prepare(make: fn() -> String) -> (String, usize) { let text = make(); let end = text.len(); (text, end) } pub fn run(make: fn() -> String) -> usize { let (text, _) = prepare(make); let (_, end) = prepare(make); text[..end].len() }"
        }
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    assert!(!obligations.is_empty(), "{case:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum VecMutation {
    Push,
    PushAfterUpperBound,
    UpperBoundInvalidated,
    PanicBeforePush,
    UserMethod,
    AliasedPush,
    ReborrowedPush,
    OtherReceiver,
    Clear,
    Pop,
    UnknownCall,
    AliasedClear,
    PanicPath,
}

#[hegel::test]
fn vec_push_establishes_only_the_nonempty_postcondition(tc: hegel::TestCase) {
    let mutation = tc.draw(hegel::generators::default::<VecMutation>());
    let source = match mutation {
        VecMutation::Push => {
            "pub fn run(mut values: Vec<u8>) -> usize { values.push(1); values.len() - 1 }"
        }
        VecMutation::PushAfterUpperBound => {
            "pub fn run(mut values: Vec<u8>) -> usize { if values.len() <= 10 { values.push(1); values.len() - 1 } else { 0 } }"
        }
        VecMutation::UpperBoundInvalidated => {
            "pub fn run(mut values: Vec<u8>) -> usize { if values.len() <= 10 { values.push(1); 10 - values.len() } else { 0 } }"
        }
        VecMutation::PanicBeforePush => {
            "pub fn run(mut values: Vec<u8>, fail: bool) -> usize { let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| { if fail { panic!() } values.push(1); })); values.len() - 1 }"
        }
        VecMutation::UserMethod => {
            "pub struct Buffer(Vec<u8>); impl Buffer { fn push(&mut self, _:u8) {} } pub fn run(mut values: Buffer) -> usize { values.push(1); values.0.len() - 1 }"
        }
        VecMutation::AliasedPush => {
            "pub fn run(values: &mut Vec<u8>) -> usize { let alias = values; alias.push(1); alias.len() - 1 }"
        }
        VecMutation::ReborrowedPush => {
            "pub fn run(values: &mut Vec<u8>) -> usize { let alias = &mut *values; alias.push(1); values.len() - 1 }"
        }
        VecMutation::OtherReceiver => {
            "pub fn run(first: &mut Vec<u8>, second: &mut Vec<u8>) -> usize { let alias = &mut *first; alias.push(1); second.len() - 1 }"
        }
        VecMutation::Clear => {
            "pub fn run(mut values: Vec<u8>) -> usize { values.push(1); values.clear(); values.len() - 1 }"
        }
        VecMutation::Pop => {
            "pub fn run(mut values: Vec<u8>) -> usize { values.push(1); values.pop(); values.len() - 1 }"
        }
        VecMutation::UnknownCall => {
            "pub fn run(mut values: Vec<u8>, touch: fn(&mut Vec<u8>)) -> usize { values.push(1); touch(&mut values); values.len() - 1 }"
        }
        VecMutation::AliasedClear => {
            "pub fn run(values: &mut Vec<u8>) -> usize { let alias = values; alias.push(1); alias.clear(); alias.len() - 1 }"
        }
        VecMutation::PanicPath => {
            "pub fn run(mut values: Vec<u8>, panic_now: bool) -> usize { values.push(1); if panic_now { panic!() } values.len() - 1 }"
        }
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    match mutation {
        VecMutation::Push
        | VecMutation::PushAfterUpperBound
        | VecMutation::AliasedPush
        | VecMutation::ReborrowedPush
        | VecMutation::PanicPath => {
            assert!(obligations.is_empty(), "{mutation:?}: {output}");
        }
        VecMutation::Clear
        | VecMutation::UpperBoundInvalidated
        | VecMutation::PanicBeforePush
        | VecMutation::UserMethod
        | VecMutation::OtherReceiver
        | VecMutation::Pop
        | VecMutation::UnknownCall
        | VecMutation::AliasedClear => {
            assert!(!obligations.is_empty(), "{mutation:?}: {output}");
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Invocation {
    Nested,
    DistinctNested,
    RepeatedInLoop,
}

#[hegel::test]
fn returned_correlations_belong_to_one_invocation(tc: hegel::TestCase) {
    let invocation = tc.draw(hegel::generators::default::<Invocation>());
    let body = match invocation {
        Invocation::Nested => "let (text, end) = outer(make); text[..end].len()",
        Invocation::DistinctNested => {
            "let (text, _) = outer(make); let (_, end) = outer(make); text[..end].len()"
        }
        Invocation::RepeatedInLoop => {
            "let (mut text, end) = outer(make); for _ in 0..n { let (next, _) = outer(make); text = next; } text[..end].len()"
        }
    };
    let source = format!(
        "fn prepare(make: fn() -> String) -> (String, usize) {{ let text = make(); let end = text.len(); (text, end) }} fn outer(make: fn() -> String) -> (String, usize) {{ prepare(make) }} pub fn run(make: fn() -> String, n: usize) -> usize {{ let _ = n; {body} }}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    match invocation {
        Invocation::Nested => assert!(obligations.is_empty(), "{invocation:?}: {output}"),
        Invocation::DistinctNested | Invocation::RepeatedInLoop => {
            assert!(!obligations.is_empty(), "{invocation:?}: {output}")
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct BranchIndices {
    left: u8,
    right: u8,
}

#[hegel::test]
fn joined_bounds_cover_every_branch_value(tc: hegel::TestCase) {
    let BranchIndices { left, right } = tc.draw(hegel::generators::default::<BranchIndices>());
    let length = u16::from(left.max(right)) + 1;
    let source = format!(
        "fn index(choose: bool) -> usize {{ if choose {{ {left} }} else {{ {right} }} }} pub fn run(values: &[u8], choose: bool) -> Option<u8> {{ if values.len() >= {length} {{ Some(values[index(choose)]) }} else {{ None }} }}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    assert!(obligations.is_empty(), "{left}, {right}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Width {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Denominator {
    Wrapped,
    DifferenceFromMaximum,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct Wrapping {
    width: Width,
    denominator: Denominator,
}

#[hegel::test]
fn wrapping_subtraction_uses_the_integer_width(tc: hegel::TestCase) {
    let Wrapping { width, denominator } = tc.draw(hegel::generators::default::<Wrapping>());
    let integer = match width {
        Width::U8 => "u8",
        Width::U16 => "u16",
        Width::U32 => "u32",
        Width::U64 => "u64",
        Width::U128 => "u128",
        Width::Usize => "usize",
    };
    let value = match denominator {
        Denominator::Wrapped => format!("0_{integer}.wrapping_sub(1)"),
        Denominator::DifferenceFromMaximum => {
            format!("0_{integer}.wrapping_sub(1).wrapping_sub({integer}::MAX)")
        }
    };
    let source = format!(
        "fn divide(value: {integer}) -> {integer} {{ 1 / value }} pub fn run() -> {integer} {{ divide({value}) }}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    match denominator {
        Denominator::Wrapped => assert!(obligations.is_empty(), "{width:?}: {output}"),
        Denominator::DifferenceFromMaximum => {
            assert_eq!(obligations.len(), 1, "{width:?}: {output}");
            assert_eq!(
                obligations[0]["rule"], "invalid-state-use",
                "{width:?}: {output}"
            );
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum CheckedArithmetic {
    AddSafe,
    AddSafeRightBound,
    AddDubious,
    AddDefiniteFailure,
    SignedAdd,
    DynamicGuard,
    SignedNegativeSafe,
    WidenFrom,
    WidenCast,
    NarrowCast,
    LogShift,
    LogZero,
    CheckedLogShift,
    LogOfWiderInteger,
    SignedCountSafe,
    ShiftSignedNegative,
    ShiftSafeU8,
    ShiftSafeU16,
    ShiftSafeSignedValue,
    ShiftRightSafeU8,
    ShiftDefiniteFailure,
    ShiftRightDefiniteFailure,
    ShiftSignedCount,
}

#[hegel::test]
fn checked_integer_arithmetic_respects_width_and_signedness(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<CheckedArithmetic>());
    let source = match case {
        CheckedArithmetic::AddSafe => {
            "pub fn run(left: u8) -> u8 { if left <= 200 { left + 50 } else { 0 } }"
        }
        CheckedArithmetic::AddSafeRightBound => {
            "pub fn run(right: u8) -> u8 { if right <= 50 { 200u8 + right } else { 0 } }"
        }
        CheckedArithmetic::AddDubious => "pub fn run(left: u8, right: u8) -> u8 { left + right }",
        CheckedArithmetic::AddDefiniteFailure => {
            "pub fn run(left: u8) -> u8 { if left >= 250 { left + 10 } else { 0 } }"
        }
        CheckedArithmetic::SignedAdd => {
            "pub fn run(left: i8) -> i8 { if left <= 100 { left + 20 } else { 0 } }"
        }
        CheckedArithmetic::DynamicGuard => {
            "pub fn run(left:u8, right:u8)->u8 { if left <= u8::MAX - right { left + right } else { 0 } }"
        }
        CheckedArithmetic::SignedNegativeSafe => {
            "pub fn run(left:i8)->i8 { if left >= -120 { left + -8 } else { 0 } }"
        }
        CheckedArithmetic::WidenFrom => {
            "pub struct Id(pub u32); pub fn run(id: Id)->u128 { u128::from(id.0) + 1 }"
        }
        CheckedArithmetic::WidenCast => "pub fn run(x: u32)->u64 { x as u64 + 1 }",
        CheckedArithmetic::NarrowCast => "pub fn run(x: u32)->u8 { x as u8 + 1 }",
        CheckedArithmetic::LogShift => {
            "pub fn run(x: u32)->u32 { if x != 0 { 1u32 << x.ilog2() } else { 0 } }"
        }
        CheckedArithmetic::LogZero => "pub fn run()->u32 { 0u32.ilog2() }",
        CheckedArithmetic::CheckedLogShift => {
            "pub fn run(x: u128)->i128 { if let Some(bit) = x.checked_ilog2() { 1i128 << bit } else { 0 } }"
        }
        CheckedArithmetic::LogOfWiderInteger => {
            "pub fn run(x: u64)->u32 { if let Some(bit) = x.checked_ilog2() { 1u32 << bit } else { 0 } }"
        }
        CheckedArithmetic::SignedCountSafe => {
            "pub fn run(count:i8)->u8 { if count >= 0 && count < 8 { 1u8 << count } else { 0 } }"
        }
        CheckedArithmetic::ShiftSignedNegative => {
            "pub fn run(count:i8)->u8 { if count < 0 { 1u8 << count } else { 0 } }"
        }
        CheckedArithmetic::ShiftSafeU8 => {
            "pub fn run(count: u8) -> u8 { if count < 8 { 1u8 << count } else { 0 } }"
        }
        CheckedArithmetic::ShiftSafeU16 => {
            "pub fn run(count: u8) -> u16 { if count < 16 { 1u16 << count } else { 0 } }"
        }
        CheckedArithmetic::ShiftSafeSignedValue => {
            "pub fn run(count: u8) -> i8 { if count < 8 { 1i8 << count } else { 0 } }"
        }
        CheckedArithmetic::ShiftRightSafeU8 => {
            "pub fn run(count: u8) -> u8 { if count < 8 { 255u8 >> count } else { 0 } }"
        }
        CheckedArithmetic::ShiftDefiniteFailure => {
            "pub fn run(count: u8) -> u8 { if count >= 8 { 1u8 << count } else { 0 } }"
        }
        CheckedArithmetic::ShiftRightDefiniteFailure => {
            "pub fn run(count: u8) -> u8 { if count >= 8 { 255u8 >> count } else { 0 } }"
        }
        CheckedArithmetic::ShiftSignedCount => {
            "pub fn run(count: i8) -> u8 { if count < 8 { 1u8 << count } else { 0 } }"
        }
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    match case {
        CheckedArithmetic::AddSafe
        | CheckedArithmetic::AddSafeRightBound
        | CheckedArithmetic::SignedAdd
        | CheckedArithmetic::DynamicGuard
        | CheckedArithmetic::SignedNegativeSafe
        | CheckedArithmetic::WidenFrom
        | CheckedArithmetic::WidenCast
        | CheckedArithmetic::LogShift
        | CheckedArithmetic::CheckedLogShift
        | CheckedArithmetic::SignedCountSafe
        | CheckedArithmetic::ShiftSafeU8
        | CheckedArithmetic::ShiftSafeU16
        | CheckedArithmetic::ShiftSafeSignedValue
        | CheckedArithmetic::ShiftRightSafeU8 => {
            assert!(obligations.is_empty(), "{case:?}: {output}");
        }
        CheckedArithmetic::AddDubious
        | CheckedArithmetic::NarrowCast
        | CheckedArithmetic::LogZero
        | CheckedArithmetic::LogOfWiderInteger
        | CheckedArithmetic::AddDefiniteFailure
        | CheckedArithmetic::ShiftSignedNegative
        | CheckedArithmetic::ShiftDefiniteFailure
        | CheckedArithmetic::ShiftRightDefiniteFailure
        | CheckedArithmetic::ShiftSignedCount => {
            assert!(!obligations.is_empty(), "{case:?}: {output}");
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Addends {
    Signed(i8, i8),
    Unsigned(u8, u8),
}

#[hegel::test]
fn addition_at_a_call_site_agrees_with_checked_add(tc: hegel::TestCase) {
    let (ty, arguments, sum) = match tc.draw(hegel::generators::default::<Addends>()) {
        Addends::Signed(a, b) => ("i8", format!("{a}, {b}"), a.checked_add(b).map(i16::from)),
        Addends::Unsigned(a, b) => ("u8", format!("{a}, {b}"), a.checked_add(b).map(i16::from)),
    };
    let source = format!(
        "fn add(a: {ty}, b: {ty}) -> {ty} {{ a + b }} pub fn run() -> {ty} {{ add({arguments}) }}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["item"] == "run"
                && (finding["rule"] == "unproven-precondition"
                    || finding["rule"] == "invalid-state-use")
        })
        .collect();
    match sum {
        Some(_) => assert!(findings.is_empty(), "{source}: {output}"),
        None => {
            assert_eq!(findings.len(), 1, "{source}: {output}");
            assert_eq!(
                findings[0]["rule"], "invalid-state-use",
                "{source}: {output}"
            );
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum UncertainRelation {
    IndependentChoices,
    OverlappingIntervals,
}

#[hegel::test]
fn intervals_do_not_claim_exact_values(tc: hegel::TestCase) {
    let relation = tc.draw(hegel::generators::default::<UncertainRelation>());
    let condition = match relation {
        UncertainRelation::IndependentChoices => "index(a)..index(b)",
        UncertainRelation::OverlappingIntervals => "1..index(a)",
    };
    let source = format!(
        "fn index(choose: bool) -> usize {{ if choose {{ 0 }} else {{ 2 }} }} pub fn run(values: &[u8], a: bool, b: bool) -> &[u8] {{ let _ = b; if values.len() >= 2 {{ &values[{condition}] }} else {{ values }} }}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding["rule"] == "unproven-precondition")
            .count(),
        1,
        "{relation:?}: {output}"
    );
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding["rule"] == "invalid-state-use")
            .count(),
        0,
        "{relation:?}: {output}"
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Recheck {
    Argument,
    Field,
}

#[hegel::test]
fn checks_after_a_mutation_use_the_new_value(tc: hegel::TestCase) {
    let recheck = tc.draw(hegel::generators::default::<Recheck>());
    let source = match recheck {
        Recheck::Argument => {
            "pub fn run(values: &mut Vec<u8>, change: fn(&mut Vec<u8>), index: usize) -> Option<u8> { change(values); if index < values.len() { Some(values[index]) } else { None } }"
        }
        Recheck::Field => {
            "pub struct State { pub values: Vec<u8>, pub other: Vec<u8> } pub fn run(state: &mut State, change: fn(&mut Vec<u8>), index: usize) -> Option<u8> { change(&mut state.values); if index < state.values.len() { Some(state.values[index]) } else { None } }"
        }
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    assert!(obligations.is_empty(), "{recheck:?}: {output}");
}
