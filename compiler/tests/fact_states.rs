#![feature(rustc_private)]

mod support;

use std::fmt::Write;

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum Access {
    Direct,
    Alias,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Branches {
    left: Vec<u8>,
    right: Vec<u8>,
    access: Access,
}

#[hegel::test(print_blob = true)]
fn unrelated_assignments_aliases_and_merges_preserve_a_checked_value(tc: hegel::TestCase) {
    let Branches {
        left,
        right,
        access,
    } = tc.draw(hegel::generators::default::<Branches>());
    let mut source = String::from(
        "pub fn run(values:&[u8],other:&mut Vec<u8>,index:usize,choose:bool,mutate:fn(&mut Vec<u8>),observe:fn(u8))->Option<u8>{let _=observe;if index<values.len(){if choose{",
    );
    let entries = left.into_iter().enumerate();
    for (index, value) in entries {
        write!(
            source,
            "let local_{index}={value}u8;observe(local_{index});"
        )
        .expect("write generated source");
    }
    source.push_str(match access {
        Access::Direct => "mutate(other);",
        Access::Alias => "let alias=&mut *other;mutate(alias);",
    });
    source.push_str("}else{");
    let entries = right.into_iter().enumerate();
    for (index, value) in entries {
        write!(
            source,
            "let local_{index}={value}u8;observe(local_{index});"
        )
        .expect("write generated source");
    }
    source.push_str("mutate(other);}Some(values[index])}else{None}}");
    let output =
        support::analyze(&source, &["--show-analysis-gaps"]).expect("analyze generated source");
    let obligations: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("diagnostic JSON"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unproven-precondition"
                || finding["rule"] == "invalid-state-use"
                || finding["rule"] == "invalidated-validation"
        })
        .collect();
    assert_eq!(
        obligations.len(),
        0,
        "the model never writes values: {source}\n{output}"
    );
}

#[test]
fn writing_one_union_field_invalidates_a_check_on_another_field() {
    let source = "pub union Cell { pub left:u8, pub right:u8 }
        pub fn run(value:&mut Cell, mutate:fn(&mut u8))->u8 {
            if unsafe { value.left }>0 {
                mutate(unsafe { &mut value.right });
                if unsafe { value.left }>0 { 1 } else { 0 }
            } else { 0 }
        }";
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analyze union alias");
    let redundant: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("diagnostic JSON"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "redundant-check")
        .collect();
    assert_eq!(
        redundant.len(),
        0,
        "union fields occupy the same storage: {output}"
    );
}

#[test]
fn a_union_mutation_preserves_disjoint_outer_fields() {
    let source = "pub union Cell { pub left:u8, pub right:u8 }
        pub struct Outer { pub cell:Cell, pub other:u8 }
        pub fn run(value:&mut Outer, mutate:fn(&mut u8))->u8 {
            if value.other>0 {
                mutate(unsafe { &mut value.cell.right });
                if value.other>0 { 1 } else { 0 }
            } else { 0 }
        }";
    let output =
        support::analyze(source, &["--show-analysis-gaps"]).expect("analyze nested union mutation");
    let redundant: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("diagnostic JSON"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "redundant-check")
        .collect();
    assert_eq!(
        redundant.len(),
        1,
        "the mutation only overlaps the cell field: {output}"
    );
}
