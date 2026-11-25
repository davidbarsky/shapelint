#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_middle;

mod support;

use std::error::Error;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Change {
    DifferentSurroundings,
    DifferentEffect,
    DifferentError,
    DifferentType,
}

#[hegel::test]
fn loop_regions_preserve_their_effects(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let change = tc.draw(hegel::generators::default::<Change>());
        let first = "pub fn first(mut n: u32, effect: fn(u32), before: fn(), after: fn()) {
            before();
            loop { if n == 0 { break; } effect(n); n = n.wrapping_sub(1); }
            after();
        }";
        let second = "pub fn second(mut n: u32, effect: fn(u32), before: fn(), after: fn()) {
            before(); before();
            loop { if n == 0 { break; } effect(n); n = n.wrapping_sub(1); }
            after(); after();
        }";
        let (second, expected) = match change {
            Change::DifferentSurroundings => (second.to_owned(), 1),
            Change::DifferentEffect => (second.replace("effect(n);", "effect(n); effect(n);"), 0),
            Change::DifferentError => (
                second.replace("effect(n);", "effect(n); assert!(n != 42);"),
                0,
            ),
            Change::DifferentType => (second.replace("u32", "u64"), 0),
        };
        let text = format!("{first}\n{second}");
        let output = support::analyze(&text, &[])?;
        let mut findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        findings.retain(|finding| finding["rule"] == "duplicate-control-flow");
        let loops: Vec<_> = findings
            .iter()
            .filter(|finding| {
                let start = finding["primary"]["span"]["start"]
                    .as_u64()
                    .expect("byte offset") as usize;
                text[start..].starts_with("loop")
            })
            .collect();
        assert_eq!(loops.len(), expected, "{change:?}: {findings:?}");
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[test]
fn branch_region_matches_between_different_callers() -> Result<(), Box<dyn Error>> {
    let text = "pub fn first(flag: bool, a: fn(), b: fn(), setup: fn()) { setup(); if flag { a(); } else { b(); } }
        pub fn second(flag: bool, a: fn(), b: fn(), setup: fn()) { setup(); setup(); if flag { a(); } else { b(); } setup(); }";
    let output = support::analyze(text, &[])?;
    let mut findings: Vec<serde_json::Value> = output
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()?;
    findings.retain(|finding| finding["rule"] == "duplicate-control-flow");
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0]["rule"], "duplicate-control-flow");
    let start = findings[0]["primary"]["span"]["start"]
        .as_u64()
        .ok_or("missing span")? as usize;
    assert!(text[start..].starts_with("if flag"));
    Ok(())
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Iteration {
    While,
    For,
    Async,
}

#[hegel::test]
fn source_loop_forms_share_the_region_analysis(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let iteration = tc.draw(hegel::generators::default::<Iteration>());
        let text = match iteration {
            Iteration::While => "pub fn first(mut n: u32, effect: fn(u32)) { std::hint::black_box(1); while n > 0 { effect(n); n = n.wrapping_sub(1); } }
                pub fn second(mut n: u32, effect: fn(u32)) { std::hint::black_box(2); while n > 0 { effect(n); n = n.wrapping_sub(1); } }".into(),
            Iteration::For => "pub fn first(n: u32, effect: fn(u32)) { std::hint::black_box(1); for value in 0..n { effect(value); } }
                pub fn second(n: u32, effect: fn(u32)) { std::hint::black_box(2); for value in 0..n { effect(value); } }".into(),
            Iteration::Async => {
                let source = include_str!("fixtures/async_completion.rs");
                let (_, function) = source.split_once("pub async fn ").ok_or("missing fixture")?;
                let first = source.replace("    loop {", "    std::hint::black_box(1);\n    loop {");
                let second = format!("pub async fn {function}").replace("complete(", "second(").replace("    loop {", "    std::hint::black_box(2);\n    loop {");
                format!("{first}\n{second}")
            }
        };
        let output = support::analyze(&text, &[])?;
        let mut findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        findings.retain(|finding| finding["rule"] == "duplicate-control-flow");
        assert_eq!(findings.len(), 1, "{iteration:?}: {findings:?}");
        assert_eq!(findings[0]["rule"], "duplicate-control-flow");
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[test]
fn disjoint_regions_in_one_function_are_compared() -> Result<(), Box<dyn Error>> {
    let output = support::analyze(
        "pub fn run(mut a: u32, mut b: u32, effect: fn(u32)) {
        while a > 0 { effect(a); a = a.wrapping_sub(1); }
        while b > 0 { effect(b); b = b.wrapping_sub(1); }
    }",
        &[],
    )?;
    let mut findings: Vec<serde_json::Value> = output
        .lines()
        .map(serde_json::from_str)
        .collect::<Result<_, _>>()?;
    findings.retain(|finding| finding["rule"] == "duplicate-control-flow");
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0]["item"], "run");
    Ok(())
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum BindingChange {
    Renamed,
    DifferentAlias,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum BranchArm {
    Then,
    Else,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct NestedBindings {
    arms: Vec<BranchArm>,
    change: BindingChange,
}

#[hegel::test(print_blob = true)]
fn overlapping_regions_preserve_aliases_across_blocks(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let NestedBindings { arms, change } =
            tc.draw(hegel::generators::default::<NestedBindings>());
        let mut branch = "if flag { effect(right); } else { effect(left); }".to_owned();
        for arm in arms {
            branch = match arm {
                BranchArm::Then => format!("if flag {{ {branch} }} else {{ effect(right); }}"),
                BranchArm::Else => format!("if flag {{ effect(right); }} else {{ {branch} }}"),
            };
        }
        let operation = format!(
            "loop {{
                if remaining == 0 {{ break; }}
                effect(left);
                {branch}
                effect(left);
                remaining = remaining.wrapping_sub(1);
            }}"
        );
        let (second, expected) = match change {
            BindingChange::Renamed => (operation.clone(), 1),
            BindingChange::DifferentAlias => (
                operation.replace(
                    "effect(left);\n                remaining",
                    "effect(right);\n                remaining",
                ),
                0,
            ),
        };
        let second = second
            .replace("remaining", "pending")
            .replace("effect", "action");
        let text = format!(
            "pub fn first(mut remaining: u32, flag: bool, left: u32, right: u32, effect: fn(u32)) {{
                std::hint::black_box(1);
                {operation}
            }}
            pub fn second(action: fn(u32), right: u32, flag: bool, left: u32, mut pending: u32) {{
                std::hint::black_box(2);
                {second}
            }}"
        );
        let output = support::analyze(&text, &[])?;
        let findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        let loops: Vec<_> = findings
            .iter()
            .filter(|finding| {
                let start = finding["primary"]["span"]["start"]
                    .as_u64()
                    .expect("byte offset") as usize;
                finding["rule"] == "duplicate-control-flow" && text[start..].starts_with("loop")
            })
            .collect();
        assert_eq!(loops.len(), expected, "{change:?}: {findings:?}");
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ExitChange {
    Renamed,
    Continue,
}

#[hegel::test(print_blob = true)]
fn region_fingerprints_preserve_continuation_targets(tc: hegel::TestCase) {
    let run = || -> Result<(), Box<dyn Error>> {
        let change = tc.draw(hegel::generators::default::<ExitChange>());
        let operation = "while remaining > 0 {
            remaining = remaining.wrapping_sub(1);
            if stop(remaining) { break; }
            effect(remaining);
        }";
        let (second, expected) = match change {
            ExitChange::Renamed => (operation.to_owned(), 1),
            ExitChange::Continue => (operation.replace("break;", "continue;"), 0),
        };
        let second = second.replace("remaining", "pending");
        let text = format!(
            "pub fn first(mut remaining: u32, stop: fn(u32) -> bool, effect: fn(u32)) {{
                std::hint::black_box(1);
                {operation}
            }}
            pub fn second(effect: fn(u32), stop: fn(u32) -> bool, mut pending: u32) {{
                std::hint::black_box(2);
                {second}
            }}"
        );
        let output = support::analyze(&text, &[])?;
        let findings: Vec<serde_json::Value> = output
            .lines()
            .map(serde_json::from_str)
            .collect::<Result<_, _>>()?;
        let loops: Vec<_> = findings
            .iter()
            .filter(|finding| {
                let start = finding["primary"]["span"]["start"]
                    .as_u64()
                    .expect("byte offset") as usize;
                finding["rule"] == "duplicate-control-flow" && text[start..].starts_with("while")
            })
            .collect();
        assert_eq!(loops.len(), expected, "{change:?}: {findings:?}");
        Ok(())
    };
    if let Err(error) = run() {
        panic!("{error}");
    }
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct SuffixAtom {
    operation: u8,
    locals: Vec<u8>,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct SuffixComparison {
    left: Vec<SuffixAtom>,
    right: Vec<SuffixAtom>,
}

#[hegel::test(print_blob = true)]
fn suffixes_preserve_naive_alpha_equivalence(tc: hegel::TestCase) {
    use rustc_data_structures::fingerprint::Fingerprint;
    use rustc_middle::mir::Local;
    use shapelint_driver::regions::{Atom, Suffixes};

    let SuffixComparison { left, right } =
        tc.draw(hegel::generators::default::<SuffixComparison>());
    let left_graph = Suffixes::try_from(
        left.iter()
            .map(|atom| Atom {
                fingerprint: Fingerprint::new(u64::from(atom.operation), 0u64),
                locals: atom
                    .locals
                    .iter()
                    .map(|local| Local::from_usize(usize::from(*local)))
                    .collect(),
            })
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let renamed = Suffixes::try_from(
        left.iter()
            .map(|atom| Atom {
                fingerprint: Fingerprint::new(u64::from(atom.operation), 0u64),
                locals: atom
                    .locals
                    .iter()
                    .map(|local| Local::from_usize(usize::from(u8::MAX - *local)))
                    .collect(),
            })
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let right_graph = Suffixes::try_from(
        right
            .iter()
            .map(|atom| Atom {
                fingerprint: Fingerprint::new(u64::from(atom.operation), 0u64),
                locals: atom
                    .locals
                    .iter()
                    .map(|local| Local::from_usize(usize::from(*local)))
                    .collect(),
            })
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let model = |atoms: &[SuffixAtom]| {
        let mut bindings = Vec::new();
        let mut normalized = Vec::new();
        for atom in atoms {
            let mut locals = Vec::new();
            for &local in &atom.locals {
                let number = match bindings.iter().position(|previous| *previous == local) {
                    Some(index) => index,
                    None => {
                        let index = bindings.len();
                        bindings.push(local);
                        index
                    }
                };
                locals.push(number);
            }
            normalized.push((atom.operation, locals));
        }
        (bindings, normalized)
    };
    for start in 0..left.len() {
        let (bindings, expected) = model(&left[start..]);
        assert_eq!(
            left_graph[start].fingerprint, renamed[start].fingerprint,
            "renamed suffix at {start}: {left:?}"
        );
        assert_eq!(
            left_graph.bindings(start).collect::<Vec<_>>(),
            bindings
                .iter()
                .map(|local| Local::from_usize(usize::from(*local)))
                .collect::<Vec<_>>(),
            "first-use order at {start}: {left:?}",
        );
        assert_eq!(
            renamed.bindings(start).collect::<Vec<_>>(),
            bindings
                .iter()
                .map(|local| Local::from_usize(usize::from(u8::MAX - *local)))
                .collect::<Vec<_>>(),
            "renamed first-use order at {start}: {left:?}",
        );
        for other in 0..right.len() {
            assert_eq!(
                left_graph[start].fingerprint == right_graph[other].fingerprint,
                expected == model(&right[other..]).1,
                "suffixes {start}/{other}: {left:?} / {right:?}",
            );
        }
    }
}

#[test]
fn deep_suffixes_share_bindings_without_recursive_drop() {
    use rustc_data_structures::fingerprint::Fingerprint;
    use rustc_middle::mir::Local;
    use shapelint_driver::regions::{Atom, Suffixes};

    let depth = 100_000;
    let suffixes = Suffixes::try_from(
        (0..depth)
            .map(|index| Atom {
                fingerprint: Fingerprint::new(1u64, 0u64),
                locals: vec![Local::from_usize(index)],
            })
            .collect::<Vec<_>>(),
    )
    .unwrap();
    assert_eq!(
        suffixes.bindings(0).collect::<Vec<_>>(),
        (0..depth).map(Local::from_usize).collect::<Vec<_>>()
    );
    assert_eq!(
        suffixes.bindings(depth - 1).collect::<Vec<_>>(),
        vec![Local::from_usize(depth - 1)]
    );
}

#[test]
fn one_conditional_link_update_is_not_an_extractable_region() {
    let source = "pub fn left(link: Option<&mut Option<usize>>, node: usize) { std::hint::black_box(1); if let Some(parent) = link { *parent = Some(node); } } pub fn right(link: Option<&mut Option<usize>>, node: usize) { std::hint::black_box(2); if let Some(parent) = link { *parent = Some(node); } }";
    let output = support::analyze(source, &[]).expect("driver analysis");
    assert!(!output.contains("duplicate-control-flow"), "{output}");
}
