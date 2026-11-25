#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;

use hegel::PrintableGenerator;
use hegel::generators::{self, BoxedPrintableGenerator, DefaultGenerator};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{DefId, DefIndex};
use shapelint_driver::contracts::recursion::Recursion;

#[derive(Debug)]
struct Graph {
    nodes: usize,
    initial: Vec<(usize, usize)>,
    added: Vec<(usize, usize)>,
}

impl DefaultGenerator for Graph {
    type Generator = BoxedPrintableGenerator<'static, Self>;

    fn default_generator() -> Self::Generator {
        hegel::compose!(|tc| {
            let nodes = tc
                .draw(generators::vecs(generators::default::<()>()).min_size(1))
                .len();
            let edges = || {
                generators::vecs(hegel::compose!(|tc| {
                    let caller = tc.draw(generators::integers::<usize>().max_value(nodes - 1));
                    let callee = tc.draw(generators::integers::<usize>().max_value(nodes - 1));
                    (caller, callee)
                }))
            };
            let initial = tc.draw(edges());
            let added = tc.draw(edges().min_size(1));
            Self {
                nodes,
                initial,
                added,
            }
        })
        .boxed_printable()
    }
}

fn reachable(nodes: usize, edges: &[(usize, usize)]) -> FxHashSet<(usize, usize)> {
    let mut reached = FxHashSet::default();
    for start in 0..nodes {
        reached.insert((start, start));
        let mut pending = vec![start];
        while let Some(caller) = pending.pop() {
            let entries = edges.iter().filter(|(source, _)| *source == caller);
            for &(_, callee) in entries {
                if reached.insert((start, callee)) {
                    pending.push(callee);
                }
            }
        }
    }
    reached
}

#[hegel::test(print_blob = true)]
fn incremental_components_order_and_revisions_match_transitive_closure(tc: hegel::TestCase) {
    let Graph {
        nodes,
        initial,
        added,
    } = tc.draw(generators::default::<Graph>());
    let definitions: Vec<_> = (0..nodes)
        .map(|index| DefId::local(DefIndex::from_usize(index)))
        .collect();
    let mut recursion = Recursion::try_from(
        initial
            .iter()
            .map(|&(caller, callee)| (definitions[caller], definitions[callee]))
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let mut edges = initial;
    let mut before = reachable(nodes, &edges);
    for (caller, callee) in added {
        let revisions: Vec<_> = definitions
            .iter()
            .map(|def| recursion.revision(*def))
            .collect();
        let actual = recursion
            .edge(definitions[caller], definitions[callee])
            .unwrap();
        edges.push((caller, callee));
        let after = reachable(nodes, &edges);
        let expected = match after.contains(&(callee, caller)) {
            true => Some((definitions[caller], definitions[callee])),
            false => None,
        };
        assert_eq!(actual, expected, "edge {caller}->{callee}: {edges:?}");
        let mut positions = FxHashMap::default();
        let entries = recursion.components().enumerate();
        for (position, members) in entries {
            for &def in members {
                assert_eq!(
                    positions.insert(def, position),
                    None,
                    "component membership is unique"
                );
            }
        }
        for &(caller, callee) in &edges {
            assert!(
                positions[&definitions[caller]] <= positions[&definitions[callee]],
                "invalid condensation order after {edges:?}"
            );
        }
        let mut merged = FxHashSet::default();
        for left in 0..nodes {
            for right in 0..nodes {
                let expected = after.contains(&(left, right)) && after.contains(&(right, left));
                let actual = match (
                    positions.get(&definitions[left]),
                    positions.get(&definitions[right]),
                ) {
                    (Some(left), Some(right)) => left == right,
                    _ => left == right,
                };
                assert_eq!(actual, expected, "SCC {left},{right} after {edges:?}");
                if expected && !(before.contains(&(left, right)) && before.contains(&(right, left)))
                {
                    merged.insert(left);
                }
            }
        }
        let entries = definitions.iter().enumerate();
        for (index, def) in entries {
            match merged
                .iter()
                .find(|member| after.contains(&(index, **member)))
            {
                Some(_) => assert_ne!(
                    recursion.revision(*def),
                    revisions[index],
                    "affected caller {index} after {edges:?}"
                ),
                None => assert_eq!(
                    recursion.revision(*def),
                    revisions[index],
                    "unaffected caller {index} after {edges:?}"
                ),
            }
        }
        before = after;
    }
}

#[test]
fn a_cycle_invalidates_its_callers_but_preserves_its_callees_and_unrelated_roots() {
    let definitions: Vec<_> = (0..7)
        .map(|index| DefId::local(DefIndex::from_usize(index)))
        .collect();
    let [root, left, right, leaf, unrelated, other, extra] = definitions.as_slice() else {
        unreachable!("fixture defines each graph role");
    };
    let mut recursion = Recursion::try_from(
        [
            (*root, *left),
            (*left, *right),
            (*right, *leaf),
            (*unrelated, *other),
        ]
        .to_vec(),
    )
    .unwrap();
    let root_revision = recursion.revision(*root);
    let left_revision = recursion.revision(*left);
    let right_revision = recursion.revision(*right);
    let leaf_revision = recursion.revision(*leaf);
    let unrelated_revision = recursion.revision(*unrelated);
    recursion.insert(*other, *extra).unwrap();
    assert_eq!(recursion.revision(*root), root_revision);
    assert_eq!(recursion.revision(*unrelated), unrelated_revision);
    assert_eq!(
        recursion.edge(*right, *left).unwrap(),
        Some((*right, *left))
    );
    assert_ne!(recursion.revision(*root), root_revision);
    assert_ne!(recursion.revision(*left), left_revision);
    assert_ne!(recursion.revision(*right), right_revision);
    assert_eq!(recursion.revision(*leaf), leaf_revision);
    assert_eq!(recursion.revision(*unrelated), unrelated_revision);
}

#[test]
fn adding_forward_edges_to_a_long_chain_preserves_completed_revisions() {
    let definitions: Vec<_> = (0..100_000)
        .map(|index| DefId::local(DefIndex::from_usize(index)))
        .collect();
    let mut recursion = Recursion::try_from(
        definitions
            .windows(2)
            .map(|pair| (pair[0], pair[1]))
            .collect::<Vec<_>>(),
    )
    .unwrap();
    let revisions: Vec<_> = definitions
        .iter()
        .map(|def| recursion.revision(*def))
        .collect();
    for pair in definitions.windows(3) {
        assert_eq!(recursion.edge(pair[0], pair[2]).unwrap(), None);
    }
    let entries = definitions.iter().zip(revisions);
    for (def, revision) in entries {
        assert_eq!(recursion.revision(*def), revision);
    }
    let order: Vec<_> = recursion.components().flatten().copied().collect();
    assert_eq!(order, definitions);
}

#[test]
fn adding_new_callers_does_not_rebuild_the_existing_chain() {
    let definitions: Vec<_> = (0..100_000)
        .map(|index| DefId::local(DefIndex::from_usize(index)))
        .collect();
    let mut recursion = Recursion::default();
    let entries = definitions.windows(2).rev();
    for pair in entries {
        assert_eq!(recursion.edge(pair[0], pair[1]).unwrap(), None);
    }
    let order: Vec<_> = recursion.components().flatten().copied().collect();
    assert_eq!(order, definitions);
    assert_eq!(
        recursion.edge(definitions[99_999], definitions[0]).unwrap(),
        Some((definitions[99_999], definitions[0]))
    );
    assert_eq!(recursion.components().count(), 1);
}
