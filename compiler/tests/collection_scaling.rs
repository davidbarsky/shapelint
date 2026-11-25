#![feature(rustc_private)]

use std::cell::Cell;

use shapelint_driver::contracts;
use shapelint_driver::contracts::graph::sets::{Combination, SetId, Work, with_sets};
use shapelint_driver::contracts::graph::{ConditionId, ExprId, ExprNode, Graph, with_graph};
use shapelint_driver::sequence::{Scan, Sequence};

#[hegel::test]
fn saturated_work_counters_preserve_results(tc: hegel::TestCase) {
    let visits = tc.draw(hegel::generators::default::<u16>());
    with_sets::<u8, _>(|sets| {
        sets.work = Work {
            combination_visits: usize::MAX,
            subset_visits: usize::MAX,
        };
        assert_eq!(
            sets.combine(Combination::Union, SetId::EMPTY, SetId::EMPTY)
                .unwrap(),
            SetId::EMPTY
        );
        assert_eq!(sets.subset(SetId::EMPTY, SetId::EMPTY), Some(()));
        assert_eq!(sets.work.combination_visits, usize::MAX);
        assert_eq!(sets.work.subset_visits, usize::MAX);
    });

    let mut total = contracts::Work {
        requirement_visits: usize::MAX,
        ..contracts::Work::default()
    };
    total += contracts::Work {
        requirement_visits: 1,
        reporting_visits: usize::from(visits),
        ..contracts::Work::default()
    };
    assert_eq!(total.requirement_visits, usize::MAX);
    assert_eq!(total.reporting_visits, usize::from(visits));
}

#[test]
fn growing_set_overlaps_reuse_completed_branches() {
    let measured = [8_usize, 16, 32].map(|size| {
        with_sets(|sets| {
            let mut complete = SetId::EMPTY;
            let mut prefix = SetId::EMPTY;
            for value in 0..size {
                complete = sets.insert(complete, value).unwrap();
            }
            sets.work = Work::default();
            for value in 0..size {
                prefix = sets.insert(prefix, value).unwrap();
                assert_eq!(
                    sets.combine(Combination::Intersection, prefix, complete)
                        .unwrap(),
                    prefix,
                );
                assert_eq!(sets.subset(prefix, complete), Some(()));
            }
            assert_eq!(prefix, complete);
            let visits_per_prefix = 2 * size.ilog2() as usize + 2;
            assert!(sets.work.combination_visits <= size * visits_per_prefix);
            assert!(sets.work.subset_visits <= size * visits_per_prefix);
            sets.work
        })
    });
    eprintln!("growing set overlaps: {measured:?}");
}

#[test]
fn disjoint_set_queries_skip_unrelated_branches() {
    let measured = [8, 16, 32].map(|size| {
        with_sets(|sets| {
            let mut even = SetId::EMPTY;
            let mut odd = SetId::EMPTY;
            for value in 0..size {
                even = sets.insert(even, value * 2).unwrap();
                odd = sets.insert(odd, value * 2 + 1).unwrap();
            }
            sets.work = Work::default();
            assert_eq!(
                sets.combine(Combination::Intersection, even, odd).unwrap(),
                SetId::EMPTY
            );
            assert_eq!(sets.subset(even, odd), None);
            let first = sets.work;
            assert_eq!(
                sets.combine(Combination::Intersection, odd, even).unwrap(),
                SetId::EMPTY
            );
            assert_eq!(sets.subset(even, odd), None);
            assert_eq!(sets.work.combination_visits, first.combination_visits + 1);
            assert_eq!(sets.work.subset_visits, first.subset_visits + 1);
            first
        })
    });
    eprintln!("disjoint set queries: {measured:?}");
    let [small, medium, large] = measured;
    assert_eq!(
        large.combination_visits - medium.combination_visits,
        2 * (medium.combination_visits - small.combination_visits)
    );
    assert_eq!(
        large.subset_visits - medium.subset_visits,
        2 * (medium.subset_visits - small.subset_visits)
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Growth {
    Append,
    Prepend,
}

fn conjunction_work<'g>(graph: &mut Graph<'g>, size: usize, growth: Growth) -> (usize, usize) {
    let calls = Cell::new(0);
    let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
    let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
    let mut sequence = Sequence::EMPTY;
    let mut scan = Scan::new(
        |graph: &mut Graph<'g>, prefix: ExprId<'g>, condition: &ConditionId<'g>| {
            calls.set(calls.get() + 1);
            graph.intern_expr(ExprNode::Select(*condition, prefix, zero))
        },
    );
    for value in 0..size {
        let input = graph.intern_expr(ExprNode::Argument(value)).unwrap();
        let condition = graph.from_expr(input, 1).unwrap();
        sequence = match growth {
            Growth::Append => graph.condition_sequences.push(sequence, condition).unwrap(),
            Growth::Prepend => {
                let singleton = graph
                    .condition_sequences
                    .push(Sequence::EMPTY, condition)
                    .unwrap();
                graph
                    .condition_sequences
                    .append(singleton, sequence)
                    .unwrap()
            }
        };
        let mut result = scan
            .apply(
                graph,
                |graph| &graph.condition_sequences,
                sequence,
                one,
                zero,
            )
            .unwrap();
        let conditions = graph.condition_sequences.iter(sequence).rev();
        for expected in conditions {
            match graph[result] {
                ExprNode::Select(condition, prefix, fallback) => {
                    assert_eq!(condition, *expected);
                    assert_eq!(fallback, zero);
                    result = prefix;
                }
                ExprNode::Test(condition) => {
                    assert_eq!(condition, *expected);
                    result = one;
                }
                _ => panic!(
                    "conjunction retains its ordered conditions: {:?}",
                    graph[result]
                ),
            }
        }
        assert_eq!(result, one);
    }
    let expressions = graph
        .expressions()
        .filter(|node| match node {
            ExprNode::Select(..) | ExprNode::Test(_) => true,
            _ => false,
        })
        .count();
    (calls.get(), expressions)
}

#[test]
fn prepended_conjunctions_characterize_quadratic_intermediate_nodes() {
    let measured = [8, 16, 32]
        .map(|size| with_graph(|mut graph| conjunction_work(&mut graph, size, Growth::Prepend)));
    eprintln!("prepended conjunctions (leaf calls, conjunction nodes): {measured:?}");
    assert_eq!(measured, [(36, 36), (136, 136), (528, 528)]);
}

#[test]
fn appended_conjunctions_reuse_prefixes() {
    let measured = [8, 16, 32]
        .map(|size| with_graph(|mut graph| conjunction_work(&mut graph, size, Growth::Append)));
    eprintln!("appended conjunctions (leaf calls, conjunction nodes): {measured:?}");
    assert_eq!(measured, [(8, 8), (16, 16), (32, 32)]);
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Conjunctions {
    conditions: Vec<()>,
    growth: Growth,
}

#[hegel::test(print_blob = true)]
fn conjunction_work_matches_retained_ordered_nodes(tc: hegel::TestCase) {
    let Conjunctions { conditions, growth } = tc.draw(hegel::generators::default::<Conjunctions>());
    let size = conditions.len();
    let expected = match growth {
        Growth::Append => size,
        Growth::Prepend => size * (size + 1) / 2,
    };
    assert_eq!(
        with_graph(|mut graph| conjunction_work(&mut graph, size, growth)),
        (expected, expected)
    );
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HashDistribution {
    Distinct,
    Colliding,
}

#[derive(Clone, Copy, Debug)]
struct CountedKey<'a> {
    value: usize,
    distribution: HashDistribution,
    comparisons: &'a Cell<usize>,
}

impl PartialEq for CountedKey<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.comparisons.set(self.comparisons.get() + 1);
        self.value == other.value && self.distribution == other.distribution
    }
}
impl Eq for CountedKey<'_> {}
impl std::hash::Hash for CountedKey<'_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        match self.distribution {
            HashDistribution::Distinct => self.value.hash(state),
            HashDistribution::Colliding => 0_usize.hash(state),
        }
    }
}

fn map_lookup_work(size: usize, distribution: HashDistribution) -> usize {
    use shapelint_driver::persistent::{Hashed, Map, with_maps};
    let comparisons = Cell::new(0);
    with_maps::<CountedKey<'_>, usize, Hashed, _>(|maps| {
        let mut map = Map::EMPTY;
        for value in 0..size {
            maps.insert(
                &mut map,
                CountedKey {
                    value,
                    distribution,
                    comparisons: &comparisons,
                },
                value,
            )
            .unwrap();
        }
        comparisons.set(0);
        for value in 0..size {
            assert_eq!(
                maps.get(
                    map,
                    &CountedKey {
                        value,
                        distribution,
                        comparisons: &comparisons
                    }
                ),
                Some(&value)
            );
        }
    });
    comparisons.get()
}

#[test]
fn distinct_map_lookups_do_not_scan_siblings() {
    let measured = [8, 16, 32].map(|size| map_lookup_work(size, HashDistribution::Distinct));
    eprintln!("distinct map lookup equality calls: {measured:?}");
    assert_eq!(measured, [8, 16, 32]);
}

#[test]
fn constant_hash_keys_require_equality_search_in_the_key_interner() {
    let measured = [8, 16, 32].map(|size| map_lookup_work(size, HashDistribution::Colliding));
    eprintln!("forced collision map lookup equality calls: {measured:?}");
    // Hash and equality alone cannot route distinct keys when every hash is equal.
    // The interner searches candidates; the routed singleton then checks its key once.
    assert_eq!(
        measured,
        [8, 16, 32].map(|size| size * (size + 1) / 2 + size)
    );
}
