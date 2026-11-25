#![feature(rustc_private)]
extern crate rustc_data_structures;
extern crate rustc_driver;

use rustc_data_structures::fx::FxHashMap;
use shapelint_driver::contracts::graph::CapacityError;
use shapelint_driver::persistent::{
    Composition, Difference, Differences, Hashed, Identical, Map, Neighbor, Ordered, with_maps,
};
use std::cell::Cell;
use std::hash::{Hash, Hasher};
use std::ptr;

#[test]
fn map_handles_fit_their_u32_identity() {
    assert_eq!(
        std::mem::size_of::<Map<'static, u8, u8>>(),
        std::mem::size_of::<u32>()
    );
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum Key {
    Spread(u8),
    Collision(u8),
}
impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Self::Spread(v) => (0_u8, v).hash(state),
            Self::Collision(_) => 1_u8.hash(state),
        }
    }
}
#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum Action {
    Put(Key, i16),
    Remove(Key),
    Save,
    Restore,
    IntersectSaved,
    OverlaySaved,
}

#[hegel::test(print_blob = true)]
fn snapshots_preserve_changes_and_canonical_identity(tc: hegel::TestCase) {
    let actions = tc.draw(hegel::generators::default::<Vec<Action>>());
    with_maps::<Key, i16, Hashed, _>(|maps| {
        let mut actual = Map::EMPTY;
        let mut expected = FxHashMap::default();
        let mut saved = (actual, expected.clone());
        for action in actions {
            match action {
                Action::Put(k, v) => assert_eq!(
                    maps.insert(&mut actual, k, v).unwrap(),
                    expected.insert(k, v)
                ),
                Action::Remove(k) => {
                    assert_eq!(maps.remove(&mut actual, &k).unwrap(), expected.remove(&k))
                }
                Action::Save => saved = (actual, expected.clone()),
                Action::Restore => {
                    actual = saved.0;
                    expected = saved.1.clone();
                }
                Action::IntersectSaved => {
                    maps.intersection(&mut actual, saved.0).unwrap();
                    expected.retain(|key, value| saved.1.get(key) == Some(value));
                }
                Action::OverlaySaved => {
                    maps.overlay(&mut actual, saved.0).unwrap();
                    expected.extend(saved.1.iter().map(|(&key, &value)| (key, value)));
                }
            }
            let observed: FxHashMap<_, _> = maps.iter(actual).map(|(k, v)| (*k, *v)).collect();
            assert_eq!(observed, expected);
            assert_eq!(
                maps.iter(saved.0)
                    .map(|(k, v)| (*k, *v))
                    .collect::<FxHashMap<_, _>>(),
                saved.1
            );
            assert_eq!(maps.len(actual), expected.len());
            assert_eq!(actual == saved.0, expected == saved.1);
            let mut reverse = Map::EMPTY;
            let mut entries: Vec<_> = expected.iter().map(|(&k, &v)| (k, v)).collect();
            entries.reverse();
            for (k, v) in entries {
                maps.insert(&mut reverse, k, v).unwrap();
            }
            assert_eq!(actual, reverse);
            let differences: FxHashMap<_, _> = Differences::from((&*maps, actual, saved.0))
                .map(|(k, d)| {
                    (
                        *k,
                        match d {
                            Difference::Left(v) => (Some(*v), None),
                            Difference::Right(v) => (None, Some(*v)),
                            Difference::Both(a, b) => (Some(*a), Some(*b)),
                        },
                    )
                })
                .collect();
            let mut model = FxHashMap::default();
            for (&k, &v) in &expected {
                match saved.1.get(&k) {
                    Some(other) if *other == v => {}
                    other => {
                        model.insert(k, (Some(v), other.copied()));
                    }
                }
            }
            for (&k, &v) in &saved.1 {
                if let None = expected.get(&k) {
                    model.insert(k, (None, Some(v)));
                }
            }
            assert_eq!(differences, model);
        }
    });
}

#[test]
fn equal_insert_keeps_the_canonical_map_and_saved_version() {
    with_maps::<u8, String, Hashed, _>(|maps| {
        let mut current = Map::EMPTY;
        maps.insert(&mut current, 1, "one".to_owned()).unwrap();
        maps.insert(&mut current, 2, "two".to_owned()).unwrap();
        let saved = current;
        let retained = maps.retained_nodes();

        assert_eq!(
            maps.insert(&mut current, 1, "one".to_owned()).unwrap(),
            Some("one".to_owned())
        );
        assert_eq!(current, saved);
        assert_eq!(maps.retained_nodes(), retained);
        assert_eq!(maps.get(saved, &1).map(String::as_str), Some("one"));
        assert_eq!(maps.get(saved, &2).map(String::as_str), Some("two"));
    });
}

#[test]
fn equal_insert_compares_the_key_once() {
    #[derive(Clone, Debug)]
    struct CountedKey {
        value: u8,
        comparisons: std::rc::Rc<Cell<usize>>,
    }
    impl PartialEq for CountedKey {
        fn eq(&self, other: &Self) -> bool {
            self.comparisons.set(self.comparisons.get() + 1);
            self.value == other.value
        }
    }
    impl Eq for CountedKey {}
    impl Hash for CountedKey {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.value.hash(state);
        }
    }

    with_maps::<CountedKey, usize, Hashed, _>(|maps| {
        let comparisons = std::rc::Rc::new(Cell::new(0));
        let mut map = Map::EMPTY;
        maps.insert(
            &mut map,
            CountedKey {
                value: 1,
                comparisons: comparisons.clone(),
            },
            10,
        )
        .unwrap();
        comparisons.set(0);

        assert_eq!(
            maps.insert(
                &mut map,
                CountedKey {
                    value: 1,
                    comparisons: comparisons.clone(),
                },
                10,
            )
            .unwrap(),
            Some(10)
        );
        assert_eq!(comparisons.get(), 1);
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
struct OrderedCase {
    entries: Vec<(u128, i16)>,
    query: u128,
}

#[test]
fn ordered_routes_distinguish_every_bit_of_a_key() {
    let keys: Vec<_> = std::iter::once(0)
        .chain((0..u128::BITS).map(|bit| 1u128.rotate_left(bit)))
        .chain(std::iter::once(u128::MAX))
        .collect();
    with_maps::<u128, u128, Ordered, _>(|maps| {
        let mut map = Map::EMPTY;
        let descending = keys.iter().rev();
        for &key in descending {
            maps.insert(&mut map, key, key).unwrap();
        }
        assert!(maps.iter(map).map(|(key, _)| key).eq(&keys));
        let adjacent = keys.iter().zip(keys.iter().skip(1));
        for (lower, upper) in adjacent {
            assert_eq!(
                maps.neighbor(map, *lower, Neighbor::After),
                Some((upper, upper))
            );
            assert_eq!(
                maps.neighbor(map, *upper, Neighbor::Before),
                Some((lower, lower))
            );
        }
    });
}

#[hegel::test(print_blob = true)]
fn ordered_neighbors_match_sorted_model(tc: hegel::TestCase) {
    let OrderedCase { entries, query } = tc.draw(hegel::generators::default::<OrderedCase>());
    with_maps::<u128, i16, Ordered, _>(|maps| {
        let mut map = Map::EMPTY;
        // shapelint: allow(collection-choice) Neighbor queries require sorted range order.
        let mut model = std::collections::BTreeMap::new();
        for (k, v) in entries {
            assert_eq!(maps.insert(&mut map, k, v).unwrap(), model.insert(k, v));
        }
        assert_eq!(
            maps.iter(map).map(|(k, v)| (*k, *v)).collect::<Vec<_>>(),
            model.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>()
        );
        assert_eq!(
            maps.neighbor(map, query, Neighbor::Before),
            model.range(..query).next_back()
        );
        assert_eq!(
            maps.neighbor(map, query, Neighbor::After),
            model
                .range((std::ops::Bound::Excluded(query), std::ops::Bound::Unbounded))
                .next()
        );
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Compositions {
    left: Vec<(Key, Vec<u8>)>,
    right: Vec<(Key, Vec<u8>)>,
}
#[hegel::test(print_blob = true)]
fn composition_reuses_results_and_preserves_collisions(tc: hegel::TestCase) {
    let Compositions { left, right } = tc.draw(hegel::generators::default::<Compositions>());
    with_maps::<Key, Vec<u8>, Hashed, _>(|maps| {
        let mut a = Map::EMPTY;
        let mut b = Map::EMPTY;
        let mut expected = FxHashMap::default();
        let mut right_model = FxHashMap::default();
        for (k, v) in left {
            maps.insert(&mut a, k, v.clone()).unwrap();
            expected.insert(k, v);
        }
        for (k, v) in right {
            maps.insert(&mut b, k, v.clone()).unwrap();
            right_model.insert(k, v);
        }
        for (key, left_value, right_value) in [
            (Key::Collision(0), vec![1], vec![2]),
            (Key::Collision(1), vec![3], vec![4]),
        ] {
            maps.insert(&mut a, key, left_value.clone()).unwrap();
            maps.insert(&mut b, key, right_value.clone()).unwrap();
            expected.insert(key, left_value);
            right_model.insert(key, right_value);
        }
        for (k, v) in right_model {
            expected.entry(k).or_insert_with(Vec::new).extend(v);
        }
        let calls = Cell::new(0);
        let mut composition = Composition::new(
            Identical::Combine,
            |_: &mut (), a: &Vec<u8>, b: &Vec<u8>| {
                calls.set(calls.get() + 1);
                Ok::<_, CapacityError>(a.iter().chain(b).copied().collect())
            },
        );
        let result = composition.compose(maps, &mut (), a, b).unwrap();
        assert_eq!(
            maps.iter(result)
                .map(|(k, v)| (*k, v.clone()))
                .collect::<FxHashMap<_, _>>(),
            expected
        );
        let count = calls.get();
        assert_eq!(composition.compose(maps, &mut (), a, b).unwrap(), result);
        assert_eq!(calls.get(), count);
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Sets {
    left: Vec<Key>,
    right: Vec<Key>,
}
#[hegel::test(print_blob = true)]
fn set_union_and_intersection_preserve_snapshots(tc: hegel::TestCase) {
    let Sets { left, right } = tc.draw(hegel::generators::default::<Sets>());
    with_maps::<Key, (), Hashed, _>(|maps| {
        let mut a = Map::EMPTY;
        let mut b = Map::EMPTY;
        let mut expected = rustc_data_structures::fx::FxHashSet::default();
        let mut expected_right = rustc_data_structures::fx::FxHashSet::default();
        for k in left {
            maps.insert(&mut a, k, ()).unwrap();
            expected.insert(k);
        }
        for k in right {
            maps.insert(&mut b, k, ()).unwrap();
            expected_right.insert(k);
        }
        let original = a;
        maps.overlay(&mut a, b).unwrap();
        assert_eq!(
            maps.iter(a)
                .map(|(k, _)| *k)
                .collect::<rustc_data_structures::fx::FxHashSet<_>>(),
            expected.union(&expected_right).copied().collect()
        );
        assert_eq!(
            maps.iter(original)
                .map(|(k, _)| *k)
                .collect::<rustc_data_structures::fx::FxHashSet<_>>(),
            expected
        );
        maps.intersection(&mut a, original).unwrap();
        assert_eq!(a, original);
    });
}

#[derive(Debug)]
struct Counted {
    value: usize,
    clones: std::rc::Rc<Cell<usize>>,
}
impl Clone for Counted {
    fn clone(&self) -> Self {
        self.clones.set(self.clones.get() + 1);
        Self {
            value: self.value,
            clones: self.clones.clone(),
        }
    }
}
impl PartialEq for Counted {
    fn eq(&self, other: &Self) -> bool {
        self.value == other.value
    }
}
impl Eq for Counted {}
impl Hash for Counted {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state);
    }
}

#[test]
fn growing_snapshots_do_not_clone_retained_values() {
    with_maps::<usize, Counted, Hashed, _>(|maps| {
        let clones = std::rc::Rc::new(Cell::new(0));
        let mut current = Map::EMPTY;
        let mut snapshots = Vec::new();
        for value in 0..10_000 {
            snapshots.push(current);
            maps.insert(
                &mut current,
                value,
                Counted {
                    value,
                    clones: clones.clone(),
                },
            )
            .unwrap();
        }
        assert_eq!(maps.len(current), 10_000);
        assert_eq!(maps.len(snapshots[0]), 0);
        assert_eq!(maps.len(snapshots[5_000]), 5_000);
        assert_eq!(clones.get(), 0);
    });
}

#[test]
fn shared_maps_reuse_canonical_ids_and_stable_payload_references() {
    with_maps::<u32, String, Hashed, _>(|maps| {
        let mut shared = maps.share();
        let mut original = Map::EMPTY;
        let mut equivalent = Map::EMPTY;

        maps.insert(&mut original, 11, "value".to_owned()).unwrap();
        shared
            .insert(&mut equivalent, 11, "value".to_owned())
            .unwrap();

        assert_eq!(original, equivalent);
        let original_value = maps.get(original, &11).unwrap();
        let equivalent_value = shared.get(equivalent, &11).unwrap();
        assert!(ptr::eq(original_value, equivalent_value));

        let (original_key, _) = maps.iter(original).next().unwrap();
        let (equivalent_key, _) = shared.iter(equivalent).next().unwrap();
        assert!(ptr::eq(original_key, equivalent_key));
    });
}

#[test]
fn composition_reuses_unchanged_overlapping_branches() {
    with_maps::<u128, u128, Ordered, _>(|maps| {
        let mut left = Map::EMPTY;
        let mut right = Map::EMPTY;
        for key in 0..128 {
            maps.insert(&mut left, key, 10).unwrap();
            maps.insert(&mut right, key, 20).unwrap();
        }
        let calls = Cell::new(0);
        let mut composition =
            Composition::new(Identical::Combine, |_: &mut (), a: &u128, b: &u128| {
                calls.set(calls.get() + 1);
                Ok::<_, CapacityError>(*a + *b)
            });
        let initial = composition.compose(maps, &mut (), left, right).unwrap();
        assert_eq!(calls.get(), 128);
        for key in 128..256 {
            maps.insert(&mut right, key, key).unwrap();
            let result = composition.compose(maps, &mut (), left, right).unwrap();
            assert_eq!(maps.get(result, &key), Some(&key));
            assert_eq!(calls.get(), 128);
        }
        for key in 0..128 {
            maps.insert(&mut right, key, 21).unwrap();
            let result = composition.compose(maps, &mut (), left, right).unwrap();
            assert_eq!(maps.get(result, &key), Some(&31));
            assert_eq!(calls.get(), 128 + usize::try_from(key + 1).unwrap());
        }
        assert_eq!(maps.get(initial, &0), Some(&30));
        assert_eq!(maps.len(initial), 128);
    });
}

#[hegel::test(print_blob = true)]
fn identical_composition_keeps_duplicate_sequence_occurrences(tc: hegel::TestCase) {
    let values = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_maps::<u8, Vec<u8>, Hashed, _>(|maps| {
        let mut map = Map::EMPTY;
        maps.insert(&mut map, 0, values.clone()).unwrap();
        let mut composition = Composition::new(
            Identical::Combine,
            |_: &mut (), left: &Vec<u8>, right: &Vec<u8>| {
                Ok::<_, CapacityError>(left.iter().chain(right).copied().collect())
            },
        );
        let result = composition.compose(maps, &mut (), map, map).unwrap();
        assert_eq!(
            maps.get(result, &0),
            Some(&values.iter().chain(&values).copied().collect::<Vec<_>>())
        );
    });
}

#[test]
fn nested_write_unions_share_inner_argument_sets() {
    with_maps::<Counted, (), Hashed, _>(|maps| {
        let clones = std::rc::Rc::new(Cell::new(0));
        let mut inner = Map::EMPTY;
        let mut snapshots = Vec::new();
        for value in 0..10_000 {
            let mut outer = Map::EMPTY;
            maps.insert(
                &mut outer,
                Counted {
                    value,
                    clones: clones.clone(),
                },
                (),
            )
            .unwrap();
            maps.overlay(&mut outer, inner).unwrap();
            snapshots.push(inner);
            inner = outer;
        }
        assert_eq!(maps.len(inner), 10_000);
        assert_eq!(maps.len(snapshots[5_000]), 5_000);
        assert_eq!(clones.get(), 0);
    });
}

#[hegel::test(print_blob = true)]
fn owned_map_updates_clone_only_returned_values(tc: hegel::TestCase) {
    let entries = tc.draw(hegel::generators::default::<Vec<(Key, usize)>>());
    with_maps::<Key, Counted, Hashed, _>(|maps| {
        let clones = std::rc::Rc::new(Cell::new(0));
        let mut actual = Map::EMPTY;
        let mut expected = FxHashMap::default();
        let mut returned = 0;
        for (key, value) in entries {
            let previous = maps
                .insert(
                    &mut actual,
                    key,
                    Counted {
                        value,
                        clones: clones.clone(),
                    },
                )
                .unwrap();
            let previous = match previous {
                Some(value) => {
                    returned += 1;
                    Some(value.value)
                }
                None => None,
            };
            assert_eq!(previous, expected.insert(key, value));
            assert_eq!(clones.get(), returned);
        }
    });
}
