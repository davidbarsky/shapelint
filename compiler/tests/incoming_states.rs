#![feature(rustc_private)]

use shapelint_driver::contracts::graph::CapacityError;
use shapelint_driver::persistent::{Composition, Identical, Map, Ordered, Routing, with_maps};
use shapelint_driver::states::incoming::Incoming;

#[derive(Debug, PartialEq, Eq)]
enum Error {
    Capacity(CapacityError),
    Interrupted,
}
impl From<CapacityError> for Error {
    fn from(value: CapacityError) -> Self {
        Self::Capacity(value)
    }
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Update {
    position: u16,
    value: Option<u64>,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Updates {
    seed: Option<u64>,
    batches: Vec<Vec<Update>>,
}

#[hegel::test(print_blob = true)]
fn changed_sparse_inputs_preserve_the_ordered_nonassociative_fold(tc: hegel::TestCase) {
    let Updates { seed, batches } = tc.draw(hegel::generators::default::<Updates>());
    with_maps::<u128, u64, Ordered, _>(|maps| {
        let mut incoming = Incoming::new(seed);
        let mut inputs: Vec<(usize, u64)> = Vec::new();
        for batch in batches {
            for Update { position, value } in batch {
                let position = usize::from(position);
                incoming.replace(maps, position, value).unwrap();
                inputs.retain(|(existing, _)| *existing != position);
                if let Some(value) = value {
                    inputs.push((position, value));
                }
            }
            inputs.sort_by_key(|(position, _)| *position);
            let expected = inputs.iter().fold(seed, |prefix, (_, value)| {
                Some(match prefix {
                    Some(prefix) => prefix.wrapping_mul(37).wrapping_add(*value),
                    None => *value,
                })
            });
            let actual = incoming
                .fold(maps, |prefix, value| {
                    *prefix = prefix.wrapping_mul(37).wrapping_add(*value);
                    Ok::<_, CapacityError>(())
                })
                .expect("infallible merge");
            assert_eq!(actual, expected);
        }
    });
}

#[hegel::test(print_blob = true)]
fn arriving_inputs_reuse_every_completed_prefix(tc: hegel::TestCase) {
    let values = tc.draw(hegel::generators::default::<Vec<u64>>());
    with_maps::<u128, u64, Ordered, _>(|maps| {
        let mut incoming = Incoming::new(None);
        let mut calls = 0;
        let entries = values.iter().enumerate();
        for (position, &value) in entries {
            incoming.replace(maps, position, Some(value)).unwrap();
            incoming
                .fold(maps, |prefix, value| {
                    calls += 1;
                    *prefix = prefix.wrapping_mul(37).wrapping_add(*value);
                    Ok::<_, CapacityError>(())
                })
                .expect("infallible merge");
        }
        assert_eq!(calls, values.len().saturating_sub(1));

        let entries = values.iter().enumerate();
        for (position, &value) in entries {
            incoming.replace(maps, position, Some(value)).unwrap();
        }
        incoming
            .fold(maps, |_, _| -> Result<(), CapacityError> {
                panic!("unchanged inputs must not reenter the merge")
            })
            .expect("cached fold");
    });
}

#[test]
fn convergence_reuses_the_unchanged_suffix() {
    with_maps::<u128, u64, Ordered, _>(|maps| {
        let mut incoming = Incoming::new(None);
        let entries = [1u64, 2, 3, 4].into_iter().enumerate();
        for (position, value) in entries {
            incoming.replace(maps, position, Some(value)).unwrap();
        }
        let original = incoming
            .fold(maps, |prefix, value| {
                *prefix = (*prefix + value) % 7;
                Ok::<_, CapacityError>(())
            })
            .expect("initial fold");
        incoming.replace(maps, 0, Some(8)).unwrap();
        let mut calls = 0;
        let changed = incoming
            .fold(maps, |prefix, value| {
                calls += 1;
                *prefix = (*prefix + value) % 7;
                Ok::<_, CapacityError>(())
            })
            .expect("changed fold");
        assert_eq!(changed, original);
        assert_eq!(calls, 1);
    });
}

#[test]
fn failed_merge_retries_from_its_completed_prefix() {
    with_maps::<u128, u64, Ordered, _>(|maps| {
        let mut incoming = Incoming::new(Some(1u64));
        let entries = [2, 3, 4].into_iter().enumerate();
        for (position, value) in entries {
            incoming.replace(maps, position, Some(value)).unwrap();
        }
        let mut visited = Vec::new();
        let failed = incoming.fold(maps, |prefix, value| {
            visited.push(*value);
            *prefix = *prefix * 10 + value;
            match value {
                3 => Err(Error::Interrupted),
                _ => Ok(()),
            }
        });
        assert_eq!(failed, Err(Error::Interrupted));
        assert_eq!(visited, [2, 3]);

        let mut visited = Vec::new();
        let completed = incoming
            .fold(maps, |prefix, value| {
                visited.push(*value);
                *prefix = *prefix * 10 + value;
                Ok::<_, CapacityError>(())
            })
            .expect("resumed merge");
        assert_eq!(completed, Some(1234));
        assert_eq!(visited, [3, 4]);
    });
}

#[test]
fn deleting_the_final_sparse_input_restores_the_seed() {
    with_maps::<u128, u64, Ordered, _>(|maps| {
        let mut incoming = Incoming::new(Some(5u64));
        incoming.replace(maps, usize::MAX, Some(2)).unwrap();
        let populated = incoming
            .fold(maps, |prefix, value| {
                *prefix -= value;
                Ok::<_, CapacityError>(())
            })
            .expect("populated fold");
        assert_eq!(populated, Some(3));

        incoming.replace(maps, usize::MAX, None).unwrap();
        let empty = incoming
            .fold(maps, |_, _| -> Result<(), CapacityError> {
                panic!("removal leaves no inputs to merge")
            })
            .expect("empty fold");
        assert_eq!(empty, Some(5));
    });
}

#[test]
fn edits_after_a_failed_fold_do_not_reuse_its_incomplete_result() {
    with_maps::<u128, u64, Ordered, _>(|maps| {
        let mut incoming = Incoming::new(Some(1u64));
        let entries = [2, 3, 4, 5].into_iter().enumerate();
        for (position, value) in entries {
            incoming.replace(maps, position, Some(value)).unwrap();
        }
        let original = incoming
            .fold(maps, |prefix, value| {
                *prefix = *prefix * 10 + value;
                Ok::<_, CapacityError>(())
            })
            .expect("initial fold");
        assert_eq!(original, Some(12345));

        incoming.replace(maps, 0, Some(9)).unwrap();
        let failed = incoming.fold(maps, |prefix, value| {
            *prefix = *prefix * 10 + value;
            match value {
                4 => Err(Error::Interrupted),
                _ => Ok(()),
            }
        });
        assert_eq!(failed, Err(Error::Interrupted));

        incoming.replace(maps, 0, Some(8)).unwrap();
        incoming.replace(maps, 0, Some(9)).unwrap();
        let mut visited = Vec::new();
        let resumed = incoming
            .fold(maps, |prefix, value| {
                visited.push(*value);
                *prefix = *prefix * 10 + value;
                Ok::<_, CapacityError>(())
            })
            .expect("resumed fold");
        assert_eq!(resumed, Some(19345));
        assert_eq!(visited, [9, 3, 4, 5]);
    });
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct ForcedCollisionKey(u32);

struct ForcedCollisionRouting;
impl Routing<ForcedCollisionKey> for ForcedCollisionRouting {
    fn address(_: &ForcedCollisionKey) -> u128 {
        0
    }
}

#[test]
fn forced_hash_collisions_keep_exact_map_oracle_and_singleton_leaves() {
    with_maps::<ForcedCollisionKey, u32, ForcedCollisionRouting, _>(|maps| {
        let mut map = Map::EMPTY;
        let count = 512;
        for key in 0..count {
            assert_eq!(
                maps.insert(&mut map, ForcedCollisionKey(key), key),
                Ok(None)
            );
        }
        for key in 0..count {
            assert_eq!(maps.get(map, &ForcedCollisionKey(key)), Some(&key));
        }
        assert_eq!(maps.len(map), count as usize);
        assert!(maps.retained_nodes() >= count as usize);

        for key in 0..count {
            assert_eq!(
                maps.remove(&mut map, &ForcedCollisionKey(key)),
                Ok(Some(key))
            );
        }
        assert_eq!(maps.len(map), 0);
    });
}

#[test]
fn forced_hash_collisions_preserve_overlay_and_composition_oracles() {
    with_maps::<ForcedCollisionKey, u32, ForcedCollisionRouting, _>(|maps| {
        let mut left = Map::EMPTY;
        let mut right = Map::EMPTY;
        for key in 0..256 {
            maps.insert(&mut left, ForcedCollisionKey(key), key)
                .unwrap();
            maps.insert(&mut right, ForcedCollisionKey(key), 10_000 + key)
                .unwrap();
        }
        let mut overlay = left;
        maps.overlay(&mut overlay, right).unwrap();
        for key in 0..256 {
            assert_eq!(
                maps.get(overlay, &ForcedCollisionKey(key)),
                Some(&(10_000 + key))
            );
        }

        let mut composition =
            Composition::new(Identical::Combine, |_: &mut (), left: &u32, right: &u32| {
                Ok::<_, shapelint_driver::contracts::graph::CapacityError>(*left + *right)
            });
        let composed = composition
            .compose(maps, &mut (), left, right)
            .expect("composition succeeds");
        for key in 0..256 {
            assert_eq!(
                maps.get(composed, &ForcedCollisionKey(key)),
                Some(&(10_000 + 2 * key))
            );
        }
    });
}

#[test]
fn forced_hash_collisions_retain_bounded_patricia_nodes() {
    let observations = [8, 16, 32, 64].map(|count| {
        with_maps::<ForcedCollisionKey, u32, ForcedCollisionRouting, _>(|maps| {
            let mut map = Map::EMPTY;
            for key in 0..count {
                maps.insert(&mut map, ForcedCollisionKey(key), key).unwrap();
            }
            let retained = maps.retained_nodes();
            assert_eq!(maps.len(map), count as usize);
            eprintln!("forced collision entries={count}, retained_nodes={retained}");
            retained
        })
    });
    assert!(
        observations.windows(2).all(|pair| pair[0] < pair[1]),
        "{observations:?}"
    );
}
