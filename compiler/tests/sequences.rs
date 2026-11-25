#![feature(rustc_private)]

use std::hash::{Hash, Hasher};

use shapelint_driver::sequence::{Mapper, Sequence, with_sequences};

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Edits {
    initial: Vec<u8>,
    edits: Vec<(u8, u8)>,
}

#[hegel::test(print_blob = true)]
fn rejected_edits_at_the_end_leave_split_work_unchanged(tc: hegel::TestCase) {
    let (first, rest, replacement) = tc.draw(hegel::generators::default::<(u8, Vec<u8>, u8)>());
    with_sequences(|mut sequences| {
        let sequence = sequences
            .from_iter(std::iter::once(first).chain(rest))
            .unwrap();
        let end = sequences.len(sequence);
        let before = sequences.split_operations();
        assert_eq!(sequences.remove(sequence, end).unwrap(), None);
        assert_eq!(sequences.split_operations(), before);
        assert_eq!(sequences.replace(sequence, end, replacement).unwrap(), None);
        assert_eq!(sequences.split_operations(), before);
    });
}

#[hegel::test(print_blob = true)]
fn shared_edits_preserve_order_and_previous_roots(tc: hegel::TestCase) {
    let Edits { initial, edits } = tc.draw(hegel::generators::default::<Edits>());
    with_sequences(|mut sequences| {
        let mut expected = initial.clone();
        let mut sequence = sequences.from_iter(initial).unwrap();
        for (position, value) in edits {
            let previous = sequence;
            let before = expected.clone();
            let index = usize::from(position) % (expected.len() + 1);
            match value % 4 {
                0 => {
                    sequence = sequences.push(sequence, value).unwrap();
                    expected.push(value);
                }
                1 if index < expected.len() => {
                    let (next, removed) = sequences.remove(sequence, index).unwrap().unwrap();
                    sequence = next;
                    assert_eq!(removed, expected.remove(index));
                }
                2 if index < expected.len() => {
                    sequence = sequences.replace(sequence, index, value).unwrap().unwrap();
                    expected[index] = value;
                }
                _ => {
                    let removed: Vec<_> = sequences
                        .iter(sequence)
                        .enumerate()
                        .filter_map(|(index, item)| (*item == value).then_some(index))
                        .collect();
                    let removed = removed.into_iter().rev();
                    for index in removed {
                        sequence = sequences.remove(sequence, index).unwrap().unwrap().0;
                    }
                    expected.retain(|item| *item != value);
                }
            }
            assert_eq!(
                sequences.iter(previous).copied().collect::<Vec<_>>(),
                before
            );
            assert_eq!(
                sequences.iter(sequence).copied().collect::<Vec<_>>(),
                expected
            );
            assert_eq!(
                sequences.iter(sequence).rev().copied().collect::<Vec<_>>(),
                expected.iter().rev().copied().collect::<Vec<_>>()
            );
            let len = sequences.len(sequence);
            let split = usize::from(position) % (len + 1);
            let left = sequences.slice(sequence, 0..split).unwrap().unwrap();
            let right = sequences.slice(sequence, split..len).unwrap().unwrap();
            let rejoined = sequences.append(left, right).unwrap();
            assert_eq!(rejoined, sequence);
        }
    });
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Collision(u8);
impl Hash for Collision {
    fn hash<H: Hasher>(&self, state: &mut H) {
        0u8.hash(state);
    }
}

#[hegel::test(print_blob = true)]
fn equality_uses_exact_contents_across_shapes_and_hash_collisions(tc: hegel::TestCase) {
    let values = tc.draw(hegel::generators::default::<Vec<u8>>());
    let expected_retained_nodes = match values.as_slice() {
        [] => 0,
        [_, ..] => 1,
    };
    with_sequences(|mut sequences| {
        let mut level: Vec<_> = values
            .iter()
            .copied()
            .map(|value| {
                let empty = Sequence::EMPTY;
                sequences.push(empty, Collision(value)).unwrap()
            })
            .collect();
        while level.len() > 1 {
            let mut next = Vec::new();
            let mut chunks = level.chunks_exact(2);
            for pair in &mut chunks {
                next.push(sequences.append(pair[0], pair[1]).unwrap());
            }
            next.extend_from_slice(chunks.remainder());
            level = next;
        }
        let balanced = level.first().copied().unwrap_or_else(|| Sequence::EMPTY);
        let mut appended = Sequence::EMPTY;
        for value in values {
            appended = sequences.push(appended, Collision(value)).unwrap();
            let prefix = sequences
                .slice(balanced, 0..sequences.len(appended))
                .unwrap()
                .unwrap();
            assert_eq!(appended, prefix);
        }
        assert_eq!(balanced, appended);
        let first = sequences.iter(appended).next().cloned();
        match first {
            Some(first) => {
                let replacement = Collision(first.0.wrapping_add(1));
                let changed = sequences
                    .replace(appended, 0, replacement)
                    .unwrap()
                    .unwrap();
                assert_ne!(balanced, changed);
            }
            None => assert_eq!(sequences.len(balanced), 0),
        }
        assert!(sequences.retained_nodes() >= expected_retained_nodes);
    });
}

#[test]
fn sequence_fingerprint_candidates_use_full_equality() {
    with_sequences(|mut sequences| {
        let balanced = sequences
            .from_iter((0..64).map(Collision))
            .expect("balanced sequence");
        let mut appended = Sequence::EMPTY;
        for value in 0..64 {
            appended = sequences
                .push(appended, Collision(value))
                .expect("appended sequence");
        }
        assert_eq!(
            sequences
                .iter(balanced)
                .map(|value| value.0)
                .collect::<Vec<_>>(),
            sequences
                .iter(appended)
                .map(|value| value.0)
                .collect::<Vec<_>>()
        );
        assert_eq!(balanced, appended);
        assert!(sequences.retained_nodes() >= 64);
    });
}

#[test]
fn mapping_growing_prefixes_visits_each_shared_value_once() {
    let visited = std::cell::Cell::new(0usize);
    with_sequences(|mut source| {
        with_sequences(|mut destination| {
            let mut mapper = Mapper::new(|value: &u32| {
                visited.set(visited.get() + 1);
                u64::from(*value) * 2
            });
            let mut sequence = Sequence::EMPTY;
            for value in 0..1024 {
                sequence = source.push(sequence, value).unwrap();
                let mapped = mapper.map(&source, &mut destination, sequence).unwrap();
                assert_eq!(
                    destination.iter(mapped).next_back(),
                    Some(&(u64::from(value) * 2))
                );
            }
            assert_eq!(visited.get(), 1024);
            while source.len(sequence) != 0 {
                sequence = source.remove(sequence, 0).unwrap().unwrap().0;
                let mapped = mapper.map(&source, &mut destination, sequence).unwrap();
                assert_eq!(destination.len(mapped), source.len(sequence));
            }
            assert_eq!(visited.get(), 1024);
        })
    });
}

#[hegel::test(print_blob = true)]
fn mapping_growing_suffixes_reuses_each_shared_leaf(tc: hegel::TestCase) {
    let wrappers = tc.draw(hegel::generators::default::<Vec<()>>());
    let visited = std::cell::Cell::new(0usize);
    with_sequences(|mut source| {
        with_sequences(|mut destination| {
            let mut mapper = Mapper::new(|value: &usize| {
                visited.set(visited.get() + 1);
                *value
            });
            let mut sequence = Sequence::EMPTY;
            let mut expected = Vec::new();
            let wrappers = wrappers.into_iter().enumerate();
            for (value, ()) in wrappers {
                let empty = Sequence::EMPTY;
                let prefix = source.push(empty, value).unwrap();
                sequence = source.append(prefix, sequence).unwrap();
                expected.insert(0, value);
                let mapped = mapper.map(&source, &mut destination, sequence).unwrap();
                assert_eq!(
                    destination.iter(mapped).copied().collect::<Vec<_>>(),
                    expected
                );
                assert_eq!(visited.get(), value + 1);
            }
        })
    });
}

#[test]
fn batch_construction_moves_values_without_cloning_prefixes() {
    #[derive(Debug)]
    struct Value<'a> {
        value: usize,
        clones: &'a std::cell::Cell<usize>,
    }
    impl Clone for Value<'_> {
        fn clone(&self) -> Self {
            self.clones.set(self.clones.get() + 1);
            Self {
                value: self.value,
                clones: self.clones,
            }
        }
    }
    impl PartialEq for Value<'_> {
        fn eq(&self, other: &Self) -> bool {
            self.value == other.value
        }
    }
    impl Eq for Value<'_> {}
    impl Hash for Value<'_> {
        fn hash<H: Hasher>(&self, state: &mut H) {
            self.value.hash(state);
        }
    }
    let clones = std::cell::Cell::new(0);
    with_sequences(|mut sequences| {
        let values = (0..1024).map(|value| Value {
            value,
            clones: &clones,
        });
        let sequence = sequences.from_iter(values).unwrap();
        assert_eq!(sequences.len(sequence), 1024);
        assert_eq!(clones.get(), 0);
    });
}
