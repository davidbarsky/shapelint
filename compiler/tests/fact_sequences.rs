#![feature(rustc_private)]

extern crate rustc_data_structures;

use rustc_data_structures::fx::FxHashSet;
use std::cell::Cell;
use std::rc::Rc;

use shapelint_driver::contracts::graph::CapacityError;
use shapelint_driver::sequence::{
    Part, Rewrite, Selection, Sequence, Sequences, Transform, with_sequences,
};

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum Edit {
    Append(u8),
    Replace { from: u8, to: u8 },
    Remove(u8),
    Save,
    Restore,
}

struct Replacement {
    summarized: Rc<Cell<usize>>,
    visited: Rc<Cell<usize>>,
}

impl<'g, T: Copy + Eq + std::hash::Hash> Rewrite<'g, T> for Replacement {
    type Summary = FxHashSet<T>;
    type Context = Option<(T, Option<T>)>;
    type Error = CapacityError;

    fn summarize(
        &mut self,
        _: &mut Sequences<'g, T>,
        part: Part<'_, T, FxHashSet<T>>,
    ) -> Result<FxHashSet<T>, Self::Error> {
        self.summarized.set(self.summarized.get() + 1);
        Ok(match part {
            Part::Leaf(value) => std::iter::once(*value).collect(),
            Part::Branch(left, right) => left.union(right).copied().collect(),
        })
    }

    fn normalize(
        &mut self,
        _: &mut Sequences<'g, T>,
        summary: &FxHashSet<T>,
        context: &Self::Context,
    ) -> Result<Self::Context, Self::Error> {
        Ok(match context {
            Some((from, _)) if summary.contains(from) => *context,
            _ => None,
        })
    }

    fn select(
        &mut self,
        _: &mut Sequences<'g, T>,
        _: &FxHashSet<T>,
        context: &Self::Context,
    ) -> Result<Selection, Self::Error> {
        Ok(match context {
            None => Selection::Keep,
            Some(_) => Selection::Visit,
        })
    }

    fn value(
        &mut self,
        _: &mut Sequences<'g, T>,
        value: &T,
        context: &Self::Context,
    ) -> Result<Option<T>, Self::Error> {
        let Some((from, replacement)) = context else {
            panic!("untouched fragments never visit a value");
        };
        assert!(value == from);
        self.visited.set(self.visited.get() + 1);
        Ok(*replacement)
    }
}

#[hegel::test(print_blob = true)]
fn summary_pruned_edits_match_the_independent_ordered_model(tc: hegel::TestCase) {
    let edits = tc.draw(hegel::generators::default::<Vec<Edit>>());
    with_sequences::<u8, _>(|mut arena| {
        let mut sequence = Sequence::EMPTY;
        let mut expected = Vec::new();
        let mut saved = (sequence.clone(), expected.clone());
        for edit in edits {
            let (from, replacement) = match edit {
                Edit::Append(value) => {
                    sequence = arena.push(sequence, value).expect("sequence fits");
                    expected.push(value);
                    continue;
                }
                Edit::Save => {
                    saved = (sequence.clone(), expected.clone());
                    continue;
                }
                Edit::Restore => {
                    sequence = saved.0.clone();
                    expected = saved.1.clone();
                    continue;
                }
                Edit::Replace { from, to } => (from, Some(to)),
                Edit::Remove(value) => (value, None),
            };
            let before = sequence.clone();
            let previous = expected.clone();
            let visited = Rc::new(Cell::new(0));
            let mut transform = Transform::new(Replacement {
                summarized: Rc::new(Cell::new(0)),
                visited: Rc::clone(&visited),
            });
            sequence = transform
                .apply(&mut arena, sequence, Some((from, replacement)))
                .expect("infallible model edit");
            expected = expected
                .into_iter()
                .filter_map(|value| match value == from {
                    true => replacement,
                    false => Some(value),
                })
                .collect();
            assert_eq!(arena.iter(sequence).copied().collect::<Vec<_>>(), expected);
            assert_eq!(arena.iter(before).copied().collect::<Vec<_>>(), previous);
            assert_eq!(
                visited.get(),
                previous
                    .iter()
                    .copied()
                    .filter(|value| *value == from)
                    .collect::<FxHashSet<_>>()
                    .len()
            );
        }
    });
}

#[test]
fn unchanged_sequence_edits_reuse_completed_summaries() {
    with_sequences::<u32, _>(|mut arena| {
        let sequence = arena.from_iter(0..10_000).unwrap();
        let summarized = Rc::new(Cell::new(0));
        let visited = Rc::new(Cell::new(0));
        let mut transform = Transform::new(Replacement {
            summarized: Rc::clone(&summarized),
            visited: Rc::clone(&visited),
        });
        let unchanged = transform
            .apply(&mut arena, sequence, None)
            .expect("infallible summary");
        let completed = summarized.get();
        let unchanged = transform
            .apply(&mut arena, unchanged, None)
            .expect("infallible edit");
        assert_eq!(summarized.get(), completed);
        assert_eq!(visited.get(), 0);
        assert_eq!(
            arena.iter(unchanged).copied().collect::<Vec<_>>(),
            (0..10_000).collect::<Vec<_>>()
        );
    });
}

#[test]
fn repeated_normalized_fragment_queries_reuse_completed_edits() {
    with_sequences::<u32, _>(|mut arena| {
        let prefix = arena.from_iter(0..10_000).unwrap();
        let visited = Rc::new(Cell::new(0));
        let summarized = Rc::new(Cell::new(0));
        let mut transform = Transform::new(Replacement {
            summarized: Rc::clone(&summarized),
            visited: Rc::clone(&visited),
        });
        let expected = transform
            .apply(&mut arena, prefix, Some((5, Some(7))))
            .expect("first edit");
        assert_eq!(visited.get(), 1);
        let completed = summarized.get();
        for absent in 10_000..10_100 {
            let unchanged = transform
                .apply(&mut arena, prefix, Some((absent, None)))
                .expect("absent edit");
            assert_eq!(
                arena.iter(unchanged).copied().collect::<Vec<_>>(),
                arena.iter(prefix).copied().collect::<Vec<_>>()
            );
            let repeated = transform
                .apply(&mut arena, prefix, Some((5, Some(7))))
                .expect("repeated edit");
            assert_eq!(
                arena.iter(repeated).copied().collect::<Vec<_>>(),
                arena.iter(expected).copied().collect::<Vec<_>>()
            );
        }
        assert_eq!(visited.get(), 1);
        assert_eq!(summarized.get(), completed);
    });
}
