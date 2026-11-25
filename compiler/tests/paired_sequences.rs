#![feature(rustc_private)]

use shapelint_driver::sequence::{Alignment, Paired, PairedPart, Sequence, with_sequences};

#[test]
fn paired_folds_collect_evidence_even_for_shared_inputs() {
    let depth = 1024usize;
    with_sequences(|mut sequences| {
        let mut sequence = Sequence::EMPTY;
        let mut visits = 0;
        let mut paired = Paired::new(
            None,
            |part: PairedPart<'_, usize, usize>| -> Result<_, std::convert::Infallible> {
                Ok(match part {
                    PairedPart::Leaf(left, right) => {
                        assert_eq!(left, right);
                        visits += 1;
                        1
                    }
                    PairedPart::Branch(left, right) => left + right,
                })
            },
        );
        for value in 0..depth {
            sequence = sequences.push(sequence, value).unwrap();
            let result = paired.fold(&sequences, sequence, sequence).unwrap();
            match result {
                Alignment::Aligned(count) => assert_eq!(count, value + 1),
                Alignment::Empty | Alignment::DifferentLengths => {
                    panic!("identical nonempty prefixes align")
                }
            }
        }
        drop(paired);
        assert_eq!(visits, depth);
    });
}

#[hegel::test(print_blob = true)]
fn paired_folds_align_values_across_rope_shapes(tc: hegel::TestCase) {
    let values = tc.draw(hegel::generators::default::<Vec<u8>>());
    with_sequences(|mut sequences| {
        let balanced = sequences.from_iter(values.iter().copied()).unwrap();
        let mut appended = Sequence::default();
        for &value in &values {
            appended = sequences.push(appended, value).unwrap();
        }
        let mut paired = Paired::new(
            None,
            |part: PairedPart<'_, u8, usize>| -> Result<_, std::convert::Infallible> {
                Ok(match part {
                    PairedPart::Leaf(left, right) => {
                        assert_eq!(left, right);
                        1
                    }
                    PairedPart::Branch(left, right) => left + right,
                })
            },
        );
        let result = paired.fold(&sequences, balanced, appended).unwrap();
        match (values.len(), result) {
            (0, Alignment::Empty) => {}
            (length, Alignment::Aligned(count)) => assert_eq!(count, length),
            _ => panic!("equal sequences must align regardless of rope shape"),
        }
    });
}

#[hegel::test(print_blob = true)]
fn paired_folds_preserve_order_for_distinct_sequences(tc: hegel::TestCase) {
    let pairs = tc.draw(hegel::generators::default::<Vec<(u8, u8)>>());
    with_sequences(|mut sequences| {
        let left = sequences.from_iter(pairs.iter().map(|&(a, _)| a)).unwrap();
        let mut right = Sequence::EMPTY;
        for &(_, b) in &pairs {
            right = sequences.push(right, b).unwrap();
        }
        let mut paired = Paired::new(
            None,
            |part: PairedPart<'_, u8, Vec<(u8, u8)>>| -> Result<_, std::convert::Infallible> {
                Ok(match part {
                    PairedPart::Leaf(a, b) => vec![(*a, *b)],
                    PairedPart::Branch(a, b) => a.iter().chain(b).copied().collect(),
                })
            },
        );
        match paired.fold(&sequences, left, right).unwrap() {
            Alignment::Empty => assert!(pairs.is_empty()),
            Alignment::Aligned(actual) => assert_eq!(actual, pairs),
            Alignment::DifferentLengths => panic!("both sequences came from the same pairs"),
        }
    });
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ShorterPrefix {
    Left,
    Right,
}

#[hegel::test]
fn paired_splits_align_maximum_length_ropes(tc: hegel::TestCase) {
    let shorter = tc.draw(hegel::generators::default::<ShorterPrefix>());
    with_sequences(|mut sequences| {
        let mut zeros = sequences.from_iter([0u8]).unwrap();
        let mut ones = sequences.from_iter([1u8]).unwrap();
        let mut zero_block = zeros;
        let mut one_block = ones;
        for _ in 1..usize::BITS {
            zero_block = sequences.append(zero_block, zero_block).unwrap();
            one_block = sequences.append(one_block, one_block).unwrap();
            zeros = sequences.append(zeros, zero_block).unwrap();
            ones = sequences.append(one_block, ones).unwrap();
        }
        let (left, right, expected) = match shorter {
            ShorterPrefix::Left => (zeros, ones, (0, 1)),
            ShorterPrefix::Right => (ones, zeros, (1, 0)),
        };
        let mut paired = Paired::new(None, |part: PairedPart<'_, u8, usize>| match part {
            PairedPart::Leaf(a, b) => {
                assert_eq!((*a, *b), expected);
                Ok(1)
            }
            PairedPart::Branch(a, b) => a.checked_add(*b).ok_or("aligned too many elements"),
        });
        let Alignment::Aligned(count) = paired.fold(&sequences, left, right).unwrap() else {
            panic!("both ropes have maximum length")
        };
        assert_eq!(count, usize::MAX);
    });
}

#[test]
fn retrying_a_paired_fold_reuses_only_successful_subtrees() {
    with_sequences(|mut sequences| {
        let left = sequences.from_iter([0u8, 1]).unwrap();
        let right = sequences.from_iter([2u8, 3]).unwrap();
        let mut attempted = Vec::new();
        let mut fail = Some(());
        let mut paired = Paired::new(None, |part: PairedPart<'_, u8, usize>| match part {
            PairedPart::Leaf(a, b) => {
                attempted.push((*a, *b));
                if *a == 1
                    && let Some(()) = fail.take()
                {
                    return Err("try again");
                }
                Ok(1)
            }
            PairedPart::Branch(a, b) => Ok(a + b),
        });
        let Err(error) = paired.fold(&sequences, left, right) else {
            panic!("the operation should fail on its second leaf");
        };
        assert_eq!(error, "try again");
        let Alignment::Aligned(count) = paired.fold(&sequences, left, right).unwrap() else {
            panic!("the retry should finish both leaves");
        };
        assert_eq!(count, 2);
        drop(paired);
        assert_eq!(attempted, [(0, 2), (1, 3), (1, 3)]);
    });
}

#[test]
fn paired_operations_keep_independent_results_for_shared_inputs() {
    with_sequences(|mut sequences| {
        let sequence = sequences.from_iter([7u8]).unwrap();
        let mut count = Paired::new(
            None,
            |part: PairedPart<'_, u8, usize>| -> Result<_, std::convert::Infallible> {
                Ok(match part {
                    PairedPart::Leaf(_, _) => 1,
                    PairedPart::Branch(left, right) => left + right,
                })
            },
        );
        let mut doubled = Paired::new(
            None,
            |part: PairedPart<'_, u8, usize>| -> Result<_, std::convert::Infallible> {
                Ok(match part {
                    PairedPart::Leaf(_, _) => 2,
                    PairedPart::Branch(left, right) => left + right,
                })
            },
        );
        let Alignment::Aligned(first) = count.fold(&sequences, sequence, sequence).unwrap() else {
            panic!("nonempty equal inputs align");
        };
        let Alignment::Aligned(second) = doubled.fold(&sequences, sequence, sequence).unwrap()
        else {
            panic!("nonempty equal inputs align");
        };
        let Alignment::Aligned(repeated) = count.fold(&sequences, sequence, sequence).unwrap()
        else {
            panic!("nonempty equal inputs align");
        };
        assert_eq!((first, second, repeated), (1, 2, 1));
    });
}
