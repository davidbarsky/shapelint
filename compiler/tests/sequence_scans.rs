#![feature(rustc_private)]

use std::convert::Infallible;

use shapelint_driver::sequence::{Scan, Sequence, with_sequences};

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum Edit {
    Append(u8),
    Prepend(u8),
    Slice { start: u8, end: u8 },
    Save,
    Restore,
    Input(u64),
}

#[hegel::test(print_blob = true)]
fn scans_match_sequential_folds_across_edits_and_input_states(tc: hegel::TestCase) {
    let edits = tc.draw(hegel::generators::default::<Vec<Edit>>());
    with_sequences(|sequences| {
        let mut context = (sequences, 0usize);
        let mut actual = Sequence::EMPTY;
        let mut expected = Vec::new();
        let mut saved = (actual.clone(), expected.clone());
        let mut input = 0u64;
        let mut scan = Scan::new(|context: &mut (_, usize), state: u64, value: &u8| {
            context.1 += 1;
            Ok::<_, Infallible>(state.wrapping_mul(257).wrapping_add(u64::from(*value) + 1))
        });
        for edit in edits {
            match edit {
                Edit::Append(value) => {
                    actual = context.0.push(actual, value).expect("append");
                    expected.push(value);
                }
                Edit::Prepend(value) => {
                    let prefix = context.0.from_iter([value]).expect("prefix");
                    actual = context.0.append(prefix, actual).expect("prepend");
                    expected.insert(0, value);
                }
                Edit::Slice { start, end } => {
                    let start = usize::from(start).min(expected.len());
                    let end = usize::from(end).min(expected.len()).max(start);
                    actual = context
                        .0
                        .slice(actual, start..end)
                        .expect("capacity")
                        .expect("valid slice");
                    expected = expected[start..end].to_vec();
                }
                Edit::Save => saved = (actual.clone(), expected.clone()),
                Edit::Restore => (actual, expected) = saved.clone(),
                Edit::Input(value) => input = value,
            }
            let result = scan
                .apply(&mut context, |context| &context.0, actual, input, ())
                .expect("scan");
            let expected = expected.iter().fold(input, |state, value| {
                state.wrapping_mul(257).wrapping_add(u64::from(*value) + 1)
            });
            assert_eq!(result, expected);
            let completed = context.1;
            assert_eq!(
                scan.apply(&mut context, |context| &context.0, actual, input, ())
                    .expect("repeated scan"),
                expected
            );
            assert_eq!(context.1, completed);
        }
    });
}

#[test]
fn growing_prefixes_apply_each_leaf_once_without_reassociating() {
    with_sequences(|sequences| {
        let mut context = (sequences, 0usize);
        let mut sequence = Sequence::EMPTY;
        let mut expected = 7u64;
        let mut scan = Scan::new(|context: &mut (_, usize), state: u64, value: &u64| {
            context.1 += 1;
            Ok::<_, Infallible>(state.wrapping_mul(31).wrapping_sub(*value))
        });
        for value in 0..10_000u64 {
            sequence = context.0.push(sequence, value).expect("append");
            expected = expected.wrapping_mul(31).wrapping_sub(value);
            assert_eq!(
                scan.apply(&mut context, |context| &context.0, sequence, 7, ())
                    .expect("scan"),
                expected
            );
            assert_eq!(
                context.1,
                usize::try_from(value + 1).expect("test size fits")
            );
        }
    });
}

#[test]
fn shared_fragments_are_evaluated_for_their_own_input_state() {
    with_sequences(|mut sequences| {
        let fragment = sequences.from_iter([1u64, 2, 3]).unwrap();
        let sequence = sequences
            .append(fragment, fragment)
            .expect("repeat fragment");
        let mut context = (sequences, Vec::new());
        let mut scan = Scan::new(
            |context: &mut (_, Vec<(u64, u64)>), state: u64, value: &u64| {
                context.1.push((state, *value));
                Ok::<_, Infallible>(state * 10 + value)
            },
        );
        assert_eq!(
            scan.apply(&mut context, |context| &context.0, sequence, 0, ())
                .expect("scan"),
            123123
        );
        assert_eq!(
            context.1,
            vec![(0, 1), (1, 2), (12, 3), (123, 1), (1231, 2), (12312, 3)]
        );
    });
}

#[test]
fn failed_scan_retains_completed_children_for_retry() {
    #[derive(Debug, PartialEq, Eq)]
    struct Interrupted;
    with_sequences(|mut sequences| {
        let sequence = sequences.from_iter([1u64, 2, 3, 4]).unwrap();
        let mut scan = Scan::new(
            |context: &mut (_, Option<u64>, Vec<u64>), state: u64, value: &u64| {
                context.2.push(*value);
                if context.1 == Some(*value) {
                    return Err(Interrupted);
                }
                Ok(state * 10 + value)
            },
        );
        let mut context = (sequences, Some(3), Vec::new());
        assert_eq!(
            scan.apply(&mut context, |context| &context.0, sequence, 0, ()),
            Err(Interrupted)
        );
        assert_eq!(context.2, vec![1, 2, 3]);
        context.1 = None;
        assert_eq!(
            scan.apply(&mut context, |context| &context.0, sequence, 0, ()),
            Ok(1234)
        );
        assert_eq!(context.2, vec![1, 2, 3, 3, 4]);
    });
}
