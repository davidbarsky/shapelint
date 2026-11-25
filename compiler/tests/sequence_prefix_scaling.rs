#![feature(rustc_private)]

use shapelint_driver::sequence::{Sequence, with_sequences};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Shape {
    Balanced,
    Pushed,
    Prepended,
    Reversed,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct PrefixCase {
    shape: Shape,
    values: Vec<u32>,
}

#[hegel::test]
fn prefix_preserves_occurrences_across_construction_shapes(tc: hegel::TestCase) {
    let PrefixCase { shape, values } = tc.draw(hegel::generators::default::<PrefixCase>());
    with_sequences(|mut sequences| {
        let (mut sequence, mut expected) = match shape {
            Shape::Balanced => (sequences.from_iter(values.iter().copied()).unwrap(), values),
            Shape::Pushed => {
                let mut sequence = Sequence::EMPTY;
                for &value in &values {
                    sequence = sequences.push(sequence, value).unwrap();
                }
                (sequence, values)
            }
            Shape::Prepended => {
                let mut sequence = Sequence::EMPTY;
                let reversed = values.iter().rev();
                for &value in reversed {
                    let singleton = sequences.push(Sequence::EMPTY, value).unwrap();
                    sequence = sequences.append(singleton, sequence).unwrap();
                }
                (sequence, values)
            }
            Shape::Reversed => {
                let expected: Vec<_> = values.into_iter().rev().collect();
                let sequence = sequences.from_iter(expected.iter().copied()).unwrap();
                (sequence, expected)
            }
        };
        while let Some((prefix, value)) = sequences.prefix(sequence).unwrap() {
            assert_eq!(value, expected.pop().expect("prefix has a final value"));
            sequence = prefix;
        }
        assert!(expected.is_empty());
        assert_eq!(sequence, Sequence::EMPTY);
    });
}

// shapelint: allow(literal-test-cases) These sizes form the prefix-work scaling gate.
#[test]
fn repeated_and_successive_prefixes_bound_split_work() {
    for size in [8_usize, 16, 32, 64, 128] {
        with_sequences(|mut sequences| {
            let values: Vec<_> = (0..size as u32).collect();
            let sequence = sequences.from_iter(values.iter().copied()).unwrap();
            let before_work = sequences.split_operations();
            let before_nodes = sequences.retained_nodes();

            let (prefix, value) = sequences
                .prefix(sequence)
                .unwrap()
                .expect("nonempty sequence has a prefix");
            assert_eq!(value, values[size - 1]);
            let first_work = sequences.split_operations();
            let first_nodes = sequences.retained_nodes();
            for _ in 0..size {
                assert_eq!(sequences.prefix(sequence).unwrap(), Some((prefix, value)));
            }
            assert_eq!(sequences.split_operations(), first_work);
            assert_eq!(sequences.retained_nodes(), first_nodes);

            let mut current = sequence;
            let mut expected = values;
            while let Some((next, value)) = sequences.prefix(current).unwrap() {
                assert_eq!(value, expected.pop().expect("prefix has a final value"));
                current = next;
            }
            assert!(expected.is_empty());
            assert_eq!(current, Sequence::EMPTY);

            let logarithmic = 2 * size.ilog2() as usize + 4;
            let work = sequences.split_operations() - before_work;
            let nodes = sequences.retained_nodes() - before_nodes;
            eprintln!("prefix size {size}: split_entries={work} retained_nodes={nodes}");
            assert!(
                work <= size * logarithmic,
                "prefix split work at {size}: {work}"
            );
            assert!(
                nodes <= size * (2 * logarithmic),
                "prefix retained nodes at {size}: {nodes}"
            );
        });
    }
}

// shapelint: allow(literal-test-cases) These sizes check the first prefix query on pushed roots.
#[test]
fn pushed_sequences_seed_their_first_prefix() {
    for size in [1_usize, 8, 32, 128] {
        with_sequences(|mut sequences| {
            let mut prefix = Sequence::EMPTY;
            for value in 0..(size - 1) as u32 {
                prefix = sequences.push(prefix, value).unwrap();
            }
            let value = size as u32 - 1;
            let sequence = sequences.push(prefix, value).unwrap();
            let before_work = sequences.split_operations();
            let before_nodes = sequences.retained_nodes();

            assert_eq!(sequences.prefix(sequence).unwrap(), Some((prefix, value)));
            assert_eq!(sequences.split_operations(), before_work);
            assert_eq!(sequences.retained_nodes(), before_nodes);
        });
    }
}
