#![feature(rustc_private)]

use std::thread;

use shapelint_driver::sequence::with_sequences;

#[test]
fn shared_sequence_views_intern_equal_content_concurrently() {
    with_sequences(|mut sequences| {
        sequences.from_iter(["alpha"]).unwrap();
        let initial = sequences.allocated_nodes();
        let mut first = sequences.share();
        let mut second = sequences.share();
        thread::scope(|scope| {
            let left = scope.spawn(|| first.from_iter(["alpha", "beta", "gamma"]));
            let right = scope.spawn(|| second.from_iter(["alpha", "beta", "gamma"]));
            let left = left.join().unwrap().unwrap();
            let right = right.join().unwrap().unwrap();
            assert_eq!(left, right);
        });
        assert_eq!(sequences.allocated_nodes(), initial);
        assert_eq!(
            initial + first.allocated_nodes() + second.allocated_nodes(),
            sequences.retained_nodes()
        );
    });
}

#[test]
fn sequence_references_survive_shared_appends() {
    with_sequences(|mut sequences| {
        let original = sequences
            .from_iter([String::from("stable"), String::from("reference")])
            .unwrap();
        let stable = sequences.get(original, 0).unwrap();
        let mut shared = sequences.share();
        for index in 0..10_000 {
            shared.push(original, format!("value {index}")).unwrap();
        }
        assert_eq!(stable.as_str(), "stable");
    });
}

#[test]
fn equal_content_from_different_tree_construction_has_one_identity() {
    with_sequences(|mut sequences| {
        let balanced = sequences.from_iter([1, 2, 3, 4, 5]).unwrap();
        let mut appended = shapelint_driver::sequence::Sequence::default();
        for value in [1, 2, 3, 4, 5] {
            appended = sequences.push(appended, value).unwrap();
        }

        assert_eq!(balanced, appended);
        assert_eq!(
            sequences.iter(balanced).copied().collect::<Vec<_>>(),
            [1, 2, 3, 4, 5]
        );
    });
}
