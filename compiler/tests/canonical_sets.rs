#![feature(rustc_private)]

use std::collections::HashSet;
use std::hash::{Hash, Hasher};

use shapelint_driver::contracts::graph::sets::{Combination, NodeKind, SetId, with_sets};

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum Key {
    Spread(u8),
    Collision(u8),
}

impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Key::Spread(value) => (0_u8, value).hash(state),
            Key::Collision(_) => 1_u8.hash(state),
        }
    }
}

#[derive(Debug, hegel::DefaultGenerator)]
enum CheckedSet {
    Left,
    Right,
    Union,
    Intersection,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Inputs {
    operation: CheckedSet,
    left: Vec<Key>,
    right: Vec<Key>,
    noise: Vec<Key>,
    probe: Key,
}

#[hegel::test(print_blob = true)]
fn canonical_operations_match_independent_sets(tc: hegel::TestCase) {
    let Inputs {
        operation,
        left,
        right,
        noise,
        probe,
    } = tc.draw(hegel::generators::default::<Inputs>());
    let expected_left: HashSet<_> = left.iter().copied().collect();
    let expected_right: HashSet<_> = right.iter().copied().collect();
    let expected_union: HashSet<_> = expected_left.union(&expected_right).copied().collect();
    let expected_intersection: HashSet<_> = expected_left
        .intersection(&expected_right)
        .copied()
        .collect();
    with_sets(|sets| {
        let mut first = SetId::EMPTY;
        for value in &left {
            first = sets.insert(first, *value).unwrap();
        }
        for value in noise {
            sets.insert(SetId::EMPTY, value).unwrap();
        }
        let mut second = SetId::EMPTY;
        for value in &right {
            second = sets.insert(second, *value).unwrap();
        }
        let mut reverse_first = SetId::EMPTY;
        let reversed = left.iter().rev();
        for value in reversed {
            reverse_first = sets.insert(reverse_first, *value).unwrap();
        }
        let mut reverse_second = SetId::EMPTY;
        let reversed = right.iter().rev();
        for value in reversed {
            reverse_second = sets.insert(reverse_second, *value).unwrap();
        }
        assert_eq!(first, reverse_first);
        assert_eq!(second, reverse_second);
        let union = sets.combine(Combination::Union, first, second).unwrap();
        let intersection = sets
            .combine(Combination::Intersection, first, second)
            .unwrap();
        assert_eq!(
            union,
            sets.combine(Combination::Union, second, first).unwrap()
        );
        assert_eq!(
            intersection,
            sets.combine(Combination::Intersection, second, first)
                .unwrap()
        );
        assert_eq!(
            union,
            sets.combine(Combination::Union, first, second).unwrap()
        );
        assert_eq!(
            intersection,
            sets.combine(Combination::Intersection, first, second)
                .unwrap()
        );
        let mut rebuilt_union = SetId::EMPTY;
        for value in &expected_union {
            rebuilt_union = sets.insert(rebuilt_union, *value).unwrap();
        }
        let mut rebuilt_intersection = SetId::EMPTY;
        for value in &expected_intersection {
            rebuilt_intersection = sets.insert(rebuilt_intersection, *value).unwrap();
        }
        assert_eq!(union, rebuilt_union);
        assert_eq!(intersection, rebuilt_intersection);
        assert_eq!(
            sets.subset(first, second),
            expected_left.is_subset(&expected_right).then_some(())
        );
        assert_eq!(
            sets.subset(second, first),
            expected_right.is_subset(&expected_left).then_some(())
        );
        let (root, expected) = match operation {
            CheckedSet::Left => (first, &expected_left),
            CheckedSet::Right => (second, &expected_right),
            CheckedSet::Union => (union, &expected_union),
            CheckedSet::Intersection => (intersection, &expected_intersection),
        };
        assert_eq!(sets.iter(root).collect::<HashSet<_>>(), *expected);
        assert_eq!(
            sets.contains(root, probe),
            expected.contains(&probe).then_some(())
        );
        let values = left.iter().chain(&right);
        for value in values {
            assert_eq!(
                sets.contains(root, *value),
                expected.contains(value).then_some(())
            );
        }
        let mut pending = vec![root];
        let mut nodes = 0;
        while let Some(node) = pending.pop() {
            match sets[node].kind {
                NodeKind::Empty => {}
                NodeKind::Leaf(_) => nodes += 1,
                NodeKind::Branch(left, right) => {
                    nodes += 1;
                    pending.extend([left, right]);
                }
            }
        }
        assert_eq!(nodes, expected.len().saturating_mul(2).saturating_sub(1));
        assert_eq!(sets[root].len, expected.len());
    });
}
