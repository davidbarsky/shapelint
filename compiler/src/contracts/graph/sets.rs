use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::ops::Index;

use rustc_data_structures::fx::FxHasher;

use crate::arena::{ArenaId, Intern};
use crate::contracts::graph::CapacityError;
use crate::memo::Memo;

fn hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = FxHasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct SetId<'g, T> {
    index: u32,
    brand: PhantomData<fn(&'g T) -> &'g T>,
}
impl<T> Copy for SetId<'_, T> {}
impl<T> Clone for SetId<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> SetId<'_, T> {
    #[shapelint_tool::arena(empty)]
    pub const EMPTY: Self = Self {
        index: 0,
        brand: PhantomData,
    };
}
impl<'g, T: Eq + Hash> ArenaId for SetId<'g, T> {
    fn from_index(index: u32) -> Self {
        Self {
            index,
            brand: PhantomData,
        }
    }

    fn index(self) -> u32 {
        self.index
    }
}

impl<T> Default for SetId<'_, T> {
    fn default() -> Self {
        Self::EMPTY
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum NodeKind<'g, T> {
    Empty,
    Leaf(T),
    Branch(SetId<'g, T>, SetId<'g, T>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ValueId(u32);
impl ArenaId for ValueId {
    fn from_index(index: u32) -> Self {
        Self(index)
    }

    fn index(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Node<'g, T> {
    pub kind: NodeKind<'g, T>,
    pub len: usize,
    key: ValueId,
}

struct Split<'g, T> {
    mask: u32,
    left: SetId<'g, T>,
    right: SetId<'g, T>,
}

#[derive(Clone, Copy)]
enum Inclusion {
    Included,
    Missing,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Combination {
    Union,
    Intersection,
}

/// Interns compressed identity tries so equal sets share one root.
pub struct Sets<'g, T> {
    values: Intern<ValueId, T>,
    #[shapelint_tool::arena(storage)]
    #[shapelint_tool::arena_backends(boxcar, hashbrown, lock_api)]
    nodes: Intern<SetId<'g, T>, Node<'g, T>>,
    #[shapelint_tool::arena(memo)]
    combinations: Memo<(Combination, SetId<'g, T>, SetId<'g, T>), SetId<'g, T>>,
    #[shapelint_tool::arena(memo)]
    subsets: Memo<(SetId<'g, T>, SetId<'g, T>), Inclusion>,
    pub work: Work,
}

/// Counts calls through this handle, including recursive visits and cache hits.
/// Each counter saturates at [`usize::MAX`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    pub combination_visits: usize,
    pub subset_visits: usize,
}

impl<T: Eq + Hash> Sets<'_, T> {
    // shapelint: allow(shallow-helper) Canonical intern tables stay private while measurements observe their storage.
    pub fn retained_nodes(&self) -> usize {
        self.nodes.len()
    }

    /// Returns the total number of cached operations, saturating at [`usize::MAX`].
    // shapelint: allow(shallow-helper) Observers cannot mutate shared operation caches.
    pub fn memo_entries(&self) -> usize {
        self.combinations.len().saturating_add(self.subsets.len())
    }

    pub(crate) fn new() -> Self {
        Self {
            values: Intern::new(),
            nodes: Intern::with_first(Node {
                kind: NodeKind::Empty,
                len: 0,
                key: ValueId(0),
            }),
            combinations: Memo::new(),
            subsets: Memo::new(),
            work: Work::default(),
        }
    }
}

pub struct Cursor<'g, T> {
    pending: Vec<SetId<'g, T>>,
}
impl<'g, T> From<SetId<'g, T>> for Cursor<'g, T> {
    fn from(root: SetId<'g, T>) -> Self {
        Self {
            pending: vec![root],
        }
    }
}

impl<'g, T: Copy + Eq + Hash> Cursor<'g, T> {
    pub fn next(&mut self, sets: &impl Index<SetId<'g, T>, Output = Node<'g, T>>) -> Option<T> {
        while let Some(id) = self.pending.pop() {
            match sets[id].kind {
                NodeKind::Empty => {}
                NodeKind::Leaf(value) => return Some(value),
                NodeKind::Branch(left, right) => {
                    self.pending.push(right);
                    self.pending.push(left);
                }
            }
        }
        None
    }
}

/// Prevents set identities from entering another collection or escaping their owner.
pub fn with_sets<T: Eq + Hash, R>(f: impl for<'g> FnOnce(&mut Sets<'g, T>) -> R) -> R {
    let mut sets = Sets::new();
    f(&mut sets)
}

impl<'g, T: Eq + Hash> Index<SetId<'g, T>> for Sets<'g, T> {
    type Output = Node<'g, T>;

    fn index(&self, id: SetId<'g, T>) -> &Self::Output {
        self.nodes.get(id)
    }
}

impl<'g, T: Copy + Eq + Hash> Sets<'g, T> {
    fn branch(
        &mut self,
        left: SetId<'g, T>,
        right: SetId<'g, T>,
    ) -> Result<SetId<'g, T>, CapacityError> {
        let len = self
            .nodes
            .get(left)
            .len
            .checked_add(self.nodes.get(right).len)
            .ok_or(CapacityError::Sets)?;
        self.nodes.intern(
            Node {
                kind: NodeKind::Branch(left, right),
                len,
                key: self.nodes.get(left).key,
            },
            CapacityError::Sets,
        )
    }

    fn split(&self, root: SetId<'g, T>) -> Option<Split<'g, T>> {
        match self.nodes.get(root).kind {
            NodeKind::Branch(left, right) => {
                // combine builds each branch from the zero and one partitions of the same bit.
                let mask = (self.nodes.get(left).key.0 ^ self.nodes.get(right).key.0)
                    .isolate_highest_one();
                Some(Split { mask, left, right })
            }
            NodeKind::Empty | NodeKind::Leaf(_) => None,
        }
    }

    pub fn insert(&mut self, root: SetId<'g, T>, value: T) -> Result<SetId<'g, T>, CapacityError> {
        let key = self.values.intern(value, CapacityError::Sets)?;
        let leaf = self.nodes.intern(
            Node {
                kind: NodeKind::Leaf(value),
                len: 1,
                key,
            },
            CapacityError::Sets,
        )?;
        self.combine(Combination::Union, root, leaf)
    }

    pub fn contains(&self, mut root: SetId<'g, T>, value: T) -> Option<()> {
        let key = self
            .values
            .find_by(hash(&value), |existing| (existing == &value).then_some(()))?;
        loop {
            match self[root].kind {
                NodeKind::Empty => return None,
                NodeKind::Leaf(_) => return (self[root].key == key).then_some(()),
                NodeKind::Branch(left, right) => {
                    let mask = (self[left].key.0 ^ self[right].key.0).isolate_highest_one();
                    root = match key.0 & mask {
                        0 => left,
                        _ => right,
                    };
                }
            }
        }
    }

    pub(crate) fn members(
        &mut self,
        part: crate::sequence::Part<'_, T, SetId<'g, T>>,
    ) -> Result<SetId<'g, T>, CapacityError> {
        match part {
            crate::sequence::Part::Leaf(value) => self.insert(SetId::EMPTY, *value),
            crate::sequence::Part::Branch(left, right) => {
                self.combine(Combination::Union, *left, *right)
            }
        }
    }

    pub fn combine(
        &mut self,
        operation: Combination,
        left: SetId<'g, T>,
        right: SetId<'g, T>,
    ) -> Result<SetId<'g, T>, CapacityError> {
        self.work.combination_visits = self.work.combination_visits.saturating_add(1);
        if left == right {
            return Ok(left);
        }
        if left == SetId::EMPTY || right == SetId::EMPTY {
            return Ok(match operation {
                Combination::Union if left == SetId::EMPTY => right,
                Combination::Union => left,
                Combination::Intersection => SetId::EMPTY,
            });
        }
        if let Some(result) = self.combinations.get(&(operation, left, right)) {
            return Ok(result);
        }
        let result = if let Some(result) = self.combinations.get(&(operation, right, left)) {
            result
        } else {
            let left_node = *self.nodes.get(left);
            let right_node = *self.nodes.get(right);
            let left_branch = self.split(left);
            let right_branch = self.split(right);
            let split = left_branch
                .as_ref()
                .map(|b| b.mask)
                .max(right_branch.as_ref().map(|b| b.mask));
            let differing = (left_node.key.0 ^ right_node.key.0).isolate_highest_one();
            if differing != 0 && Some(differing) > split {
                match operation {
                    Combination::Intersection => SetId::EMPTY,
                    Combination::Union => {
                        let (a, b) = if left_node.key.0 & differing == 0 {
                            (left, right)
                        } else {
                            (right, left)
                        };
                        self.branch(a, b)?
                    }
                }
            } else if let Some(mask) = split {
                let (a, b) = match left_branch {
                    Some(branch) if branch.mask == mask => (branch.left, branch.right),
                    _ if left_node.key.0 & mask == 0 => (left, SetId::EMPTY),
                    _ => (SetId::EMPTY, left),
                };
                let (c, d) = match right_branch {
                    Some(branch) if branch.mask == mask => (branch.left, branch.right),
                    _ if right_node.key.0 & mask == 0 => (right, SetId::EMPTY),
                    _ => (SetId::EMPTY, right),
                };
                let a = self.combine(operation, a, c)?;
                let b = self.combine(operation, b, d)?;
                match (a == SetId::EMPTY, b == SetId::EMPTY) {
                    (true, _) => b,
                    (_, true) => a,
                    (false, false) => self.branch(a, b)?,
                }
            } else {
                // Both inputs are singletons with the same value identity.
                left
            }
        };
        self.combinations.insert((operation, left, right), result);
        Ok(result)
    }

    pub fn subset(&mut self, left: SetId<'g, T>, right: SetId<'g, T>) -> Option<()> {
        self.work.subset_visits = self.work.subset_visits.saturating_add(1);
        if let Some(result) = self.subsets.get(&(left, right)) {
            return match result {
                Inclusion::Included => Some(()),
                Inclusion::Missing => None,
            };
        }
        let result = if left == right || left == SetId::EMPTY {
            Inclusion::Included
        } else if right == SetId::EMPTY || self.nodes.get(left).len > self.nodes.get(right).len {
            Inclusion::Missing
        } else if let Some(Split {
            mask,
            left: c,
            right: d,
        }) = self.split(right)
        {
            let left_key = self.nodes.get(left).key.0;
            let differing = (left_key ^ self.nodes.get(right).key.0).isolate_highest_one();
            match self.split(left) {
                _ if differing > mask => Inclusion::Missing,
                Some(branch) if branch.mask > mask => Inclusion::Missing,
                Some(branch) if branch.mask == mask => {
                    match (self.subset(branch.left, c), self.subset(branch.right, d)) {
                        (Some(()), Some(())) => Inclusion::Included,
                        _ => Inclusion::Missing,
                    }
                }
                _ => {
                    let child = if left_key & mask == 0 { c } else { d };
                    match self.subset(left, child) {
                        Some(()) => Inclusion::Included,
                        None => Inclusion::Missing,
                    }
                }
            }
        } else {
            // A singleton has no proper nonempty subset.
            Inclusion::Missing
        };
        self.subsets.insert((left, right), result);
        match result {
            Inclusion::Included => Some(()),
            Inclusion::Missing => None,
        }
    }

    pub fn iter(&self, root: SetId<'g, T>) -> impl Iterator<Item = T> + '_ {
        let mut cursor = Cursor::from(root);
        std::iter::from_fn(move || cursor.next(self))
    }
}
