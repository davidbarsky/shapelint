//! Canonical ordered values and memoized traversals over their shared fragments.

use parking_lot::Mutex;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::num::NonZeroU32;
use std::ops::Range;
use std::sync::Arc;

use hashbrown::HashTable;
use rustc_data_structures::fx::{FxHashMap, FxHasher};

use crate::arena::CapacityError;
use crate::memo::Memo;

const MULTIPLIER: u128 = 0x100000001b3;

/// Identifies ordered content in one sequence arena.
pub struct Sequence<'g, T> {
    root: Option<RootId>,
    marker: PhantomData<fn(&'g (), T) -> (&'g (), T)>,
}
impl<T> Sequence<'_, T> {
    pub const EMPTY: Self = Self {
        root: None,
        marker: PhantomData,
    };

    fn identity(self) -> u32 {
        match self.root {
            Some(id) => id.0.get(),
            None => 0,
        }
    }
}
impl<T> Default for Sequence<'_, T> {
    fn default() -> Self {
        Self::EMPTY
    }
}
impl<T> Copy for Sequence<'_, T> {}
impl<T> Clone for Sequence<'_, T> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<T> PartialEq for Sequence<'_, T> {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root
    }
}
impl<T> Eq for Sequence<'_, T> {}
impl<T> Hash for Sequence<'_, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.identity().hash(state);
    }
}
impl<T> fmt::Debug for Sequence<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.identity().fmt(f)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct NodeId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct RootId(NonZeroU32);

impl From<RootId> for usize {
    fn from(id: RootId) -> Self {
        id.0.get().abs_diff(1) as usize
    }
}

impl<T> From<RootId> for Sequence<'_, T> {
    fn from(id: RootId) -> Self {
        Self {
            root: Some(id),
            marker: PhantomData,
        }
    }
}

struct Node<T> {
    len: usize,
    height: u32,
    fingerprint: u128,
    power: u128,
    kind: Kind<T>,
}
struct Root<'g, T> {
    node: NodeId,
    previous: Option<RootId>,
    prefix: Mutex<Option<(Sequence<'g, T>, NodeId)>>,
}
#[derive(Clone)]
enum Kind<T> {
    Leaf(T),
    Branch(NodeId, NodeId),
}
#[derive(Clone, Copy)]
enum End {
    Front,
    Back,
}
struct SequenceStore<'g, T> {
    nodes: boxcar::Vec<Node<T>>,
    keys: Mutex<HashTable<(u64, NodeId)>>,
    roots: boxcar::Vec<Root<'g, T>>,
    root_ids: Mutex<FxHashMap<NodeId, RootId>>,
    candidates: Mutex<HashTable<(u64, RootId)>>,
    comparisons: Arc<Mutex<FxHashMap<(Slice, Slice), Comparison>>>,
    joins: Mutex<FxHashMap<(Sequence<'g, T>, Sequence<'g, T>), Sequence<'g, T>>>,
    node_joins: Mutex<FxHashMap<(NodeId, NodeId), NodeId>>,
    splits: Mutex<FxHashMap<(NodeId, usize), (Option<NodeId>, Option<NodeId>)>>,
}

/// Owns one canonical identity for each distinct ordered content.
pub struct Sequences<'g, T> {
    store: Arc<SequenceStore<'g, T>>,
    allocated_nodes: usize,
    marker: PhantomData<fn(&'g ()) -> &'g ()>,
}

/// Gives an arena a fresh lifetime that cannot escape or be shared with another arena.
// shapelint: allow(shallow-helper) The higher-ranked closure gives each arena a fresh identity scope.
pub fn with_sequences<T, R>(f: impl for<'g> FnOnce(Sequences<'g, T>) -> R) -> R {
    let sequences = Sequences::new();
    f(sequences)
}

impl<'g, T> Sequences<'g, T> {
    pub(crate) fn new() -> Self {
        Self {
            store: Arc::new(SequenceStore {
                nodes: boxcar::Vec::new(),
                keys: Mutex::new(HashTable::new()),
                roots: boxcar::Vec::new(),
                root_ids: Mutex::new(FxHashMap::default()),
                candidates: Mutex::new(HashTable::new()),
                comparisons: Arc::new(Mutex::new(FxHashMap::default())),
                joins: Mutex::new(FxHashMap::default()),
                node_joins: Mutex::new(FxHashMap::default()),
                splits: Mutex::new(FxHashMap::default()),
            }),
            allocated_nodes: 0,
            marker: PhantomData,
        }
    }
    pub fn share(&self) -> Self {
        Self {
            store: Arc::clone(&self.store),
            allocated_nodes: 0,
            marker: PhantomData,
        }
    }
    /// Counts canonical nodes retained across all views of this store.
    // shapelint: allow(shallow-helper) This read-only witness keeps the sequence arena private.
    pub fn retained_nodes(&self) -> usize {
        self.store.nodes.count()
    }
    /// Counts nodes inserted through this view. [`Self::share`] starts a fresh count.
    // shapelint: allow(shallow-helper) Only the view that inserts a canonical node can advance its count.
    pub fn allocated_nodes(&self) -> usize {
        self.allocated_nodes
    }
    /// Returns the number of uncached tree split nodes visited by this arena.
    // shapelint: allow(shallow-helper) This work counter keeps the split cache private.
    pub fn split_operations(&self) -> usize {
        self.store.splits.lock().len()
    }
    fn node(&self, sequence: Sequence<'g, T>) -> Option<NodeId> {
        let id = sequence.root?;
        Some(self.store.roots[usize::from(id)].node)
    }
    pub fn len(&self, id: Sequence<'g, T>) -> usize {
        match self.node(id) {
            Some(root) => self.store.nodes[root.0 as usize].len,
            None => 0,
        }
    }
    pub fn get(&self, id: Sequence<'g, T>, mut index: usize) -> Option<&T> {
        let mut node = self.node(id)?;
        if index >= self.store.nodes[node.0 as usize].len {
            return None;
        }
        loop {
            match &self.store.nodes[node.0 as usize].kind {
                Kind::Leaf(value) => return Some(value),
                Kind::Branch(left, right) => {
                    let len = self.store.nodes[(*left).0 as usize].len;
                    if let Some(offset) = index.checked_sub(len) {
                        index = offset;
                        node = *right;
                    } else {
                        node = *left;
                    }
                }
            }
        }
    }
    fn first_value(&self, mut node: NodeId) -> &T {
        loop {
            match &self.store.nodes[node.0 as usize].kind {
                Kind::Leaf(value) => return value,
                Kind::Branch(left, _) => node = *left,
            }
        }
    }
    pub fn iter(&self, id: Sequence<'g, T>) -> Iter<'_, T> {
        let roots: Vec<_> = self.node(id).into_iter().collect();
        Iter {
            nodes: &self.store.nodes,
            front: roots.clone(),
            back: roots,
            remaining: self.len(id),
        }
    }
}

pub struct Cursor<'g, T> {
    pending: Vec<NodeId>,
    marker: PhantomData<fn(&'g (), T) -> (&'g (), T)>,
}
impl<'g, T> From<(&Sequences<'g, T>, Sequence<'g, T>)> for Cursor<'g, T> {
    fn from((arena, id): (&Sequences<'g, T>, Sequence<'g, T>)) -> Self {
        Self {
            pending: arena.node(id).into_iter().collect(),
            marker: PhantomData,
        }
    }
}
impl<'g, T> Cursor<'g, T> {
    pub fn next<'a>(&mut self, arena: &'a Sequences<'g, T>) -> Option<&'a T> {
        while let Some(id) = self.pending.pop() {
            match &arena.store.nodes[id.0 as usize].kind {
                Kind::Leaf(value) => return Some(value),
                Kind::Branch(left, right) => {
                    self.pending.push(*right);
                    self.pending.push(*left);
                }
            }
        }
        None
    }
}

pub struct Iter<'a, T> {
    nodes: &'a boxcar::Vec<Node<T>>,
    front: Vec<NodeId>,
    back: Vec<NodeId>,
    remaining: usize,
}
impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        self.remaining = self.remaining.checked_sub(1)?;
        while let Some(id) = self.front.pop() {
            match &self.nodes[id.0 as usize].kind {
                Kind::Leaf(value) => return Some(value),
                Kind::Branch(left, right) => {
                    self.front.push(*right);
                    self.front.push(*left);
                }
            }
        }
        unreachable!("iterator retains its remaining leaves")
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        (self.remaining, Some(self.remaining))
    }
}
impl<T> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.remaining = self.remaining.checked_sub(1)?;
        while let Some(id) = self.back.pop() {
            match &self.nodes[id.0 as usize].kind {
                Kind::Leaf(value) => return Some(value),
                Kind::Branch(left, right) => {
                    self.back.push(*left);
                    self.back.push(*right);
                }
            }
        }
        unreachable!("iterator retains its remaining leaves")
    }
}
impl<T> ExactSizeIterator for Iter<'_, T> {}

impl<'g, T: Clone + Eq + Hash> Sequences<'g, T> {
    fn leaf(&mut self, value: T) -> Result<NodeId, CapacityError> {
        let mut key_hasher = FxHasher::default();
        (0u8, &value).hash(&mut key_hasher);
        let hash = key_hasher.finish();
        let mut keys = self.store.keys.lock();
        if let Some((_, id)) = keys.find(hash, |(_, id)| {
            match &self.store.nodes[(*id).0 as usize].kind {
                Kind::Leaf(existing) => *existing == value,
                Kind::Branch(..) => false,
            }
        }) {
            return Ok(*id);
        }
        let id =
            NodeId(u32::try_from(self.store.nodes.count()).map_err(|_| CapacityError::Sequences)?);
        self.store.nodes.push(Node {
            len: 1,
            height: 1,
            fingerprint: u128::from(id.0) + 1,
            power: MULTIPLIER,
            kind: Kind::Leaf(value),
        });
        self.allocated_nodes = self.allocated_nodes.saturating_add(1);
        keys.insert_unique(hash, (hash, id), |(hash, _)| *hash);
        Ok(id)
    }
    fn branch(&mut self, left: NodeId, right: NodeId) -> Result<NodeId, CapacityError> {
        let mut key_hasher = FxHasher::default();
        (1u8, left, right).hash(&mut key_hasher);
        let hash = key_hasher.finish();
        let mut keys = self.store.keys.lock();
        if let Some((_, id)) = keys.find(hash, |(_, id)| {
            match self.store.nodes[(*id).0 as usize].kind {
                Kind::Branch(a, b) => a == left && b == right,
                Kind::Leaf(_) => false,
            }
        }) {
            return Ok(*id);
        }
        let a = &self.store.nodes[left.0 as usize];
        let b = &self.store.nodes[right.0 as usize];
        let node = Node {
            len: a.len.checked_add(b.len).ok_or(CapacityError::Sequences)?,
            height: a
                .height
                .max(b.height)
                .checked_add(1)
                .ok_or(CapacityError::Sequences)?,
            fingerprint: a
                .fingerprint
                .wrapping_mul(b.power)
                .wrapping_add(b.fingerprint),
            power: a.power.wrapping_mul(b.power),
            kind: Kind::Branch(left, right),
        };
        let id =
            NodeId(u32::try_from(self.store.nodes.count()).map_err(|_| CapacityError::Sequences)?);
        self.store.nodes.push(node);
        self.allocated_nodes = self.allocated_nodes.saturating_add(1);
        keys.insert_unique(hash, (hash, id), |(hash, _)| *hash);
        Ok(id)
    }
    fn children(&self, id: NodeId) -> (NodeId, NodeId) {
        match self.store.nodes[id.0 as usize].kind {
            Kind::Branch(a, b) => (a, b),
            Kind::Leaf(_) => unreachable!("a taller AVL subtree branches"),
        }
    }
    fn balance(&mut self, left: NodeId, right: NodeId) -> Result<NodeId, CapacityError> {
        let a = self.store.nodes[left.0 as usize].height;
        let b = self.store.nodes[right.0 as usize].height;
        if a.saturating_sub(b) > 1 {
            let (x, y) = self.children(left);
            if self.store.nodes[x.0 as usize].height >= self.store.nodes[y.0 as usize].height {
                let right = self.branch(y, right)?;
                return self.branch(x, right);
            }
            let (c, d) = self.children(y);
            let left = self.branch(x, c)?;
            let right = self.branch(d, right)?;
            return self.branch(left, right);
        }
        if b.saturating_sub(a) > 1 {
            let (x, y) = self.children(right);
            if self.store.nodes[y.0 as usize].height >= self.store.nodes[x.0 as usize].height {
                let left = self.branch(left, x)?;
                return self.branch(left, y);
            }
            let (c, d) = self.children(x);
            let left = self.branch(left, c)?;
            let right = self.branch(d, y)?;
            return self.branch(left, right);
        }
        self.branch(left, right)
    }
    fn join_nodes(&mut self, mut left: NodeId, mut right: NodeId) -> Result<NodeId, CapacityError> {
        let key = (left, right);
        if let Some(id) = self.store.node_joins.lock().get(&key).copied() {
            return Ok(id);
        }
        let mut path = Vec::new();
        let left_height = self.store.nodes[left.0 as usize].height;
        let right_height = self.store.nodes[right.0 as usize].height;
        let result = if left_height >= right_height {
            while self.store.nodes[left.0 as usize]
                .height
                .saturating_sub(right_height)
                > 1
            {
                let (a, b) = self.children(left);
                path.push(a);
                left = b;
            }
            let root = self.branch(left, right)?;
            path.into_iter()
                .rev()
                .try_fold(root, |root, sibling| self.balance(sibling, root))?
        } else {
            while self.store.nodes[right.0 as usize]
                .height
                .saturating_sub(left_height)
                > 1
            {
                let (a, b) = self.children(right);
                path.push(b);
                right = a;
            }
            let root = self.branch(left, right)?;
            path.into_iter()
                .rev()
                .try_fold(root, |root, sibling| self.balance(root, sibling))?
        };
        self.store.node_joins.lock().insert(key, result);
        Ok(result)
    }
    fn split_node(
        &mut self,
        mut node: NodeId,
        mut index: usize,
    ) -> Result<(Option<NodeId>, Option<NodeId>), CapacityError> {
        enum Side {
            Left(NodeId),
            Right(NodeId),
        }
        if index >= self.store.nodes[node.0 as usize].len {
            return Ok((Some(node), None));
        }
        let key = (node, index);
        if let Some(result) = self.store.splits.lock().get(&key).copied() {
            return Ok(result);
        }
        let mut path = Vec::new();
        let (mut left, mut right) = loop {
            if index == 0 {
                break (None, Some(node));
            }
            if index == self.store.nodes[node.0 as usize].len {
                break (Some(node), None);
            }
            let (a, b) = self.children(node);
            let len = self.store.nodes[a.0 as usize].len;
            if let Some(offset) = index.checked_sub(len) {
                index = offset;
                path.push(Side::Left(a));
                node = b;
            } else {
                path.push(Side::Right(b));
                node = a;
            }
        };
        let sides = path.into_iter().rev();
        for side in sides {
            match side {
                Side::Left(s) => {
                    left = Some(match left {
                        Some(left) => self.join_nodes(s, left)?,
                        None => s,
                    })
                }
                Side::Right(s) => {
                    right = Some(match right {
                        Some(right) => self.join_nodes(right, s)?,
                        None => s,
                    })
                }
            }
        }
        self.store.splits.lock().insert(key, (left, right));
        Ok((left, right))
    }
    fn pop_end(
        &mut self,
        root: NodeId,
        end: End,
    ) -> Result<(Option<NodeId>, NodeId), CapacityError> {
        let cut = match end {
            End::Front => 1,
            End::Back => (1..self.store.nodes[root.0 as usize].len).len(),
        };
        if let Some(split) = self.store.splits.lock().get(&(root, cut)).copied() {
            match (end, split) {
                (End::Front, (Some(leaf), rest)) | (End::Back, (rest, Some(leaf))) => {
                    return Ok((rest, leaf));
                }
                _ => {}
            }
        }
        let mut node = root;
        let mut siblings = Vec::new();
        while let Kind::Branch(left, right) = self.store.nodes[node.0 as usize].kind {
            match end {
                End::Front => {
                    siblings.push(right);
                    node = left;
                }
                End::Back => {
                    siblings.push(left);
                    node = right;
                }
            }
        }
        let mut siblings = siblings.into_iter().rev();
        let rest = match siblings.next() {
            None => None,
            Some(first) => Some(siblings.try_fold(first, |rest, sibling| match end {
                End::Front => self.join_nodes(rest, sibling),
                End::Back => self.join_nodes(sibling, rest),
            })?),
        };
        let split = match end {
            End::Front => (Some(node), rest),
            End::Back => (rest, Some(node)),
        };
        self.store.splits.lock().insert((root, cut), split);
        Ok((rest, node))
    }
    fn sequence(&mut self, root: Option<NodeId>) -> Result<Sequence<'g, T>, CapacityError> {
        match root {
            Some(node) => self.register(node).map(Sequence::from),
            None => Ok(Sequence::EMPTY),
        }
    }

    fn register(&mut self, node: NodeId) -> Result<RootId, CapacityError> {
        if let Some(id) = self.store.root_ids.lock().get(&node).copied() {
            return Ok(id);
        }
        let store = Arc::clone(&self.store);
        let content_key = |id: NodeId| {
            let node = &store.nodes[id.0 as usize];
            (node.len, node.fingerprint)
        };
        let key = content_key(node);
        let mut hasher = FxHasher::default();
        key.hash(&mut hasher);
        let hash = hasher.finish();
        let matches = |&(_, candidate): &(u64, RootId)| {
            content_key(store.roots[usize::from(candidate)].node) == key
        };
        let mut checked_head = None;
        loop {
            let head = store
                .candidates
                .lock()
                .find(hash, matches)
                .map(|(_, id)| *id);
            let mut candidate = head;
            while let Some(id) = candidate {
                if Some(id) == checked_head {
                    break;
                }
                let record = &store.roots[usize::from(id)];
                if self.compare(node, record.node) == Comparison::Equal {
                    store.root_ids.lock().insert(node, id);
                    return Ok(id);
                }
                candidate = record.previous;
            }
            checked_head = head;

            let mut candidates = store.candidates.lock();
            let current_head = candidates.find_mut(hash, matches);
            if current_head.as_deref().map(|(_, id)| *id) != head {
                continue;
            }

            let slot = u32::try_from(store.roots.count()).map_err(|_| CapacityError::Sequences)?;
            let id = RootId(
                NonZeroU32::MIN
                    .checked_add(slot)
                    .ok_or(CapacityError::Sequences)?,
            );
            store.roots.push(Root {
                node,
                previous: head,
                prefix: Mutex::new(None),
            });
            store.root_ids.lock().insert(node, id);
            match current_head {
                Some((_, current)) => *current = id,
                None => {
                    candidates.insert_unique(hash, (hash, id), |(hash, _)| *hash);
                }
            }
            return Ok(id);
        }
    }
    pub fn from_iter(
        &mut self,
        values: impl IntoIterator<Item = T>,
    ) -> Result<Sequence<'g, T>, CapacityError> {
        // Each pending tree is perfect. Equal heights merge like carries in a binary counter.
        let mut trees: Vec<NodeId> = Vec::new();
        for value in values {
            let mut tree = self.leaf(value)?;
            while let Some(left) = trees.pop_if(|left| {
                self.store.nodes[left.0 as usize].height == self.store.nodes[tree.0 as usize].height
            }) {
                tree = self.branch(left, tree)?;
            }
            trees.push(tree);
        }
        let mut trees = trees.into_iter().rev();
        let Some(mut root) = trees.next() else {
            return Ok(Sequence::EMPTY);
        };
        for left in trees {
            root = self.join_nodes(left, root)?;
        }
        self.register(root).map(Sequence::from)
    }
    pub fn push(
        &mut self,
        sequence: Sequence<'g, T>,
        value: T,
    ) -> Result<Sequence<'g, T>, CapacityError> {
        let leaf = self.leaf(value)?;
        let root = match self.node(sequence) {
            Some(root) => self.join_nodes(root, leaf)?,
            None => leaf,
        };
        let id = self.register(root)?;
        let mut prefix = self.store.roots[usize::from(id)].prefix.lock();
        match *prefix {
            Some(_) => {}
            None => *prefix = Some((sequence, leaf)),
        }
        Ok(id.into())
    }
    pub fn append(
        &mut self,
        left: Sequence<'g, T>,
        right: Sequence<'g, T>,
    ) -> Result<Sequence<'g, T>, CapacityError> {
        if let Some(id) = self.store.joins.lock().get(&(left, right)).copied() {
            return Ok(id);
        }
        let root = match (self.node(left), self.node(right)) {
            (Some(a), Some(b)) => self.join_nodes(a, b)?,
            (None, _) => return Ok(right),
            (_, None) => return Ok(left),
        };
        let id = self.register(root)?.into();
        self.store.joins.lock().insert((left, right), id);
        Ok(id)
    }
    pub fn slice(
        &mut self,
        sequence: Sequence<'g, T>,
        range: Range<usize>,
    ) -> Result<Option<Sequence<'g, T>>, CapacityError> {
        if range.start > range.end || range.end > self.len(sequence) {
            return Ok(None);
        }
        let root = match self.node(sequence) {
            None => None,
            Some(root) => {
                let (_, tail) = self.split_node(root, range.start)?;
                match tail {
                    Some(tail) => self.split_node(tail, range.len())?.0,
                    None => None,
                }
            }
        };
        self.sequence(root).map(Some)
    }
    pub fn replace(
        &mut self,
        sequence: Sequence<'g, T>,
        index: usize,
        value: T,
    ) -> Result<Option<Sequence<'g, T>>, CapacityError> {
        let Some(root) = self.node(sequence) else {
            return Ok(None);
        };
        let (left, Some(tail)) = self.split_node(root, index)? else {
            return Ok(None);
        };
        let (right, _) = self.pop_end(tail, End::Front)?;
        let value = self.leaf(value)?;
        let root = match left {
            Some(left) => self.join_nodes(left, value)?,
            None => value,
        };
        let root = match right {
            Some(right) => self.join_nodes(root, right)?,
            None => root,
        };
        Ok(Some(self.register(root)?.into()))
    }
    pub fn remove(
        &mut self,
        sequence: Sequence<'g, T>,
        index: usize,
    ) -> Result<Option<(Sequence<'g, T>, T)>, CapacityError> {
        let Some(root) = self.node(sequence) else {
            return Ok(None);
        };
        let (left, Some(tail)) = self.split_node(root, index)? else {
            return Ok(None);
        };
        let (right, first) = self.pop_end(tail, End::Front)?;
        let value = self.first_value(first).clone();
        let root = match (left, right) {
            (Some(left), Some(right)) => Some(self.join_nodes(left, right)?),
            (Some(root), None) | (None, Some(root)) => Some(root),
            (None, None) => None,
        };
        Ok(Some((self.sequence(root)?, value)))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Slice {
    node: NodeId,
    start: usize,
    end: usize,
}

enum SlicePart<'a, T> {
    Leaf(&'a T),
    Branch { prefix: Range<usize> },
}

impl Slice {
    fn whole<T>(arena: &Sequences<'_, T>, node: NodeId) -> Self {
        Self {
            node,
            start: 0,
            end: arena.store.nodes[node.0 as usize].len,
        }
    }

    // Canonicalize the cache key even when an entire slice belongs to one child.
    fn normalize<'a, T>(&mut self, arena: &'a Sequences<'_, T>) -> SlicePart<'a, T> {
        loop {
            match &arena.store.nodes[self.node.0 as usize].kind {
                Kind::Leaf(value) => return SlicePart::Leaf(value),
                Kind::Branch(left, right) => {
                    let boundary = arena.store.nodes[left.0 as usize].len;
                    if self.end <= boundary {
                        self.node = *left;
                    } else if let Some(start) = self.start.checked_sub(boundary) {
                        self.start = start;
                        self.end = (boundary..self.end).len();
                        self.node = *right;
                    } else {
                        return SlicePart::Branch {
                            prefix: self.start..boundary,
                        };
                    }
                }
            }
        }
    }

    fn split(self, mut prefix: Range<usize>, other_prefix_len: usize) -> (Self, Self) {
        let boundary = prefix.end;
        let middle = match prefix.nth(other_prefix_len) {
            Some(earlier) => earlier,
            None => boundary,
        };
        (
            Self {
                end: middle,
                ..self
            },
            Self {
                start: middle,
                ..self
            },
        )
    }
}

/// A complete ordered alignment, including empty inputs and length disagreement.
pub enum Alignment<U> {
    DifferentLengths,
    Empty,
    Aligned(U),
}
pub(crate) struct Pair(Slice, Slice);

impl<'g, T> Sequences<'g, T> {
    pub(crate) fn align(&self, left: Sequence<'g, T>, right: Sequence<'g, T>) -> Alignment<Pair> {
        match (self.node(left), self.node(right)) {
            (None, None) => Alignment::Empty,
            (Some(a), Some(b)) => {
                let a = Slice::whole(self, a);
                let b = Slice::whole(self, b);
                if a.end == b.end {
                    Alignment::Aligned(Pair(a, b))
                } else {
                    Alignment::DifferentLengths
                }
            }
            (None, Some(_)) | (Some(_), None) => Alignment::DifferentLengths,
        }
    }
}
pub enum PairedPart<'a, T, U> {
    Leaf(&'a T, &'a T),
    Branch(&'a U, &'a U),
}
pub struct Paired<'g, T, U, F> {
    cache: PairedCache<'g, T, U>,
    shared: Option<U>,
    operation: F,
}
impl<'g, T, U, F> Paired<'g, T, U, F> {
    pub fn new(shared: Option<U>, operation: F) -> Self {
        Self {
            cache: PairedCache::default(),
            shared,
            operation,
        }
    }
}
impl<'g, T, U: Clone, E, F: FnMut(PairedPart<'_, T, U>) -> Result<U, E>> Paired<'g, T, U, F> {
    pub fn fold(
        &mut self,
        arena: &Sequences<'g, T>,
        left: Sequence<'g, T>,
        right: Sequence<'g, T>,
    ) -> Result<Alignment<U>, E> {
        match arena.align(left, right) {
            Alignment::DifferentLengths => Ok(Alignment::DifferentLengths),
            Alignment::Empty => Ok(Alignment::Empty),
            Alignment::Aligned(pair) => self
                .cache
                .fold(arena, pair, self.shared.clone(), &mut self.operation)
                .map(Alignment::Aligned),
        }
    }
}
pub(crate) struct PairedCache<'g, T, U> {
    completed: Arc<Mutex<FxHashMap<(Slice, Slice), U>>>,
    marker: PhantomData<fn(&'g (), T) -> (&'g (), T)>,
}
impl<T, U> Default for PairedCache<'_, T, U> {
    fn default() -> Self {
        Self {
            completed: Arc::new(Mutex::new(FxHashMap::default())),
            marker: PhantomData,
        }
    }
}
impl<'g, T, U: Clone> PairedCache<'g, T, U> {
    // shapelint: allow(shallow-helper) Cache length is a read-only observation used by diagnostics.
    pub(crate) fn len(&self) -> usize {
        self.completed.lock().len()
    }

    // shapelint: allow(shallow-helper) Cache access is a short lock boundary outside callbacks.
    fn get(&self, pair: &(Slice, Slice)) -> Option<U> {
        self.completed.lock().get(pair).cloned()
    }

    // shapelint: allow(shallow-helper) First-writer publication keeps shared pure results canonical.
    fn publish(&self, pair: (Slice, Slice), value: U) -> U {
        self.completed.lock().entry(pair).or_insert(value).clone()
    }

    pub(crate) fn fold<E>(
        &mut self,
        arena: &Sequences<'g, T>,
        Pair(left, right): Pair,
        shared: Option<U>,
        mut operation: impl FnMut(PairedPart<'_, T, U>) -> Result<U, E>,
    ) -> Result<U, E> {
        enum Frame<U> {
            Right {
                parent: (Slice, Slice),
                right: (Slice, Slice),
            },
            Combine {
                parent: (Slice, Slice),
                left: U,
            },
        }
        let mut frames = Vec::new();
        let mut next = (left, right);
        loop {
            let (mut left, mut right) = next;
            let left_part = left.normalize(arena);
            let right_part = right.normalize(arena);
            let pair = (left, right);
            let mut value = if let Some(value) = self.get(&pair) {
                value
            } else if left == right
                && let Some(value) = &shared
            {
                self.publish(pair, value.clone())
            } else {
                match (left_part, right_part) {
                    (SlicePart::Leaf(a), SlicePart::Leaf(b)) => {
                        self.publish(pair, operation(PairedPart::Leaf(a, b))?)
                    }
                    (
                        SlicePart::Branch {
                            prefix: left_prefix,
                        },
                        SlicePart::Branch {
                            prefix: right_prefix,
                        },
                    ) => {
                        // Both slices split where the first of their left children ends.
                        let left_len = left_prefix.len();
                        let (left_first, left_rest) = left.split(left_prefix, right_prefix.len());
                        let (right_first, right_rest) = right.split(right_prefix, left_len);
                        frames.push(Frame::Right {
                            parent: pair,
                            right: (left_rest, right_rest),
                        });
                        next = (left_first, right_first);
                        continue;
                    }
                    (SlicePart::Leaf(_), SlicePart::Branch { .. })
                    | (SlicePart::Branch { .. }, SlicePart::Leaf(_)) => {
                        unreachable!("normalized equal-length slices have the same arity")
                    }
                }
            };
            loop {
                match frames.pop() {
                    None => return Ok(value),
                    Some(Frame::Right { parent, right }) => {
                        frames.push(Frame::Combine {
                            parent,
                            left: value,
                        });
                        next = right;
                        break;
                    }
                    Some(Frame::Combine { parent, left }) => {
                        value = self.publish(parent, operation(PairedPart::Branch(&left, &value))?);
                    }
                }
            }
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum Comparison {
    Equal,
    Different,
}
impl<T: Clone + Eq + Hash> Sequences<'_, T> {
    fn compare(&mut self, left: NodeId, right: NodeId) -> Comparison {
        let root = Pair(Slice::whole(self, left), Slice::whole(self, right));
        let mut cache = PairedCache {
            completed: Arc::clone(&self.store.comparisons),
            marker: PhantomData,
        };
        let result: Result<Comparison, std::convert::Infallible> =
            cache.fold(self, root, Some(Comparison::Equal), |part| {
                Ok(match part {
                    PairedPart::Leaf(a, b) => {
                        if a == b {
                            Comparison::Equal
                        } else {
                            Comparison::Different
                        }
                    }
                    PairedPart::Branch(Comparison::Equal, Comparison::Equal) => Comparison::Equal,
                    PairedPart::Branch(_, _) => Comparison::Different,
                })
            });
        match result {
            Ok(result) => result,
            Err(never) => match never {},
        }
    }
}

/// The two inputs to a compositional summary of an ordered sequence.
pub enum Part<'a, T, U> {
    Leaf(&'a T),
    Branch(&'a U, &'a U),
}
pub enum Selection {
    Keep,
    Drop,
    Visit,
}

enum Visit<K, P, V> {
    Node(K),
    Join(P, V, V),
    Done(V),
}

enum Frame<K, P, V> {
    Right { parent: P, right: K },
    Join { parent: P, left: V },
}

struct Postorder<K, P, V>(Vec<Frame<K, P, V>>);

impl<K, P, V> Postorder<K, P, V> {
    fn descend(&mut self, parent: P, left: K, right: K) -> Visit<K, P, V> {
        self.0.push(Frame::Right { parent, right });
        Visit::Node(left)
    }

    fn complete(&mut self, value: V) -> Visit<K, P, V> {
        match self.0.pop() {
            Some(Frame::Right { parent, right }) => {
                self.0.push(Frame::Join {
                    parent,
                    left: value,
                });
                Visit::Node(right)
            }
            Some(Frame::Join { parent, left }) => Visit::Join(parent, left, value),
            None => Visit::Done(value),
        }
    }
}

pub(crate) struct Fold<'g, T, U> {
    completed: Arc<Mutex<FxHashMap<NodeId, U>>>,
    marker: PhantomData<fn(&'g (), T) -> (&'g (), T)>,
}
impl<T, U> Default for Fold<'_, T, U> {
    fn default() -> Self {
        Self {
            completed: Arc::new(Mutex::new(FxHashMap::default())),
            marker: PhantomData,
        }
    }
}
impl<'g, T, U> Fold<'g, T, U> {
    pub(crate) fn share(&self) -> Self {
        Self {
            completed: Arc::clone(&self.completed),
            marker: PhantomData,
        }
    }

    // shapelint: allow(shallow-helper) Cache access is a short lock boundary outside callbacks.
    fn get(&self, id: NodeId) -> Option<U>
    where
        U: Clone,
    {
        self.completed.lock().get(&id).cloned()
    }

    // shapelint: allow(shallow-helper) First-writer publication keeps shared pure results canonical.
    fn publish(&self, id: NodeId, value: U) -> U
    where
        U: Clone,
    {
        self.completed.lock().entry(id).or_insert(value).clone()
    }
}
impl<'g, T: Clone, U: Clone> Fold<'g, T, U> {
    pub fn fold<C, E>(
        &mut self,
        context: &mut C,
        arena: impl for<'a> Fn(&'a C) -> &'a Sequences<'g, T>,
        sequence: Sequence<'g, T>,
        mut operation: impl FnMut(&mut C, Part<'_, T, U>) -> Result<U, E>,
    ) -> Result<Option<U>, E> {
        let Some(root) = arena(context).node(sequence) else {
            return Ok(None);
        };
        self.fold_node(context, arena, root, &mut operation)
            .map(Some)
    }

    fn fold_node<C, E>(
        &mut self,
        context: &mut C,
        arena: impl for<'a> Fn(&'a C) -> &'a Sequences<'g, T>,
        root: NodeId,
        operation: &mut impl FnMut(&mut C, Part<'_, T, U>) -> Result<U, E>,
    ) -> Result<U, E> {
        let mut path = Postorder(Vec::new());
        let mut visit = Visit::Node(root);
        loop {
            visit = match visit {
                Visit::Node(id) => match self.get(id) {
                    Some(value) => path.complete(value),
                    None => match arena(context).store.nodes[id.0 as usize].kind.clone() {
                        Kind::Leaf(value) => {
                            let result = operation(context, Part::Leaf(&value))?;
                            path.complete(self.publish(id, result))
                        }
                        Kind::Branch(left, right) => path.descend(id, left, right),
                    },
                },
                Visit::Join(id, left, right) => {
                    let result = operation(context, Part::Branch(&left, &right))?;
                    path.complete(self.publish(id, result))
                }
                Visit::Done(value) => return Ok(value),
            };
        }
    }
}

pub(crate) enum Parts<'g, T> {
    Empty,
    Leaf(T),
    Branch(Sequence<'g, T>, Sequence<'g, T>),
}
impl<'g, T: Clone + Eq + Hash> Sequences<'g, T> {
    pub(crate) fn parts(
        &mut self,
        sequence: Sequence<'g, T>,
    ) -> Result<Parts<'g, T>, CapacityError> {
        let Some(root) = self.node(sequence) else {
            return Ok(Parts::Empty);
        };
        match &self.store.nodes[root.0 as usize].kind {
            Kind::Leaf(value) => Ok(Parts::Leaf(value.clone())),
            Kind::Branch(left, right) => {
                let (left, right) = (*left, *right);
                let left = self.register(left)?.into();
                let right = self.register(right)?.into();
                Ok(Parts::Branch(left, right))
            }
        }
    }
    /// Removes the final occurrence while retaining the original sequence.
    pub fn prefix(
        &mut self,
        sequence: Sequence<'g, T>,
    ) -> Result<Option<(Sequence<'g, T>, T)>, CapacityError> {
        let Some(id) = sequence.root else {
            return Ok(None);
        };
        let root_index = usize::from(id);
        let cached = self.store.roots[root_index].prefix.lock().as_ref().copied();
        let (prefix, tail) = match cached {
            Some(cached) => cached,
            None => {
                let root = self.store.roots[root_index].node;
                let (prefix, tail) = self.pop_end(root, End::Back)?;
                let prefix = self.sequence(prefix)?;
                *self.store.roots[root_index]
                    .prefix
                    .lock()
                    .get_or_insert((prefix, tail))
            }
        };
        let value = self.first_value(tail).clone();
        Ok(Some((prefix, value)))
    }
}

/// Reuses each mapped fragment for one fixed operation.
pub struct Mapper<'g, 'h, T, U, F> {
    operation: F,
    completed: FxHashMap<NodeId, NodeId>,
    marker: PhantomData<fn(&'g (), T, &'h (), U) -> (&'g (), T, &'h (), U)>,
}
impl<'g, 'h, T, U, F: FnMut(&T) -> U> Mapper<'g, 'h, T, U, F> {
    pub fn new(operation: F) -> Self {
        Self {
            operation,
            completed: FxHashMap::default(),
            marker: PhantomData,
        }
    }
}
impl<'g, 'h, T, U: Clone + Eq + Hash, F: FnMut(&T) -> U> Mapper<'g, 'h, T, U, F> {
    pub fn map(
        &mut self,
        source: &Sequences<'g, T>,
        destination: &mut Sequences<'h, U>,
        sequence: Sequence<'g, T>,
    ) -> Result<Sequence<'h, U>, CapacityError> {
        let Some(root) = source.node(sequence) else {
            return Ok(Sequence::EMPTY);
        };
        let mut path = Postorder(Vec::new());
        let mut visit = Visit::Node(root);
        loop {
            visit = match visit {
                Visit::Node(id) => match self.completed.get(&id) {
                    Some(&mapped) => path.complete(mapped),
                    None => match &source.store.nodes[id.0 as usize].kind {
                        Kind::Leaf(value) => {
                            let mapped = destination.leaf((self.operation)(value))?;
                            self.completed.insert(id, mapped);
                            path.complete(mapped)
                        }
                        Kind::Branch(left, right) => path.descend(id, *left, *right),
                    },
                },
                Visit::Join(id, left, right) => {
                    let mapped = destination.branch(left, right)?;
                    self.completed.insert(id, mapped);
                    path.complete(mapped)
                }
                Visit::Done(mapped) => return destination.register(mapped).map(Sequence::from),
            };
        }
    }
}

pub(crate) struct Remap<'g, T, C> {
    completed: Memo<(NodeId, C), NodeId>,
    marker: PhantomData<fn(&'g (), T) -> (&'g (), T)>,
}
impl<T, C: Eq + Hash> Default for Remap<'_, T, C> {
    fn default() -> Self {
        Self {
            completed: Memo::default(),
            marker: PhantomData,
        }
    }
}
impl<'g, T, C> Remap<'g, T, C> {
    pub(crate) fn share(&self) -> Self {
        Self {
            completed: self.completed.clone(),
            marker: PhantomData,
        }
    }
}
impl<'g, T: Clone + Eq + Hash, C: Copy + Eq + Hash> Remap<'g, T, C> {
    pub fn apply<Context, E: From<CapacityError>>(
        &mut self,
        context: &mut Context,
        arena: impl for<'a> Fn(&'a mut Context) -> &'a mut Sequences<'g, T>,
        sequence: Sequence<'g, T>,
        context_id: C,
        mut operation: impl FnMut(&mut Context, &T) -> Result<T, E>,
    ) -> Result<Sequence<'g, T>, E> {
        let Some(root) = arena(context).node(sequence) else {
            return Ok(Sequence::EMPTY);
        };
        let mut path = Postorder(Vec::new());
        let mut visit = Visit::Node(root);
        loop {
            visit = match visit {
                Visit::Node(id) => match self.completed.get(&(id, context_id)) {
                    Some(mapped) => path.complete(mapped),
                    None => match arena(context).store.nodes[id.0 as usize].kind.clone() {
                        Kind::Leaf(value) => {
                            let value = operation(context, &value)?;
                            let mapped = arena(context).leaf(value)?;
                            self.completed.insert((id, context_id), mapped);
                            path.complete(mapped)
                        }
                        Kind::Branch(left, right) => path.descend(id, left, right),
                    },
                },
                Visit::Join(id, left, right) => {
                    let mapped = arena(context).branch(left, right)?;
                    self.completed.insert((id, context_id), mapped);
                    path.complete(mapped)
                }
                Visit::Done(mapped) => return Ok(arena(context).register(mapped)?.into()),
            };
        }
    }
}

/// Retains an exact left-to-right fold across shared fragments and input states.
pub struct Scan<'g, T, S, K, F> {
    completed: FxHashMap<(NodeId, S, K), S>,
    operation: F,
    marker: PhantomData<fn(&'g (), T) -> (&'g (), T)>,
}
impl<'g, T, S, K, F> Scan<'g, T, S, K, F> {
    pub fn new(operation: F) -> Self {
        Self {
            completed: FxHashMap::default(),
            operation,
            marker: PhantomData,
        }
    }
}
impl<'g, T: Clone, S: Clone + Eq + Hash, K: Clone + Eq + Hash, F> Scan<'g, T, S, K, F> {
    pub fn apply<C, E>(
        &mut self,
        context: &mut C,
        arena: impl for<'a> Fn(&'a C) -> &'a Sequences<'g, T>,
        sequence: Sequence<'g, T>,
        input: S,
        key: K,
    ) -> Result<S, E>
    where
        F: FnMut(&mut C, S, &T) -> Result<S, E>,
    {
        enum Work<S, K> {
            Visit((NodeId, S, K)),
            AfterLeft((NodeId, S, K)),
            AfterRight((NodeId, S, K), S),
        }
        enum Read<T> {
            Leaf(T),
            Branch(NodeId),
        }
        let Some(root) = arena(context).node(sequence) else {
            return Ok(input);
        };
        let key = (root, input, key);
        let mut pending = vec![Work::Visit(key.clone())];
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(key) => {
                    if self.completed.contains_key(&key) {
                        continue;
                    }
                    let node = match &arena(context).store.nodes[key.0.0 as usize].kind {
                        Kind::Leaf(value) => Read::Leaf(value.clone()),
                        Kind::Branch(left, _) => Read::Branch(*left),
                    };
                    match node {
                        Read::Leaf(value) => {
                            self.completed.insert(
                                key.clone(),
                                (self.operation)(context, key.1.clone(), &value)?,
                            );
                        }
                        Read::Branch(left) => {
                            let left = (left, key.1.clone(), key.2.clone());
                            pending.push(Work::AfterLeft(key));
                            pending.push(Work::Visit(left));
                        }
                    }
                }
                Work::AfterLeft(key) => {
                    let Kind::Branch(left, right) =
                        arena(context).store.nodes[key.0.0 as usize].kind
                    else {
                        unreachable!("only branches wait for children")
                    };
                    let input = self.completed[&(left, key.1.clone(), key.2.clone())].clone();
                    let child = (right, input.clone(), key.2.clone());
                    pending.push(Work::AfterRight(key, input));
                    pending.push(Work::Visit(child));
                }
                Work::AfterRight(key, input) => {
                    let Kind::Branch(_, right) = arena(context).store.nodes[key.0.0 as usize].kind
                    else {
                        unreachable!("only branches wait for children")
                    };
                    let output = self.completed[&(right, input, key.2.clone())].clone();
                    self.completed.insert(key, output);
                }
            }
        }
        Ok(self.completed[&key].clone())
    }
}

pub trait Rewrite<'g, T> {
    type Summary: Clone;
    type Context: Clone + Eq + Hash;
    type Error: From<CapacityError>;
    fn summarize(
        &mut self,
        arena: &mut Sequences<'g, T>,
        part: Part<'_, T, Self::Summary>,
    ) -> Result<Self::Summary, Self::Error>;
    fn normalize(
        &mut self,
        arena: &mut Sequences<'g, T>,
        summary: &Self::Summary,
        context: &Self::Context,
    ) -> Result<Self::Context, Self::Error>;
    fn select(
        &mut self,
        arena: &mut Sequences<'g, T>,
        summary: &Self::Summary,
        context: &Self::Context,
    ) -> Result<Selection, Self::Error>;
    fn value(
        &mut self,
        arena: &mut Sequences<'g, T>,
        value: &T,
        context: &Self::Context,
    ) -> Result<Option<T>, Self::Error>;
}
pub struct Transform<'g, T, O: Rewrite<'g, T>> {
    operation: O,
    summaries: Fold<'g, T, O::Summary>,
    cache: TransformCache<'g, T, O::Context>,
}
impl<'g, T, O: Rewrite<'g, T>> Transform<'g, T, O> {
    pub fn new(operation: O) -> Self {
        Self {
            operation,
            summaries: Fold::default(),
            cache: TransformCache::default(),
        }
    }
}
impl<'g, T: Clone + Eq + Hash, O: Rewrite<'g, T>> Transform<'g, T, O> {
    pub fn apply(
        &mut self,
        arena: &mut Sequences<'g, T>,
        sequence: Sequence<'g, T>,
        context: O::Context,
    ) -> Result<Sequence<'g, T>, O::Error> {
        self.cache.apply(
            arena,
            sequence,
            &mut self.summaries,
            context,
            &mut self.operation,
            |o, a, p| o.summarize(a, p),
            |o, a, s, c| o.normalize(a, s, c),
            |o, a, s, c| o.select(a, s, c),
            |o, a, v, c| o.value(a, v, c),
        )
    }
}
pub(crate) struct TransformCache<'g, T, C> {
    completed: Arc<Mutex<FxHashMap<(NodeId, C), Option<NodeId>>>>,
    marker: PhantomData<fn(&'g (), T) -> (&'g (), T)>,
}
impl<T, C> Default for TransformCache<'_, T, C> {
    fn default() -> Self {
        Self {
            completed: Arc::new(Mutex::new(FxHashMap::default())),
            marker: PhantomData,
        }
    }
}
impl<'g, T: Clone + Eq + Hash, C: Clone + Eq + Hash> TransformCache<'g, T, C> {
    pub(crate) fn share(&self) -> Self {
        Self {
            completed: Arc::clone(&self.completed),
            marker: PhantomData,
        }
    }

    // shapelint: allow(shallow-helper) Cache access is a short lock boundary outside rewrite callbacks.
    fn get(&self, key: &(NodeId, C)) -> Option<Option<NodeId>> {
        self.completed.lock().get(key).copied()
    }

    pub(crate) fn apply<U: Clone, S, E: From<CapacityError>>(
        &mut self,
        arena: &mut Sequences<'g, T>,
        sequence: Sequence<'g, T>,
        summaries: &mut Fold<'g, T, U>,
        context: C,
        state: &mut S,
        mut summarize: impl FnMut(&mut S, &mut Sequences<'g, T>, Part<'_, T, U>) -> Result<U, E>,
        mut normalize: impl FnMut(&mut S, &mut Sequences<'g, T>, &U, &C) -> Result<C, E>,
        mut select: impl FnMut(&mut S, &mut Sequences<'g, T>, &U, &C) -> Result<Selection, E>,
        mut value: impl FnMut(&mut S, &mut Sequences<'g, T>, &T, &C) -> Result<Option<T>, E>,
    ) -> Result<Sequence<'g, T>, E> {
        let Some(root) = arena.node(sequence) else {
            return Ok(Sequence::EMPTY);
        };
        let mut summary = |id, state: &mut S, arena: &mut Sequences<'g, T>| {
            summaries.fold_node(
                &mut (arena, state),
                |context| &*context.0,
                id,
                &mut |context, part| summarize(context.1, context.0, part),
            )
        };
        let root_summary = summary(root, state, arena)?;
        let key = (root, normalize(state, arena, &root_summary, &context)?);
        let mut path = Postorder(Vec::new());
        let mut visit = Visit::Node((key, root_summary));
        let mapped = loop {
            let (key, mapped) = match visit {
                Visit::Node((key, node_summary)) => {
                    if let Some(result) = self.get(&key) {
                        visit = path.complete(result);
                        continue;
                    }
                    let mapped = match select(state, arena, &node_summary, &key.1)? {
                        Selection::Keep => Some(key.0),
                        Selection::Drop => None,
                        Selection::Visit => {
                            match arena.store.nodes[key.0.0 as usize].kind.clone() {
                                Kind::Leaf(original) => {
                                    match value(state, arena, &original, &key.1)? {
                                        Some(value) => Some(arena.leaf(value)?),
                                        None => None,
                                    }
                                }
                                Kind::Branch(left, right) => {
                                    let left_summary = summary(left, state, arena)?;
                                    let right_summary = summary(right, state, arena)?;
                                    let left = (
                                        (left, normalize(state, arena, &left_summary, &key.1)?),
                                        left_summary,
                                    );
                                    let right = (
                                        (right, normalize(state, arena, &right_summary, &key.1)?),
                                        right_summary,
                                    );
                                    visit = path.descend(key, left, right);
                                    continue;
                                }
                            }
                        }
                    };
                    (key, mapped)
                }
                Visit::Join(key, left, right) => {
                    let mapped = match (left, right) {
                        (Some(left), Some(right)) => Some(arena.join_nodes(left, right)?),
                        (Some(root), None) | (None, Some(root)) => Some(root),
                        (None, None) => None,
                    };
                    (key, mapped)
                }
                Visit::Done(result) => break result,
            };
            let mapped = *self.completed.lock().entry(key).or_insert(mapped);
            visit = path.complete(mapped);
        };
        let result = arena.sequence(mapped)?;
        summaries.fold(
            &mut (&mut *arena, &mut *state),
            |context| &*context.0,
            result,
            |context, part| summarize(context.1, context.0, part),
        )?;
        Ok(result)
    }
}
impl<'g, T: Clone + Eq + Hash, U: Clone> Fold<'g, T, U> {
    pub(crate) fn edit<C: Clone + Eq + Hash, S, E: From<CapacityError>>(
        &mut self,
        arena: &mut Sequences<'g, T>,
        sequence: Sequence<'g, T>,
        cache: &mut TransformCache<'g, T, C>,
        key: C,
        state: &mut S,
        summarize: impl FnMut(&mut S, &mut Sequences<'g, T>, Part<'_, T, U>) -> Result<U, E>,
        select: impl FnMut(&mut S, &mut Sequences<'g, T>, &U, &C) -> Result<Selection, E>,
        operation: impl FnMut(&mut S, &mut Sequences<'g, T>, &T, &C) -> Result<Option<T>, E>,
    ) -> Result<Sequence<'g, T>, E> {
        cache.apply(
            arena,
            sequence,
            self,
            key,
            state,
            summarize,
            |_, _, _, context| Ok(context.clone()),
            select,
            operation,
        )
    }
}
