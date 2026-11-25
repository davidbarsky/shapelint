use rustc_data_structures::fx::{FxHashMap, FxHasher};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::num::{NonZeroU32, NonZeroU64};

use crate::arena::{ArenaId, CapacityError, Intern};
use crate::memo::Memo;

#[derive(Clone)]
pub(crate) enum Root<T> {
    Empty,
    Tree(T),
}
impl<T> From<Option<T>> for Root<T> {
    fn from(root: Option<T>) -> Self {
        match root {
            None => Self::Empty,
            Some(root) => Self::Tree(root),
        }
    }
}
impl<T> From<Root<T>> for Option<T> {
    fn from(root: Root<T>) -> Self {
        match root {
            Root::Empty => None,
            Root::Tree(root) => Some(root),
        }
    }
}
impl<'a, T> From<&'a Root<T>> for Option<&'a T> {
    fn from(root: &'a Root<T>) -> Self {
        match root {
            Root::Empty => None,
            Root::Tree(root) => Some(root),
        }
    }
}
impl<'a, T> From<&'a mut Root<T>> for Option<&'a mut T> {
    fn from(root: &'a mut Root<T>) -> Self {
        match root {
            Root::Empty => None,
            Root::Tree(root) => Some(root),
        }
    }
}

pub trait Routing<K> {
    fn address(key: &K) -> u128;
}
pub struct Hashed;
impl<K: Hash> Routing<K> for Hashed {
    fn address(key: &K) -> u128 {
        let mut h = FxHasher::default();
        key.hash(&mut h);
        u128::from(h.finish())
    }
}
pub struct Ordered;
impl Routing<u128> for Ordered {
    fn address(key: &u128) -> u128 {
        *key
    }
}
#[derive(Clone, Copy)]
pub enum Neighbor {
    Before,
    After,
}

rustc_index::newtype_index! {
    #[max = 0xffff_fffe]
    #[orderable]
    struct NodeId {}
}
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct KeyId(u32);
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct ValueId(u32);

impl ArenaId for NodeId {
    const MAX_INDEX: u32 = Self::MAX_AS_U32;

    fn from_index(index: u32) -> Self {
        Self::from_u32(index)
    }

    fn index(self) -> u32 {
        self.as_u32()
    }
}
impl ArenaId for KeyId {
    fn from_index(index: u32) -> Self {
        Self(index)
    }

    fn index(self) -> u32 {
        self.0
    }
}
impl ArenaId for ValueId {
    fn from_index(index: u32) -> Self {
        Self(index)
    }

    fn index(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
enum Node {
    Leaf {
        hash: u128,
        key: KeyId,
        value: ValueId,
    },
    Branch {
        bit: BranchBit,
        left: NodeId,
        right: NodeId,
    },
}

// Hash bits route first. Interned key bits distinguish keys with the same hash.
#[derive(Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
enum BranchBit {
    Key(NonZeroU32),
    LowHash(NonZeroU64),
    HighHash(NonZeroU64),
}

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
struct Address {
    hash: u128,
    key: KeyId,
}

#[derive(Clone, Copy)]
enum Membership {
    Either,
    Both,
}

enum Overlap {
    Split(BranchBit),
    Leaves {
        address: Address,
        left: ValueId,
        right: ValueId,
    },
}

#[derive(Clone, Copy)]
enum Side {
    Left,
    Right,
}

impl Address {
    fn side(self, bit: BranchBit) -> Side {
        let masked = match bit {
            BranchBit::Key(mask) => u64::from(self.key.0 & mask.get()),
            BranchBit::LowHash(mask) => self.hash as u64 & mask.get(),
            BranchBit::HighHash(mask) => (self.hash >> u64::BITS) as u64 & mask.get(),
        };
        match masked {
            0 => Side::Left,
            _ => Side::Right,
        }
    }

    fn split(self, other: Self) -> Option<BranchBit> {
        let differing = self.hash ^ other.hash;
        if let Some(high) = NonZeroU64::new((differing >> u64::BITS) as u64) {
            return Some(BranchBit::HighHash(high.isolate_highest_one()));
        }
        if let Some(low) = NonZeroU64::new(differing as u64) {
            return Some(BranchBit::LowHash(low.isolate_highest_one()));
        }
        NonZeroU32::new(self.key.0 ^ other.key.0)
            .map(|key| BranchBit::Key(key.isolate_highest_one()))
    }
}

#[derive(Clone, Hash, PartialEq, Eq)]
struct NodeInfo {
    node: Node,
    len: usize,
    extrema: (Address, Address),
}

/// Identifies a canonical map in its branded owner.
pub struct Map<'g, K, V, R = Hashed> {
    root: Option<NodeId>,
    brand: PhantomData<fn(&'g mut (K, V, R)) -> &'g mut (K, V, R)>,
}
impl<K, V, R> Map<'_, K, V, R> {
    pub const EMPTY: Self = Self {
        root: None,
        brand: PhantomData,
    };

    // shapelint: allow(shallow-helper) The root identity stays behind the branded map boundary.
    pub(crate) fn identity(self) -> u32 {
        self.root.map_or(0, |root| root.as_u32() + 1)
    }
}
impl<K, V, R> Copy for Map<'_, K, V, R> {}
impl<K, V, R> Clone for Map<'_, K, V, R> {
    fn clone(&self) -> Self {
        *self
    }
}
impl<K, V, R> PartialEq for Map<'_, K, V, R> {
    fn eq(&self, other: &Self) -> bool {
        self.root == other.root
    }
}
impl<K, V, R> Eq for Map<'_, K, V, R> {}
impl<K, V, R> Hash for Map<'_, K, V, R> {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.identity().hash(h);
    }
}
impl<K, V, R> std::fmt::Debug for Map<'_, K, V, R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Map(NodeId({}))", self.identity())
    }
}
pub type Set<'g, K, R = Hashed> = Map<'g, K, (), R>;
pub type Sets<'g, K, R = Hashed> = Maps<'g, K, (), R>;

/// Owns canonical nodes and payloads for one branded map domain.
pub struct Maps<'g, K, V, R = Hashed> {
    nodes: Intern<NodeId, NodeInfo>,
    overlays: Memo<(NodeId, NodeId), Option<NodeId>>,
    intersections: Memo<(NodeId, NodeId), Option<NodeId>>,
    keys: Intern<KeyId, K>,
    values: Intern<ValueId, V>,
    brand: PhantomData<fn(&'g mut (K, V, R)) -> &'g mut (K, V, R)>,
}
/// Creates an owner whose handles cannot escape or mix with another owner.
pub fn with_maps<K, V, R, T>(f: impl for<'g> FnOnce(&mut Maps<'g, K, V, R>) -> T) -> T {
    let mut maps = Maps::new();
    f(&mut maps)
}
impl<'g, K, V, R> Maps<'g, K, V, R> {
    pub(crate) fn new() -> Self {
        Self {
            nodes: Intern::new(),
            overlays: Memo::default(),
            intersections: Memo::default(),
            keys: Intern::new(),
            values: Intern::new(),
            brand: PhantomData,
        }
    }
    /// Shares canonical nodes, payloads, and pure operation results with this owner.
    pub fn share(&self) -> Self {
        Self {
            nodes: self.nodes.clone(),
            overlays: self.overlays.clone(),
            intersections: self.intersections.clone(),
            keys: self.keys.clone(),
            values: self.values.clone(),
            brand: PhantomData,
        }
    }
    fn intern_node(&self, node: Node) -> Result<NodeId, CapacityError> {
        let hash = hash(&node);
        let len = match &node {
            Node::Leaf { .. } => 1,
            Node::Branch { left, right, .. } => self
                .nodes
                .get(*left)
                .len
                .checked_add(self.nodes.get(*right).len)
                .ok_or(CapacityError::Sets)?,
        };
        let extrema = match &node {
            Node::Leaf { hash, key, .. } => {
                let address = Address {
                    hash: *hash,
                    key: *key,
                };
                (address, address)
            }
            Node::Branch { left, right, .. } => (
                self.nodes.get(*left).extrema.0,
                self.nodes.get(*right).extrema.1,
            ),
        };
        self.nodes.intern_by(
            NodeInfo { node, len, extrema },
            hash,
            CapacityError::Sets,
            |existing, candidate| (existing.node == candidate.node).then_some(()),
        )
    }
    pub fn len(&self, map: Map<'g, K, V, R>) -> usize {
        match map.root {
            Some(root) => self.nodes.get(root).len,
            None => 0,
        }
    }
    /// Returns the number of canonical nodes retained by this persistent map
    /// owner, including historical versions still reachable through handles.
    // shapelint: allow(shallow-helper) This read-only witness keeps the persistent arena private.
    pub fn retained_nodes(&self) -> usize {
        self.nodes.len()
    }
    pub fn iter(&self, map: Map<'g, K, V, R>) -> Iter<'_, 'g, K, V, R> {
        Iter {
            maps: self,
            pending: match map.root {
                Some(root) => vec![root],
                None => Vec::new(),
            },
        }
    }
    fn part(&self, id: NodeId) -> Part<'_, K, V, NodeId> {
        match self.nodes.get(id).node {
            Node::Leaf { key, value, .. } => Part::Leaf(self.keys.get(key), self.values.get(value)),
            Node::Branch { left, right, .. } => Part::Branch(left, right),
        }
    }

    fn next_difference(
        &self,
        pending: &mut Vec<(Option<NodeId>, Option<NodeId>)>,
    ) -> Option<(&K, Difference<&V>)> {
        while let Some(pair) = pending.pop() {
            match pair {
                (None, None) => {}
                (Some(a), Some(b)) if a == b => {}
                (Some(id), None) => match self.part(id) {
                    Part::Leaf(key, value) => return Some((key, Difference::Left(value))),
                    Part::Branch(left, right) => {
                        pending.push((Some(right), None));
                        pending.push((Some(left), None));
                    }
                },
                (None, Some(id)) => match self.part(id) {
                    Part::Leaf(key, value) => return Some((key, Difference::Right(value))),
                    Part::Branch(left, right) => {
                        pending.push((None, Some(right)));
                        pending.push((None, Some(left)));
                    }
                },
                (Some(a), Some(b)) => match self.overlap(a, b) {
                    Overlap::Split(bit) => {
                        let (al, ar) = self.partition(a, bit);
                        let (bl, br) = self.partition(b, bit);
                        pending.push((ar, br));
                        pending.push((al, bl));
                    }
                    Overlap::Leaves {
                        address,
                        left,
                        right,
                    } => {
                        let difference =
                            Difference::Both(self.values.get(left), self.values.get(right));
                        return Some((self.keys.get(address.key), difference));
                    }
                },
            }
        }
        None
    }

    fn partition(&self, id: NodeId, bit: BranchBit) -> (Option<NodeId>, Option<NodeId>) {
        match &self.nodes.get(id).node {
            Node::Branch {
                bit: own,
                left,
                right,
            } if *own == bit => (Some(*left), Some(*right)),
            _ => match self.nodes.get(id).extrema.0.side(bit) {
                Side::Left => (Some(id), None),
                Side::Right => (None, Some(id)),
            },
        }
    }
    fn overlap(&self, left: NodeId, right: NodeId) -> Overlap {
        let left = self.nodes.get(left);
        let right = self.nodes.get(right);
        let address = left.extrema.0;
        let differing = address.split(right.extrema.0);
        let branch_bit = match (&left.node, &right.node) {
            (Node::Leaf { value: a, .. }, Node::Leaf { value: b, .. }) => {
                return match differing {
                    Some(bit) => Overlap::Split(bit),
                    None => Overlap::Leaves {
                        address,
                        left: *a,
                        right: *b,
                    },
                };
            }
            (Node::Branch { bit, .. }, Node::Leaf { .. })
            | (Node::Leaf { .. }, Node::Branch { bit, .. }) => *bit,
            (Node::Branch { bit: a, .. }, Node::Branch { bit: b, .. }) => *a.max(b),
        };
        Overlap::Split(differing.map_or(branch_bit, |bit| bit.max(branch_bit)))
    }
}
fn hash<T: Hash>(value: &T) -> u64 {
    let mut h = FxHasher::default();
    value.hash(&mut h);
    h.finish()
}
impl<'g, K: Eq + Hash, V: Eq + Hash, R: Routing<K>> Maps<'g, K, V, R> {
    pub fn get(&self, map: Map<'g, K, V, R>, key: &K) -> Option<&V> {
        let hash = R::address(key);
        let mut address = Address {
            hash,
            key: KeyId(0),
        };
        let mut collision_key = None;
        let mut id = map.root;
        while let Some(current) = id {
            match &self.nodes.get(current).node {
                Node::Leaf {
                    hash: own,
                    key: own_key,
                    value,
                } => {
                    return if *own == hash {
                        (self.keys.get(*own_key) == key).then(|| self.values.get(*value))
                    } else {
                        None
                    };
                }
                Node::Branch { bit, left, right } => {
                    if let BranchBit::Key(_) = bit {
                        address.key = match collision_key {
                            Some(key) => key,
                            None => {
                                let id = self
                                    .keys
                                    .find_by(crate::persistent::hash(key), |candidate| {
                                        (candidate == key).then_some(())
                                    })?;
                                collision_key = Some(id);
                                id
                            }
                        };
                    }
                    id = match address.side(*bit) {
                        Side::Left => Some(*left),
                        Side::Right => Some(*right),
                    }
                }
            }
        }
        None
    }
    pub fn insert(
        &mut self,
        map: &mut Map<'g, K, V, R>,
        key: K,
        value: V,
    ) -> Result<Option<V>, CapacityError>
    where
        V: Clone,
    {
        let hash = R::address(&key);
        let key = self.keys.intern(key, CapacityError::Sets)?;
        let value = self.values.intern(value, CapacityError::Sets)?;
        let address = Address { hash, key };
        let Some(mut id) = map.root else {
            map.root = Some(self.intern_node(Node::Leaf { hash, key, value })?);
            return Ok(None);
        };
        let mut path = Vec::new();
        let (stored, old_value) = loop {
            match self.nodes.get(id).node {
                Node::Leaf { hash, key, value } => break (Address { hash, key }, value),
                Node::Branch { bit, left, right } => match address.side(bit) {
                    Side::Left => {
                        path.push((id, bit, Side::Left, right));
                        id = left;
                    }
                    Side::Right => {
                        path.push((id, bit, Side::Right, left));
                        id = right;
                    }
                },
            }
        };
        let (mut result, previous) = match address.split(stored) {
            None => {
                let previous = Some(self.values.get(old_value).clone());
                if old_value == value {
                    return Ok(previous);
                }
                (self.intern_node(Node::Leaf { hash, key, value })?, previous)
            }
            Some(bit) => {
                let mut insertion = id;
                while let Some((subtree, ..)) =
                    path.pop_if(|(_, child_bit, _, _)| *child_bit <= bit)
                {
                    insertion = subtree;
                }
                let leaf = self.intern_node(Node::Leaf { hash, key, value })?;
                let (left, right) = match address.side(bit) {
                    Side::Left => (leaf, insertion),
                    Side::Right => (insertion, leaf),
                };
                (self.intern_node(Node::Branch { bit, left, right })?, None)
            }
        };
        while let Some((_, bit, side, sibling)) = path.pop() {
            let (left, right) = match side {
                Side::Left => (result, sibling),
                Side::Right => (sibling, result),
            };
            result = self.intern_node(Node::Branch { bit, left, right })?;
        }
        map.root = Some(result);
        Ok(previous)
    }
    pub fn remove(
        &mut self,
        map: &mut Map<'g, K, V, R>,
        key: &K,
    ) -> Result<Option<V>, CapacityError>
    where
        V: Clone,
    {
        let Some(key_id) = self
            .keys
            .find_by(hash(key), |candidate| (candidate == key).then_some(()))
        else {
            return Ok(None);
        };
        let hash = R::address(key);
        let address = Address { hash, key: key_id };
        let Some(mut id) = map.root else {
            return Ok(None);
        };
        let mut path = Vec::new();
        let previous = loop {
            match self.nodes.get(id).node {
                Node::Leaf {
                    hash: own,
                    key: own_key,
                    value,
                } => {
                    if own != hash || self.keys.get(own_key) != key {
                        return Ok(None);
                    }
                    break self.values.get(value).clone();
                }
                Node::Branch { bit, left, right } => match address.side(bit) {
                    Side::Left => {
                        path.push((bit, Side::Left, right));
                        id = left;
                    }
                    Side::Right => {
                        path.push((bit, Side::Right, left));
                        id = right;
                    }
                },
            }
        };
        // Removing the leaf promotes its sibling. Every remaining ancestor keeps both children.
        let result = if let Some((_, _, mut subtree)) = path.pop() {
            while let Some((bit, side, sibling)) = path.pop() {
                let (left, right) = match side {
                    Side::Left => (subtree, sibling),
                    Side::Right => (sibling, subtree),
                };
                subtree = self.intern_node(Node::Branch { bit, left, right })?;
            }
            Some(subtree)
        } else {
            None
        };
        map.root = result;
        Ok(Some(previous))
    }
    /// Reuses completed subtree pairs while taking values from `other`.
    pub fn overlay(
        &mut self,
        map: &mut Map<'g, K, V, R>,
        other: Map<'g, K, V, R>,
    ) -> Result<(), CapacityError> {
        map.root = self.combine(
            (map.root, other.root),
            &self.overlays,
            Membership::Either,
            Identical::Reuse,
            |_, right| Ok::<_, CapacityError>(Some(right)),
        )?;
        Ok(())
    }

    /// Keeps only entries whose keys and values occur in both maps.
    pub fn intersection(
        &mut self,
        map: &mut Map<'g, K, V, R>,
        other: Map<'g, K, V, R>,
    ) -> Result<(), CapacityError> {
        map.root = self.combine(
            (map.root, other.root),
            &self.intersections,
            Membership::Both,
            Identical::Reuse,
            |_, _| Ok::<_, CapacityError>(None),
        )?;
        Ok(())
    }

    fn combine_values<E: From<CapacityError>>(
        &self,
        left: ValueId,
        right: ValueId,
        combine: impl FnOnce(&V, &V) -> Result<V, E>,
    ) -> Result<ValueId, E> {
        let value = combine(self.values.get(left), self.values.get(right))?;
        Ok(self.values.intern(value, CapacityError::Sets)?)
    }

    fn combine<E: From<CapacityError>>(
        &self,
        mut next: (Option<NodeId>, Option<NodeId>),
        cache: &Memo<(NodeId, NodeId), Option<NodeId>>,
        membership: Membership,
        identical: Identical,
        mut values: impl FnMut(ValueId, ValueId) -> Result<Option<ValueId>, E>,
    ) -> Result<Option<NodeId>, E> {
        enum Frame {
            Right {
                parents: (NodeId, NodeId),
                bit: BranchBit,
                right: (Option<NodeId>, Option<NodeId>),
            },
            Join {
                parents: (NodeId, NodeId),
                bit: BranchBit,
                left: Option<NodeId>,
            },
        }
        let mut frames = Vec::new();
        loop {
            let mut result = match next {
                (None, other) | (other, None) => match membership {
                    Membership::Either => other,
                    Membership::Both => None,
                },
                (Some(a), Some(b)) => {
                    if let Identical::Reuse = identical
                        && a == b
                    {
                        Some(a)
                    } else if let Some(cached) = cache.get(&(a, b)) {
                        cached
                    } else {
                        match self.overlap(a, b) {
                            Overlap::Split(bit) => {
                                let (al, ar) = self.partition(a, bit);
                                let (bl, br) = self.partition(b, bit);
                                frames.push(Frame::Right {
                                    parents: (a, b),
                                    bit,
                                    right: (ar, br),
                                });
                                next = (al, bl);
                                continue;
                            }
                            Overlap::Leaves {
                                address,
                                left,
                                right,
                            } => {
                                let result = match values(left, right)? {
                                    None => None,
                                    Some(value) if value == right => Some(b),
                                    Some(value) if value == left => Some(a),
                                    Some(value) => Some(self.intern_node(Node::Leaf {
                                        hash: address.hash,
                                        key: address.key,
                                        value,
                                    })?),
                                };
                                cache.insert((a, b), result);
                                result
                            }
                        }
                    }
                }
            };
            loop {
                match frames.pop() {
                    None => return Ok(result),
                    Some(Frame::Right {
                        parents,
                        bit,
                        right,
                    }) => {
                        frames.push(Frame::Join {
                            parents,
                            bit,
                            left: result,
                        });
                        next = right;
                        break;
                    }
                    Some(Frame::Join { parents, bit, left }) => {
                        result = match (left, result) {
                            (None, other) | (other, None) => other,
                            (Some(left), Some(right)) => {
                                Some(self.intern_node(Node::Branch { bit, left, right })?)
                            }
                        };
                        cache.insert(parents, result);
                    }
                }
            }
        }
    }
}
impl<'g, V> Maps<'g, u128, V, Ordered> {
    pub fn neighbor(
        &self,
        map: Map<'g, u128, V, Ordered>,
        key: u128,
        direction: Neighbor,
    ) -> Option<(&u128, &V)> {
        let mut pending: Vec<_> = map.root.into_iter().collect();
        while let Some(id) = pending.pop() {
            match direction {
                Neighbor::Before if self.nodes.get(id).extrema.0.hash >= key => continue,
                Neighbor::After if self.nodes.get(id).extrema.1.hash <= key => continue,
                Neighbor::Before | Neighbor::After => {}
            }
            match &self.nodes.get(id).node {
                Node::Leaf { key, value, .. } => {
                    return Some((self.keys.get(*key), self.values.get(*value)));
                }
                Node::Branch { left, right, .. } => match direction {
                    Neighbor::Before => {
                        pending.push(*left);
                        pending.push(*right);
                    }
                    Neighbor::After => {
                        pending.push(*right);
                        pending.push(*left);
                    }
                },
            }
        }
        None
    }
}
pub struct Iter<'a, 'g, K, V, R = Hashed> {
    maps: &'a Maps<'g, K, V, R>,
    pending: Vec<NodeId>,
}
impl<'a, 'g, K, V, R> Iterator for Iter<'a, 'g, K, V, R> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<Self::Item> {
        loop {
            match self.maps.part(self.pending.pop()?) {
                Part::Leaf(key, value) => return Some((key, value)),
                Part::Branch(left, right) => {
                    self.pending.push(right);
                    self.pending.push(left);
                }
            }
        }
    }
}
pub enum Difference<V> {
    Left(V),
    Right(V),
    Both(V, V),
}
pub struct Differences<'a, 'g, K, V, R = Hashed> {
    maps: &'a Maps<'g, K, V, R>,
    pending: Vec<(Option<NodeId>, Option<NodeId>)>,
}
impl<'a, 'g, K, V, R> From<(&'a Maps<'g, K, V, R>, Map<'g, K, V, R>, Map<'g, K, V, R>)>
    for Differences<'a, 'g, K, V, R>
{
    fn from(
        (maps, left, right): (&'a Maps<'g, K, V, R>, Map<'g, K, V, R>, Map<'g, K, V, R>),
    ) -> Self {
        Self {
            maps,
            pending: vec![(left.root, right.root)],
        }
    }
}
impl<'a, 'g, K, V, R> Iterator for Differences<'a, 'g, K, V, R> {
    type Item = (&'a K, Difference<&'a V>);
    fn next(&mut self) -> Option<Self::Item> {
        self.maps.next_difference(&mut self.pending)
    }
}
#[derive(Clone, Copy)]
pub enum Identical {
    Reuse,
    Combine,
}
/// Retains results for one fixed combination operation.
///
/// The callback must return the same value for the same inputs throughout the
/// cache lifetime, including when its mutable context changes.
pub struct Composition<'g, K, V, F, R = Hashed> {
    identical: Identical,
    combine: F,
    completed: Memo<(NodeId, NodeId), Option<NodeId>>,
    marker: PhantomData<fn(&'g mut (K, V, R)) -> &'g mut (K, V, R)>,
}
impl<'g, K, V, F, R> Composition<'g, K, V, F, R> {
    pub fn new(identical: Identical, combine: F) -> Self {
        Self {
            identical,
            combine,
            completed: Memo::default(),
            marker: PhantomData,
        }
    }
    pub(crate) fn share(&self) -> Self
    where
        F: Clone,
    {
        Self {
            identical: self.identical,
            combine: self.combine.clone(),
            completed: self.completed.clone(),
            marker: PhantomData,
        }
    }
}
impl<'g, K: Eq + Hash, V: Eq + Hash, F, R: Routing<K>> Composition<'g, K, V, F, R> {
    pub fn compose<C, E>(
        &mut self,
        maps: &mut Maps<'g, K, V, R>,
        context: &mut C,
        left: Map<'g, K, V, R>,
        right: Map<'g, K, V, R>,
    ) -> Result<Map<'g, K, V, R>, E>
    where
        F: FnMut(&mut C, &V, &V) -> Result<V, E>,
        E: From<CapacityError>,
    {
        let root = maps.combine(
            (left.root, right.root),
            &self.completed,
            Membership::Either,
            self.identical,
            |a, b| {
                maps.combine_values(a, b, |a, b| (self.combine)(context, a, b))
                    .map(Some)
            },
        )?;
        Ok(Map {
            root,
            brand: PhantomData,
        })
    }
}
pub(crate) enum Part<'a, K, V, U> {
    Leaf(&'a K, &'a V),
    Branch(U, U),
}
pub(crate) struct Fold<'g, K, V, U> {
    completed: FxHashMap<NodeId, U>,
    marker: PhantomData<fn(&'g mut (K, V)) -> &'g mut (K, V)>,
}
impl<'g, K, V, U> Default for Fold<'g, K, V, U> {
    fn default() -> Self {
        Self {
            completed: FxHashMap::default(),
            marker: PhantomData,
        }
    }
}
impl<'g, K, V, U> Fold<'g, K, V, U> {
    pub(crate) fn fold<'a, R, E>(
        &'a mut self,
        maps: &Maps<'g, K, V, R>,
        map: Map<'g, K, V, R>,
        mut operation: impl FnMut(Part<'_, K, V, &U>) -> Result<U, E>,
    ) -> Result<Option<&'a U>, E>
    where
        E: From<CapacityError>,
    {
        enum Work {
            Visit(NodeId),
            Build {
                node: NodeId,
                left: NodeId,
                right: NodeId,
            },
        }
        let Some(root) = map.root else {
            return Ok(None);
        };
        let mut pending = vec![Work::Visit(root)];
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(id) => {
                    if self.completed.contains_key(&id) {
                        continue;
                    }
                    match maps.part(id) {
                        Part::Leaf(key, value) => {
                            let value = operation(Part::Leaf(key, value))?;
                            self.completed.insert(id, value);
                        }
                        Part::Branch(left, right) => {
                            pending.push(Work::Build {
                                node: id,
                                left,
                                right,
                            });
                            pending.push(Work::Visit(right));
                            pending.push(Work::Visit(left));
                        }
                    }
                }
                Work::Build { node, left, right } => {
                    let value = operation(Part::Branch(
                        &self.completed[&left],
                        &self.completed[&right],
                    ))?;
                    self.completed.insert(node, value);
                }
            }
        }
        Ok(self.completed.get(&root))
    }
}
