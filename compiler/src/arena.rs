//! Stable append-only storage and canonical interning for graph identities.

use parking_lot::Mutex;
use std::hash::{BuildHasher, Hash};
use std::ops::Index;
use std::sync::Arc;

use hashbrown::HashTable;
use rustc_data_structures::fx::FxBuildHasher;

#[derive(Clone, Copy, Debug, PartialEq, Eq, thiserror::Error)]
pub enum CapacityError {
    #[error("the persistent map exceeds its identity capacity")]
    Maps,
    #[error("the semantic values exceed their identity capacity")]
    Values,
    #[error("the analysis states exceed their identity capacity")]
    States,
    #[error("the ordered sequence graph exceeds its identity or length capacity")]
    Sequences,
    #[error("the shared alternative graph exceeds its u32 identity capacity")]
    Choices,
    #[error("the shared fact sets exceed their u32 identity capacity")]
    Sets,
    #[error("the symbolic expression graph exceeds its u32 identity capacity")]
    Expressions,
    #[error("the protocol history graph exceeds its u32 identity capacity")]
    Flows,
    #[error("the symbolic condition graph exceeds its u32 identity capacity")]
    Conditions,
    #[error("the symbolic query worklist exceeds its u32 identity capacity")]
    Queries,
    #[error("the symbolic rewrite contexts exceed their u32 identity capacity")]
    RewriteContexts,
}

/// Converts a checked `u32` index to and from a domain identity.
pub(crate) trait ArenaId: Copy + Eq + Hash {
    const MAX_INDEX: u32 = u32::MAX;

    fn from_index(index: u32) -> Self;
    fn index(self) -> u32;
}

struct Interned<I, T> {
    values: boxcar::Vec<T>,
    index: Mutex<HashTable<(u64, I)>>,
}

/// Shares one canonical identity for each equal value across cloned handles.
pub(crate) struct Intern<I, T> {
    interned: Arc<Interned<I, T>>,
}

impl<I, T> Clone for Intern<I, T> {
    fn clone(&self) -> Self {
        Self {
            interned: Arc::clone(&self.interned),
        }
    }
}

impl<I: ArenaId, T> Intern<I, T> {
    /// Creates an empty shared canonical table.
    pub(crate) fn new() -> Self {
        Self {
            interned: Arc::new(Interned {
                values: boxcar::Vec::new(),
                index: Mutex::new(HashTable::new()),
            }),
        }
    }

    // shapelint: allow(shallow-helper) This boundary checks that the typed identity belongs to this arena.
    #[shapelint_tool::arena(read)]
    pub(crate) fn get(&self, id: I) -> &T {
        &self.interned.values[id.index() as usize]
    }

    // shapelint: allow(shallow-helper) The backing append-only vector is private to the arena.
    pub(crate) fn len(&self) -> usize {
        self.interned.values.count()
    }
}

impl<I: ArenaId, T: Eq + Hash> Intern<I, T> {
    /// Returns the canonical identity for an equal value or appends it.
    #[shapelint_tool::arena(append)]
    pub(crate) fn intern<E: Copy>(&self, value: T, capacity_error: E) -> Result<I, E> {
        let hash = FxBuildHasher.hash_one(&value);
        self.intern_by(value, hash, capacity_error, |existing, value| {
            (existing == value).then_some(())
        })
    }

    /// Returns the canonical identity for a value using a caller-provided hash and equality.
    pub(crate) fn intern_by<E: Copy>(
        &self,
        value: T,
        hash: u64,
        capacity_error: E,
        equal: impl Fn(&T, &T) -> Option<()>,
    ) -> Result<I, E> {
        let mut index = self.interned.index.lock();
        if let Some((_, id)) = index.find(hash, |(_, id)| match equal(self.get(*id), &value) {
            Some(()) => true,
            None => false,
        }) {
            return Ok(*id);
        }
        self.publish(&mut index, hash, value, capacity_error)
    }

    /// Finds a value using a precomputed hash and full equality predicate.
    pub(crate) fn find_by(&self, hash: u64, equal: impl Fn(&T) -> Option<()>) -> Option<I> {
        self.interned
            .index
            .lock()
            .find(hash, |(_, id)| match equal(self.get(*id)) {
                Some(()) => true,
                None => false,
            })
            .map(|(_, id)| *id)
    }

    fn publish<E: Copy>(
        &self,
        index: &mut HashTable<(u64, I)>,
        hash: u64,
        value: T,
        capacity_error: E,
    ) -> Result<I, E> {
        let entry_index =
            u32::try_from(self.interned.values.count()).map_err(|_| capacity_error)?;
        if entry_index > I::MAX_INDEX {
            return Err(capacity_error);
        }
        let id = I::from_index(entry_index);
        self.append(index, hash, id, value);
        Ok(id)
    }

    fn append(&self, index: &mut HashTable<(u64, I)>, hash: u64, id: I, value: T) {
        let actual = self.interned.values.push(value);
        assert_eq!(
            actual,
            id.index() as usize,
            "intern appends are serialized by the index lock"
        );
        index.insert_unique(hash, (hash, id), |(hash, _)| *hash);
    }
}

impl<I: ArenaId, T: Eq + Hash> Default for Intern<I, T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<I: ArenaId, T> Index<I> for Intern<I, T> {
    type Output = T;

    fn index(&self, id: I) -> &Self::Output {
        self.get(id)
    }
}
