use parking_lot::Mutex;
use std::hash::Hash;
use std::sync::Arc;

use rustc_data_structures::fx::FxHashMap;

/// Shares completed pure results across graph views.
pub(crate) struct Memo<K, V> {
    entries: Arc<Mutex<FxHashMap<K, V>>>,
}

impl<K, V> Clone for Memo<K, V> {
    fn clone(&self) -> Self {
        Self {
            entries: Arc::clone(&self.entries),
        }
    }
}

impl<K: Eq + Hash, V: Copy> Memo<K, V> {
    pub(crate) fn new() -> Self {
        Self {
            entries: Arc::new(Mutex::new(FxHashMap::default())),
        }
    }

    // shapelint: allow(shallow-helper) The lock stays inside this shared memo boundary.
    #[shapelint_tool::arena(lookup)]
    pub(crate) fn get(&self, key: &K) -> Option<V> {
        self.entries.lock().get(key).copied()
    }

    // shapelint: allow(shallow-helper) The lock stays inside this shared memo boundary.
    #[shapelint_tool::arena(remember)]
    pub(crate) fn insert(&self, key: K, value: V) -> Option<V> {
        self.entries.lock().insert(key, value)
    }
}

impl<K: Eq + Hash, V: Copy> Default for Memo<K, V> {
    fn default() -> Self {
        Self::new()
    }
}
