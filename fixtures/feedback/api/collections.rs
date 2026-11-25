use std::collections::{BTreeMap, BTreeSet};

struct Registry {
    entries: BTreeMap<Key, Entry>,
    membership: std::collections::BTreeSet<Key>,
}

fn build() {
    let mut registry = BTreeMap::new();
    registry.insert(Key::A, Entry::new());
}

struct InsertionOrdered { entries: indexmap::IndexMap<Key, Entry> }
struct LookupOnly { entries: rustc_hash::FxHashMap<Key, Entry> }

// shapelint: allow(collection-choice) Range queries implement the ordered index contract.
struct OrderedIndex {
    entries: BTreeMap<Key, Entry>,
}
