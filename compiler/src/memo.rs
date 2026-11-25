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
    pub(crate) fn len(&self) -> usize {
        self.entries.lock().len()
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

pub(crate) enum Demand<K> {
    Child(K),
    Children(Vec<K>),
    Capacity(crate::arena::CapacityError),
}

impl<K> From<crate::arena::CapacityError> for Demand<K> {
    fn from(error: crate::arena::CapacityError) -> Self {
        Self::Capacity(error)
    }
}

/// Resolves acyclic dependencies against the caller's completed-result cache.
/// Wide nodes can enqueue every outstanding sibling in one pass.
pub(crate) fn resolve<S, K: Copy, R>(
    state: &mut S,
    root: impl Fn(&S) -> Result<R, K>,
    mut compute: impl FnMut(&mut S, K) -> Result<(), Demand<K>>,
) -> Result<R, crate::arena::CapacityError> {
    let mut pending = Vec::new();
    loop {
        let key = match pending.pop() {
            Some(key) => key,
            None => match root(state) {
                Ok(value) => return Ok(value),
                Err(key) => key,
            },
        };
        match compute(state, key) {
            Ok(()) => {}
            Err(Demand::Child(child)) => pending.extend([key, child]),
            Err(Demand::Children(children)) => {
                pending.push(key);
                pending.extend(children.into_iter().rev());
            }
            Err(Demand::Capacity(error)) => return Err(error),
        }
    }
}

pub(crate) enum VisitOrder {
    Forward,
    Reverse,
}

/// Returns every value, or all outstanding requests in the chosen traversal order.
pub(crate) fn collect<K: Copy, V, Q>(
    mut children: impl Iterator<Item = K>,
    lookup: impl Fn(K) -> Option<V>,
    request: impl Fn(K) -> Q,
    order: VisitOrder,
) -> Result<Vec<V>, Demand<Q>> {
    let mut mapped = Vec::with_capacity(children.size_hint().0);
    while let Some(child) = children.next() {
        match lookup(child) {
            Some(value) => mapped.push(value),
            None => {
                let mut missing = vec![request(child)];
                missing.extend(children.filter_map(|child| match lookup(child) {
                    Some(_) => None,
                    None => Some(request(child)),
                }));
                if let VisitOrder::Reverse = order {
                    missing.reverse();
                }
                return Err(Demand::Children(missing));
            }
        }
    }
    Ok(mapped)
}
