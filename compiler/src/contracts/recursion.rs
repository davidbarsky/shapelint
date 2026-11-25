use crate::contracts::graph::CapacityError;
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet};
use rustc_data_structures::graph::{DirectedGraph, Successors, scc::Sccs};
use rustc_hir::def_id::DefId;
use rustc_index::{Idx, IndexVec};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Revision(usize);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct ComponentId(u32);

impl Idx for ComponentId {
    fn new(index: usize) -> Self {
        Self(<u32 as Idx>::new(index))
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

#[derive(Default)]
struct Component {
    members: Vec<DefId>,
    outgoing: FxHashSet<ComponentId>,
    incoming: FxHashSet<ComponentId>,
    revision: Revision,
}

enum ComponentSlot {
    Live(Component),
    Merged(ComponentId),
}

#[derive(Default)]
struct Components(IndexVec<ComponentId, ComponentSlot>);

impl std::ops::Index<ComponentId> for Components {
    type Output = Component;

    fn index(&self, mut id: ComponentId) -> &Component {
        loop {
            match &self.0[id] {
                ComponentSlot::Live(component) => return component,
                ComponentSlot::Merged(root) => id = *root,
            }
        }
    }
}

impl std::ops::IndexMut<ComponentId> for Components {
    fn index_mut(&mut self, mut id: ComponentId) -> &mut Component {
        while let ComponentSlot::Merged(root) = self.0[id] {
            id = root;
        }
        let ComponentSlot::Live(component) = &mut self.0[id] else {
            unreachable!("followed merged components to a live slot")
        };
        component
    }
}

impl Components {
    fn merge_into(
        &mut self,
        mut id: ComponentId,
        root: ComponentId,
    ) -> Option<(ComponentId, Component)> {
        while id != root {
            match &mut self.0[id] {
                ComponentSlot::Live(component) => {
                    let component = std::mem::take(component);
                    self.0[id] = ComponentSlot::Merged(root);
                    return Some((id, component));
                }
                ComponentSlot::Merged(next) => id = *next,
            }
        }
        None
    }
}

struct Position {
    parent: Option<ComponentId>,
    left: Option<ComponentId>,
    right: Option<ComponentId>,
    size: usize,
}

#[derive(Default)]
struct Order {
    root: Option<ComponentId>,
    positions: IndexVec<ComponentId, Position>,
}

impl Order {
    fn size(&self, node: Option<ComponentId>) -> usize {
        match node {
            Some(node) => self.positions[node].size,
            None => 0,
        }
    }

    fn update(&mut self, node: ComponentId) {
        self.positions[node].size =
            1 + self.size(self.positions[node].left) + self.size(self.positions[node].right);
    }

    fn rotate(&mut self, node: ComponentId, parent: ComponentId) {
        let grandparent = self.positions[parent].parent;
        let middle = if self.positions[parent].left == Some(node) {
            let middle = self.positions[node].right;
            self.positions[parent].left = middle;
            self.positions[node].right = Some(parent);
            middle
        } else {
            let middle = self.positions[node].left;
            self.positions[parent].right = middle;
            self.positions[node].left = Some(parent);
            middle
        };
        if let Some(middle) = middle {
            self.positions[middle].parent = Some(parent);
        }
        self.positions[parent].parent = Some(node);
        self.positions[node].parent = grandparent;
        match grandparent {
            Some(grandparent) => {
                if self.positions[grandparent].left == Some(parent) {
                    self.positions[grandparent].left = Some(node);
                } else {
                    self.positions[grandparent].right = Some(node);
                }
            }
            None => self.root = Some(node),
        }
        self.update(parent);
        self.update(node);
    }

    fn splay(&mut self, node: ComponentId) {
        while let Some(parent) = self.positions[node].parent {
            let parent = if let Some(grandparent) = self.positions[parent].parent {
                if (self.positions[parent].left == Some(node))
                    == (self.positions[grandparent].left == Some(parent))
                {
                    self.rotate(parent, grandparent);
                    parent
                } else {
                    self.rotate(node, parent);
                    grandparent
                }
            } else {
                parent
            };
            self.rotate(node, parent);
        }
    }

    fn rightmost(&self, mut node: ComponentId) -> ComponentId {
        while let Some(right) = self.positions[node].right {
            node = right;
        }
        node
    }

    fn rank(&mut self, node: ComponentId) -> usize {
        self.splay(node);
        self.size(self.positions[node].left)
    }

    fn insert(&mut self, node: ComponentId, before: Option<ComponentId>) {
        match before {
            Some(before) => {
                self.splay(before);
                let left = self.positions[before].left.take();
                self.positions[node].left = left;
                self.positions[node].right = Some(before);
                self.positions[node].parent = None;
                self.positions[before].parent = Some(node);
                if let Some(left) = left {
                    self.positions[left].parent = Some(node);
                }
                self.root = Some(node);
                self.update(before);
                self.update(node);
            }
            None => match self.root {
                Some(root) => {
                    let last = self.rightmost(root);
                    self.splay(last);
                    self.positions[last].right = Some(node);
                    self.positions[node].parent = Some(last);
                    self.update(last);
                    self.splay(node);
                }
                None => self.root = Some(node),
            },
        }
    }

    fn remove(&mut self, node: ComponentId) {
        self.splay(node);
        let left = self.positions[node].left.take();
        let right = self.positions[node].right.take();
        self.positions[node].size = 1;
        if let Some(right) = right {
            self.positions[right].parent = None;
        }
        match left {
            Some(left) => {
                self.positions[left].parent = None;
                self.root = Some(left);
                let last = self.rightmost(left);
                self.splay(last);
                self.positions[last].right = right;
                if let Some(right) = right {
                    self.positions[right].parent = Some(last);
                }
                self.update(last);
            }
            None => self.root = right,
        }
    }

    fn move_after(&mut self, node: ComponentId, after: ComponentId) {
        self.remove(node);
        self.splay(after);
        let right = self.positions[after].right.take();
        self.positions[node].right = right;
        self.positions[node].parent = Some(after);
        self.positions[after].right = Some(node);
        if let Some(right) = right {
            self.positions[right].parent = Some(node);
        }
        self.update(node);
        self.update(after);
        self.splay(node);
    }
}

/// Retains a condensation graph as previously unresolved call edges become known.
///
/// Revisions change only when an SCC merge changes recursive-edge classification,
/// and propagate to callers that can have imported those requirements.
#[derive(Default)]
pub struct Recursion {
    pub work: Work,
    initial_edges: usize,
    edges: FxIndexSet<(DefId, DefId)>,
    definitions: FxHashMap<DefId, ComponentId>,
    components: Components,
    order: Order,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    pub forward_search_edges: usize,
    pub invalidated_components: usize,
}

struct Calls(IndexVec<usize, Vec<usize>>);

impl DirectedGraph for Calls {
    type Node = usize;
    fn num_nodes(&self) -> usize {
        self.0.len()
    }
}

impl Successors for Calls {
    fn successors(&self, node: usize) -> impl Iterator<Item = usize> {
        self.0[node].iter().copied()
    }
}

impl TryFrom<Vec<(DefId, DefId)>> for Recursion {
    type Error = CapacityError;
    fn try_from(edges: Vec<(DefId, DefId)>) -> Result<Self, CapacityError> {
        let edges: FxIndexSet<_> = edges.into_iter().collect();
        let mut nodes = FxIndexMap::default();
        let mut graph = Calls(IndexVec::new());
        for &(caller, callee) in &edges {
            let caller = *nodes
                .entry(caller)
                .or_insert_with(|| graph.0.push(Vec::new()));
            let callee = *nodes
                .entry(callee)
                .or_insert_with(|| graph.0.push(Vec::new()));
            graph.0[caller].push(callee);
        }
        let sccs = Sccs::<usize, usize>::new(&graph);
        if let Some(last) = sccs.num_sccs().checked_sub(1) {
            u32::try_from(last).map_err(|_| CapacityError::Queries)?;
        }
        let mut components = IndexVec::from_fn_n(|_| Component::default(), sccs.num_sccs());
        let mut definitions = FxHashMap::default();
        for (def, index) in nodes {
            let component =
                ComponentId(u32::try_from(sccs.scc(index)).map_err(|_| CapacityError::Queries)?);
            definitions.insert(def, component);
            components[component].members.push(def);
        }
        for &(caller, callee) in &edges {
            let caller = definitions[&caller];
            let callee = definitions[&callee];
            if caller != callee {
                components[caller].outgoing.insert(callee);
                components[callee].incoming.insert(caller);
            }
        }
        let mut order = Order::default();
        order.positions = (0..components.len())
            .map(|_| Position {
                parent: None,
                left: None,
                right: None,
                size: 1,
            })
            .collect();
        // rustc SCC indices are in dependency order; this order puts callers first.
        let callers_first = components.indices().rev();
        for component in callers_first {
            order.insert(component, None);
        }
        let recursion = Self {
            work: Work::default(),
            initial_edges: edges.len(),
            edges,
            definitions,
            components: Components(components.into_iter().map(ComponentSlot::Live).collect()),
            order,
        };
        Ok(recursion)
    }
}

impl Recursion {
    pub fn merged_revision(
        mut self,
        workers: impl IntoIterator<Item = Self>,
    ) -> Result<Option<Revision>, CapacityError> {
        for worker in workers {
            let discovered = worker.edges.iter().skip(worker.initial_edges);
            for &(caller, callee) in discovered {
                self.insert(caller, callee)?;
            }
        }
        Ok(self
            .components
            .0
            .iter()
            .filter_map(|slot| match slot {
                ComponentSlot::Live(component) => Some(component.revision),
                ComponentSlot::Merged(_) => None,
            })
            .find(|revision| *revision != Revision::default()))
    }

    pub fn revision(&self, def: DefId) -> Revision {
        match self.definitions.get(&def) {
            Some(&component) => self.components[component].revision,
            None => Revision::default(),
        }
    }

    pub(crate) fn recursive_definitions(&self) -> impl Iterator<Item = DefId> + '_ {
        self.definitions.iter().filter_map(|(&def, &component)| {
            (self.components[component].members.len() > 1 || self.edges.contains(&(def, def)))
                .then_some(def)
        })
    }

    /// Visits components in caller-before-callee order.
    pub fn components(&self) -> impl Iterator<Item = &[DefId]> {
        let mut pending = Vec::new();
        let mut next = self.order.root;
        std::iter::from_fn(move || {
            while let Some(node) = next {
                pending.push(node);
                next = self.order.positions[node].left;
            }
            let node = pending.pop()?;
            next = self.order.positions[node].right;
            Some(self.components[node].members.as_slice())
        })
    }

    pub fn insert(&mut self, caller: DefId, callee: DefId) -> Result<(), CapacityError> {
        if self.edges.contains(&(caller, callee)) {
            return Ok(());
        }
        let missing = std::iter::once(caller)
            .chain((caller != callee).then_some(callee))
            .filter(|def| !self.definitions.contains_key(def))
            .count();
        let count = self
            .components
            .0
            .len()
            .checked_add(missing)
            .ok_or(CapacityError::Queries)?;
        if let Some(last) = count.checked_sub(1) {
            u32::try_from(last).map_err(|_| CapacityError::Queries)?;
        }
        self.edges.insert((caller, callee));
        for (def, before) in [
            (caller, self.definitions.get(&callee).copied()),
            (callee, None),
        ] {
            if self.definitions.contains_key(&def) {
                continue;
            }
            let component = self.components.0.push(ComponentSlot::Live(Component {
                members: vec![def],
                outgoing: FxHashSet::default(),
                incoming: FxHashSet::default(),
                revision: Revision::default(),
            }));
            self.order.positions.push(Position {
                parent: None,
                left: None,
                right: None,
                size: 1,
            });
            self.order.insert(component, before);
            self.definitions.insert(def, component);
        }
        let caller = self.definitions[&caller];
        let callee = self.definitions[&callee];
        if caller == callee || !self.components[caller].outgoing.insert(callee) {
            return Ok(());
        }
        self.components[callee].incoming.insert(caller);
        let end = self.order.rank(caller);
        if end < self.order.rank(callee) {
            return Ok(());
        }
        let mut forward = FxHashMap::default();
        forward.insert(callee, self.order.rank(callee));
        let mut pending = vec![callee];
        while let Some(component) = pending.pop() {
            for &successor in &self.components[component].outgoing {
                self.work.forward_search_edges = self.work.forward_search_edges.saturating_add(1);
                if forward.contains_key(&successor) {
                    continue;
                }
                let position = self.order.rank(successor);
                if position <= end {
                    forward.insert(successor, position);
                    pending.push(successor);
                }
            }
        }
        let mut merged = FxHashSet::default();
        if forward.contains_key(&caller) {
            merged.insert(caller);
            pending.push(caller);
            while let Some(component) = pending.pop() {
                for &predecessor in &self.components[component].incoming {
                    if forward.contains_key(&predecessor) && merged.insert(predecessor) {
                        pending.push(predecessor);
                    }
                }
            }
        }
        let mut after = caller;
        if let Some(root) = merged
            .iter()
            .copied()
            .max_by_key(|&id| self.components[id].members.len())
        {
            let revision = Revision(self.edges.len());
            let mut invalidated = FxHashSet::default();
            invalidated.insert(caller);
            pending.push(caller);
            while let Some(component) = pending.pop() {
                self.work.invalidated_components =
                    self.work.invalidated_components.saturating_add(1);
                let component = &mut self.components[component];
                component.revision = revision;
                for &predecessor in &component.incoming {
                    if invalidated.insert(predecessor) {
                        pending.push(predecessor);
                    }
                }
            }
            if root != caller {
                self.order.move_after(root, caller);
            }
            for &component in &merged {
                self.components[root].outgoing.remove(&component);
                self.components[root].incoming.remove(&component);
                let Some((component, absorbed)) = self.components.merge_into(component, root)
                else {
                    continue;
                };
                self.order.remove(component);
                for def in &absorbed.members {
                    self.definitions.insert(*def, root);
                }
                self.components[root].members.extend(absorbed.members);
                for child in absorbed.outgoing {
                    if !merged.contains(&child) {
                        let parents = &mut self.components[child].incoming;
                        parents.remove(&component);
                        parents.insert(root);
                        self.components[root].outgoing.insert(child);
                    }
                }
                for parent in absorbed.incoming {
                    if !merged.contains(&parent) {
                        let children = &mut self.components[parent].outgoing;
                        children.remove(&component);
                        children.insert(root);
                        self.components[root].incoming.insert(parent);
                    }
                }
            }
            after = root;
        }
        let mut moved: Vec<_> = forward
            .into_iter()
            .filter(|(component, _)| !merged.contains(component))
            .collect();
        moved.sort_unstable_by_key(|(_, position)| *position);
        for (component, _) in moved {
            self.order.move_after(component, after);
            after = component;
        }
        Ok(())
    }

    pub fn edge(
        &mut self,
        caller: DefId,
        callee: DefId,
    ) -> Result<Option<(DefId, DefId)>, CapacityError> {
        self.insert(caller, callee)?;
        Ok(
            match self.definitions[&caller] == self.definitions[&callee] {
                true => Some((caller, callee)),
                false => None,
            },
        )
    }
}
