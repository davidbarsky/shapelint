use std::cmp::Reverse;
use std::collections::BinaryHeap;

use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::graph::{Successors, scc::Sccs};
use rustc_index::{Idx, IndexVec};

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct Rank(usize);

impl Idx for Rank {
    fn new(index: usize) -> Self {
        Self(index)
    }
    fn index(self) -> usize {
        self.0
    }
}

#[derive(Default)]
struct Component {
    current: BinaryHeap<Reverse<Rank>>,
    next: BinaryHeap<Reverse<Rank>>,
    cursor: Option<Rank>,
}

/// Completes each component before activating its downstream consumers.
/// Within a component, backward updates wait for the next ordered round.
pub struct Schedule<N: Idx> {
    sccs: Sccs<N, usize>,
    components: Vec<Component>,
    ranks: IndexVec<N, Option<Rank>>,
    nodes: IndexVec<Rank, N>,
    queued: FxHashSet<N>,
}

impl<N: Idx> Schedule<N> {
    /// Uses the execution graph's reverse postorder; omitted nodes stay unreachable.
    pub fn new(graph: &impl Successors<Node = N>, order: &[N], entry: N) -> Self {
        let sccs = Sccs::new(graph);
        let components = sccs.all_sccs().map(|_| Component::default()).collect();
        let mut ranks = IndexVec::from_elem_n(None, graph.num_nodes());
        let nodes = IndexVec::from_raw(order.to_vec());
        let entries = nodes.iter_enumerated();
        for (rank, &node) in entries {
            ranks[node] = Some(rank);
        }
        let mut schedule = Self {
            sccs,
            components,
            ranks,
            nodes,
            queued: FxHashSet::default(),
        };
        schedule.changed(entry);
        schedule
    }

    pub fn changed(&mut self, node: N) {
        let Some(rank) = self.ranks[node] else {
            return;
        };
        let Some(component) = self.components.get_mut(self.sccs.scc(node)) else {
            return; // This component has completed.
        };
        if !self.queued.insert(node) {
            return;
        }
        match component.cursor {
            Some(cursor) if rank <= cursor => component.next.push(Reverse(rank)),
            Some(_) | None => component.current.push(Reverse(rank)),
        }
    }

    pub fn pop(&mut self) -> Option<N> {
        while let Some(component) = self.components.last_mut() {
            if let Some(Reverse(rank)) = component.current.pop() {
                component.cursor = Some(rank);
                let node = self.nodes[rank];
                self.queued.remove(&node);
                return Some(node);
            }
            if component.next.is_empty() {
                self.components.pop();
            } else {
                std::mem::swap(&mut component.current, &mut component.next);
                component.cursor = None;
            }
        }
        None
    }
}
