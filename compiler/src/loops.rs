use std::ops::Range;

use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::graph::Predecessors;
use rustc_data_structures::graph::dominators::Dominators;
use rustc_data_structures::union_find::UnionFind;
use rustc_index::IndexVec;
use rustc_middle::mir::BasicBlock;

pub struct Node {
    pub parent: Option<BasicBlock>,
    pub innermost: Option<BasicBlock>,
    pub range: Range<usize>,
}

/// Keeps natural-loop membership as nested intervals, including each loop's header.
/// The supplied backedges determine the edge policy; predecessors retain the full CFG.
pub struct Forest {
    nodes: IndexVec<BasicBlock, Node>,
    order: Vec<BasicBlock>,
}

impl Forest {
    pub fn new(
        graph: &impl Predecessors<Node = BasicBlock>,
        dominators: &Dominators<BasicBlock>,
        order: &[BasicBlock],
        headers: &FxHashMap<BasicBlock, Vec<BasicBlock>>,
    ) -> Self {
        let mut groups = UnionFind::new(graph.num_nodes());
        let mut representatives: IndexVec<BasicBlock, BasicBlock> =
            IndexVec::from_fn_n(std::convert::identity, graph.num_nodes());
        let mut parents = IndexVec::from_elem_n(None, graph.num_nodes());
        let headers_in_reverse = order.iter().rev();
        for &header in headers_in_reverse {
            let Some(tails) = headers.get(&header) else {
                continue;
            };
            let mut pending = tails.clone();
            while let Some(tail) = pending.pop() {
                let member = representatives[groups.find(tail)];
                if member == header
                    || !dominators.is_reachable(member)
                    || !dominators.dominates(header, member)
                {
                    continue;
                }
                // A dominated natural loop has no external entry except its header.
                // Collapsed inner loops therefore expose exactly this predecessor list.
                pending.extend(graph.predecessors(member));
                parents[member] = Some(header);
                let root = groups.unify(member, header);
                representatives[root] = header;
            }
        }
        let mut children =
            IndexVec::<BasicBlock, Vec<BasicBlock>>::from_elem_n(Vec::new(), graph.num_nodes());
        let mut roots = Vec::new();
        for (block, parent) in parents.iter_enumerated() {
            match parent {
                Some(parent) => children[*parent].push(block),
                None => roots.push(block),
            }
        }
        enum Visit {
            Enter(BasicBlock, Option<BasicBlock>),
            Leave(BasicBlock),
        }
        let mut nodes = IndexVec::from_fn_n(
            |_| Node {
                parent: None,
                innermost: None,
                range: 0..0,
            },
            graph.num_nodes(),
        );
        let mut order = Vec::with_capacity(graph.num_nodes());
        let mut pending: Vec<_> = roots
            .into_iter()
            .rev()
            .map(|block| Visit::Enter(block, None))
            .collect();
        while let Some(visit) = pending.pop() {
            match visit {
                Visit::Enter(block, outer) => {
                    let innermost = match headers.contains_key(&block) {
                        true => Some(block),
                        false => outer,
                    };
                    nodes[block] = Node {
                        parent: parents[block],
                        innermost,
                        range: order.len()..0,
                    };
                    order.push(block);
                    pending.push(Visit::Leave(block));
                    pending.extend(
                        children[block]
                            .iter()
                            .rev()
                            .map(|child| Visit::Enter(*child, innermost)),
                    );
                }
                Visit::Leave(block) => nodes[block].range.end = order.len(),
            }
        }
        Self { nodes, order }
    }

    pub fn writes<'a, 'g>(
        &self,
        events: impl IntoIterator<Item = (BasicBlock, &'a crate::contracts::Writes<'g>)>,
        sets: &mut impl crate::contracts::ArgumentUnion<'g>,
    ) -> Result<
        FxHashMap<BasicBlock, crate::contracts::Writes<'g>>,
        crate::contracts::graph::CapacityError,
    >
    where
        'g: 'a,
    {
        let mut writes: FxHashMap<BasicBlock, crate::contracts::Writes<'g>> = FxHashMap::default();
        for (block, event) in events {
            if let Some(header) = self.nodes[block].innermost {
                writes.entry(header).or_default().merge(event, sets)?;
            }
        }
        let headers = self.headers().rev();
        for header in headers {
            let inner = writes.remove(&header).unwrap_or_default();
            if let Some(parent) = self.nodes[header].parent {
                writes.entry(parent).or_default().merge(&inner, sets)?;
            }
            writes.insert(header, inner);
        }
        Ok(writes)
    }

    pub fn headers(&self) -> impl DoubleEndedIterator<Item = BasicBlock> + '_ {
        self.order
            .iter()
            .copied()
            .filter(|block| self.nodes[*block].innermost == Some(*block))
    }
}

impl std::ops::Index<BasicBlock> for Forest {
    type Output = Node;

    fn index(&self, block: BasicBlock) -> &Self::Output {
        &self.nodes[block]
    }
}

#[derive(Clone, Copy)]
struct Jump {
    target: BasicBlock,
    minimum: usize,
    maximum: usize,
}

/// Skips postdominator prefixes contained in one natural loop.
pub struct Exits {
    jumps: IndexVec<BasicBlock, Vec<Jump>>,
}

impl Exits {
    pub fn new(forest: &Forest, dominators: &Dominators<BasicBlock>, count: usize) -> Self {
        let mut children = IndexVec::<BasicBlock, Vec<BasicBlock>>::from_elem_n(Vec::new(), count);
        let mut roots = Vec::new();
        for index in 0..count {
            let block = BasicBlock::from_usize(index);
            match dominators.immediate_dominator(block) {
                Some(parent) => children[parent].push(block),
                None => roots.push(block),
            }
        }
        let mut jumps = IndexVec::<BasicBlock, Vec<Jump>>::from_fn_n(|_| Vec::new(), count);
        let mut pending = roots;
        while let Some(block) = pending.pop() {
            pending.extend(children[block].iter().copied());
            let Some(parent) = dominators.immediate_dominator(block) else {
                continue;
            };
            let position = match forest.nodes.get(parent) {
                Some(node) => node.range.start,
                None => forest.order.len(),
            };
            let mut jump = Jump {
                target: parent,
                minimum: position,
                maximum: position,
            };
            jumps[block].push(jump);
            for level in 0.. {
                let Some(next) = jumps[jump.target].get(level) else {
                    break;
                };
                jump.minimum = jump.minimum.min(next.minimum);
                jump.maximum = jump.maximum.max(next.maximum);
                jump.target = next.target;
                jumps[block].push(jump);
            }
        }
        Self { jumps }
    }

    pub fn boundary(&self, forest: &Forest, header: BasicBlock) -> Option<BasicBlock> {
        let range = &forest[header].range;
        let mut block = header;
        for level in (0..self.jumps[header].len()).rev() {
            if let Some(jump) = self.jumps[block].get(level)
                && range.contains(&jump.minimum)
                && range.contains(&jump.maximum)
            {
                block = jump.target;
            }
        }
        self.jumps[block].first().map(|jump| jump.target)
    }
}
