#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_middle;

use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexSet};
use rustc_data_structures::graph::iterate::DepthFirstSearch;
use rustc_data_structures::graph::vec_graph::VecGraph;
use rustc_data_structures::graph::{
    DirectedGraph, Predecessors, StartNode, Successors, dominators,
};
use rustc_middle::mir::BasicBlock;
use shapelint_driver::contracts::Writes;
use shapelint_driver::loops::{Exits, Forest};

struct Graph {
    edges: VecGraph<BasicBlock, true>,
    start: BasicBlock,
}

impl DirectedGraph for Graph {
    type Node = BasicBlock;

    fn num_nodes(&self) -> usize {
        self.edges.num_nodes()
    }
}
impl StartNode for Graph {
    fn start_node(&self) -> BasicBlock {
        self.start
    }
}
impl Successors for Graph {
    fn successors(&self, node: BasicBlock) -> impl Iterator<Item = BasicBlock> {
        self.edges.successors(node).iter().copied()
    }
}
impl Predecessors for Graph {
    fn predecessors(&self, node: BasicBlock) -> impl Iterator<Item = BasicBlock> {
        self.edges.predecessors(node).iter().copied()
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum EdgeKind {
    Execution,
    Cancellation,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Policy {
    Execution,
    All,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Edge {
    source: u64,
    target: u64,
    kind: EdgeKind,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Write {
    None,
    Unknown,
    Argument(u8),
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Event {
    block: u64,
    write: Write,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Case {
    edges: Vec<Edge>,
    events: Vec<Event>,
    policy: Policy,
}

#[hegel::test(print_blob = true)]
fn loop_membership_writes_and_boundaries_match_naive_walks(tc: hegel::TestCase) {
    let Case {
        mut edges,
        mut events,
        policy,
    } = tc.draw(hegel::generators::default::<Case>());
    // Nested loops, multiple latches, a two-entry SCC, and an unreachable incoming edge.
    edges.extend([
        Edge {
            source: 0,
            target: 1,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 1,
            target: 2,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 2,
            target: 3,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 3,
            target: 2,
            kind: EdgeKind::Cancellation,
        },
        Edge {
            source: 2,
            target: 4,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 4,
            target: 1,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 1,
            target: 5,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 5,
            target: 1,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 0,
            target: 6,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 6,
            target: 7,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 7,
            target: 6,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 0,
            target: 7,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 8,
            target: 2,
            kind: EdgeKind::Execution,
        },
        Edge {
            source: 1,
            target: 9,
            kind: EdgeKind::Execution,
        },
    ]);
    events.extend([
        Event {
            block: 1,
            write: Write::Argument(1),
        },
        Event {
            block: 3,
            write: Write::Argument(3),
        },
        Event {
            block: 5,
            write: Write::Argument(5),
        },
        Event {
            block: 8,
            write: Write::Unknown,
        },
    ]);
    let mut names = FxIndexSet::from_iter([0]);
    for edge in &edges {
        names.insert(edge.source);
        names.insert(edge.target);
    }
    for event in &events {
        names.insert(event.block);
    }
    let blocks: FxHashMap<_, _> = names
        .into_iter()
        .enumerate()
        .map(|(index, name)| (name, BasicBlock::from_usize(index)))
        .collect();
    let graph = Graph {
        edges: VecGraph::new(
            blocks.len(),
            edges
                .iter()
                .map(|edge| (blocks[&edge.source], blocks[&edge.target]))
                .collect(),
        ),
        start: blocks[&0],
    };
    let dominators = dominators::dominators(&graph);
    let order: Vec<_> = DepthFirstSearch::new(&graph)
        .with_start_node(graph.start)
        .collect();
    let mut headers: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
    let mut reversed = Vec::new();
    let mut normal_sources = FxHashSet::default();
    for edge in &edges {
        match (policy, edge.kind) {
            (Policy::Execution, EdgeKind::Cancellation) => continue,
            (Policy::All, _) | (Policy::Execution, EdgeKind::Execution) => {}
        }
        let (source, target) = (blocks[&edge.source], blocks[&edge.target]);
        reversed.push((target, source));
        normal_sources.insert(source);
        if dominators.is_reachable(source) && dominators.dominates(target, source) {
            headers.entry(target).or_default().push(source);
        }
    }
    let exit = BasicBlock::from_usize(blocks.len());
    for &block in blocks.values() {
        if !normal_sources.contains(&block) {
            reversed.push((exit, block));
        }
    }
    let reverse = Graph {
        edges: VecGraph::new(blocks.len() + 1, reversed),
        start: exit,
    };
    let postdominators = dominators::dominators(&reverse);
    let forest = Forest::new(&graph, &dominators, &order, &headers);
    let exits = Exits::new(&forest, &postdominators, graph.num_nodes() + 1);
    let mut memberships = FxHashMap::default();
    for (&header, tails) in &headers {
        let mut members = FxHashSet::from_iter([header]);
        let mut pending = tails.clone();
        while let Some(block) = pending.pop() {
            if !dominators.is_reachable(block)
                || !dominators.dominates(header, block)
                || !members.insert(block)
            {
                continue;
            }
            pending.extend(graph.predecessors(block));
        }
        let actual: FxHashSet<_> = blocks
            .values()
            .copied()
            .filter(|block| forest[header].range.contains(&forest[*block].range.start))
            .collect();
        assert_eq!(actual, members, "header {header:?}; {edges:?}");
        let mut boundary = postdominators.immediate_dominator(header);
        while let Some(block) = boundary {
            if !members.contains(&block) {
                break;
            }
            boundary = postdominators.immediate_dominator(block);
        }
        assert_eq!(
            exits.boundary(&forest, header),
            boundary,
            "header {header:?}; {edges:?}"
        );
        memberships.insert(header, members);
    }
    for &block in blocks.values() {
        let expected = memberships
            .iter()
            .filter(|(_, members)| members.contains(&block))
            .min_by_key(|(_, members)| members.len())
            .map(|(header, _)| *header);
        assert_eq!(
            forest[block].innermost, expected,
            "block {block:?}; {edges:?}"
        );
    }
    shapelint_driver::contracts::graph::sets::with_sets(|sets| {
        let event_writes: Vec<_> = events
            .iter()
            .map(|event| {
                let write = match event.write {
                    Write::None => Writes::None,
                    Write::Unknown => Writes::Unknown,
                    Write::Argument(index) => Writes::Arguments(
                        sets.insert(
                            shapelint_driver::contracts::graph::sets::SetId::EMPTY,
                            usize::from(index),
                        )
                        .unwrap(),
                    ),
                };
                (blocks[&event.block], write)
            })
            .collect();
        let actual = forest
            .writes(
                event_writes.iter().map(|(block, write)| (*block, write)),
                sets,
            )
            .unwrap();
        for (header, members) in memberships {
            let mut expected = Some(FxHashSet::default());
            for event in &events {
                if !members.contains(&blocks[&event.block]) {
                    continue;
                }
                match event.write {
                    Write::None => {}
                    Write::Unknown => expected = None,
                    Write::Argument(index) => {
                        if let Some(arguments) = &mut expected {
                            arguments.insert(usize::from(index));
                        }
                    }
                }
            }
            match (&actual[&header], expected) {
                (Writes::Unknown, None) => {}
                (Writes::None, Some(arguments)) => assert!(arguments.is_empty()),
                (Writes::Arguments(actual), Some(expected)) => {
                    assert_eq!(sets.iter(*actual).collect::<FxHashSet<_>>(), expected)
                }
                _ => panic!("incorrect writes for {header:?}; {events:?}"),
            }
        }
    });
}

#[test]
fn deeply_nested_loops_share_membership_and_exit_searches() {
    let depth = 100_000;
    let mut edges = Vec::new();
    for index in 0..depth {
        edges.push((
            BasicBlock::from_usize(index),
            BasicBlock::from_usize(index + 1),
        ));
        edges.push((
            BasicBlock::from_usize(index + 1),
            BasicBlock::from_usize(index),
        ));
    }
    let exit = BasicBlock::from_usize(depth + 1);
    edges.push((BasicBlock::from_usize(depth), exit));
    let reverse = Graph {
        edges: VecGraph::new(
            depth + 2,
            edges
                .iter()
                .map(|(source, target)| (*target, *source))
                .collect(),
        ),
        start: exit,
    };
    let graph = Graph {
        edges: VecGraph::new(depth + 2, edges),
        start: BasicBlock::from_usize(0),
    };
    let dominators = dominators::dominators(&graph);
    let postdominators = dominators::dominators(&reverse);
    let order: Vec<_> = DepthFirstSearch::new(&graph)
        .with_start_node(graph.start)
        .collect();
    let headers = (0..depth)
        .map(|index| {
            (
                BasicBlock::from_usize(index),
                vec![BasicBlock::from_usize(index + 1)],
            )
        })
        .collect();
    let forest = Forest::new(&graph, &dominators, &order, &headers);
    let exits = Exits::new(&forest, &postdominators, graph.num_nodes());
    assert_eq!(forest.headers().count(), depth);
    for index in 0..depth {
        let header = BasicBlock::from_usize(index);
        assert_eq!(forest[header].range.len(), depth - index + 1);
        assert_eq!(exits.boundary(&forest, header), Some(exit));
    }
}
