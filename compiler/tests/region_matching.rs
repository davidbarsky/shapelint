#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::{DefIndex, LocalDefId};
use rustc_middle::mir::{BasicBlock, Local};
use rustc_span::{BytePos, DUMMY_SP};
use shapelint_driver::regions::matching::{Block, Body, Input, Phase, with_matcher};
use shapelint_driver::regions::{Atom, Suffixes};

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum Variable {
    First,
    Second,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum Execution {
    Normal,
    Cleanup,
}

#[derive(Clone, Debug)]
struct Operation {
    code: u8,
    local: Variable,
}

#[derive(Clone, Debug)]
struct Node {
    phase: Execution,
    operations: Vec<Operation>,
    successors: Vec<usize>,
}

#[derive(Clone, Debug)]
struct Model {
    owner: usize,
    nodes: Vec<Node>,
    types: [u8; 2],
}

impl From<&Model> for Input {
    fn from(model: &Model) -> Self {
        let blocks = model
            .nodes
            .iter()
            .map(|node| Block {
                phase: match node.phase {
                    Execution::Normal => Phase::Execution,
                    Execution::Cleanup => Phase::Cleanup,
                },
                suffixes: Suffixes::try_from(
                    node.operations
                        .iter()
                        .map(|operation| Atom {
                            fingerprint: Fingerprint::new(u64::from(operation.code), 0u64),
                            locals: vec![Local::from_usize(match operation.local {
                                Variable::First => 0,
                                Variable::Second => 1,
                            })],
                        })
                        .collect::<Vec<_>>(),
                )
                .unwrap(),
                successors: node
                    .successors
                    .iter()
                    .copied()
                    .map(BasicBlock::from_usize)
                    .collect(),
            })
            .collect();
        let types = model
            .types
            .iter()
            .enumerate()
            .map(|(local, ty)| {
                (
                    Local::from_usize(local),
                    Fingerprint::new(u64::from(*ty), 0u64),
                )
            })
            .collect();
        Self {
            owner: LocalDefId {
                local_def_index: DefIndex::from_usize(model.owner),
            },
            coroutine: Fingerprint::ZERO,
            blocks,
            types,
        }
    }
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum Step {
    Line { code: u8, local: Variable },
    Branch { local: Variable },
    Cycle { local: Variable },
    Exit { phase: Execution, local: Variable },
}

impl From<Vec<Step>> for Model {
    fn from(steps: Vec<Step>) -> Self {
        let mut nodes = vec![
            Node {
                phase: Execution::Normal,
                operations: vec![Operation {
                    code: 100,
                    local: Variable::First,
                }],
                successors: vec![1, 2],
            },
            Node {
                phase: Execution::Normal,
                operations: vec![Operation {
                    code: 101,
                    local: Variable::First,
                }],
                successors: vec![3],
            },
            Node {
                phase: Execution::Normal,
                operations: vec![Operation {
                    code: 102,
                    local: Variable::Second,
                }],
                successors: vec![3],
            },
            Node {
                phase: Execution::Normal,
                operations: vec![Operation {
                    code: 103,
                    local: Variable::First,
                }],
                successors: Vec::new(),
            },
        ];
        let mut tail = 3;
        for step in steps {
            let entry = nodes.len();
            nodes[tail].successors.push(entry);
            match step {
                Step::Line { code, local } => {
                    nodes.push(Node {
                        phase: Execution::Normal,
                        operations: vec![Operation { code, local }],
                        successors: Vec::new(),
                    });
                    tail = entry;
                }
                Step::Branch { local } => {
                    nodes.push(Node {
                        phase: Execution::Normal,
                        operations: vec![Operation { code: 1, local }],
                        successors: vec![entry + 1, entry + 2],
                    });
                    nodes.push(Node {
                        phase: Execution::Normal,
                        operations: vec![Operation { code: 2, local }],
                        successors: vec![entry + 3],
                    });
                    nodes.push(Node {
                        phase: Execution::Normal,
                        operations: vec![Operation {
                            code: 2,
                            local: Variable::First,
                        }],
                        successors: vec![entry + 3],
                    });
                    nodes.push(Node {
                        phase: Execution::Normal,
                        operations: vec![Operation { code: 3, local }],
                        successors: Vec::new(),
                    });
                    tail = entry + 3;
                }
                Step::Cycle { local } => {
                    nodes.push(Node {
                        phase: Execution::Normal,
                        operations: vec![Operation { code: 4, local }],
                        successors: vec![entry + 1, entry + 2],
                    });
                    nodes.push(Node {
                        phase: Execution::Normal,
                        operations: vec![Operation { code: 5, local }],
                        successors: vec![entry],
                    });
                    nodes.push(Node {
                        phase: Execution::Normal,
                        operations: vec![Operation { code: 6, local }],
                        successors: Vec::new(),
                    });
                    tail = entry + 2;
                }
                Step::Exit { phase, local } => {
                    nodes.push(Node {
                        phase: Execution::Normal,
                        operations: vec![Operation { code: 7, local }],
                        successors: vec![entry + 1, entry + 2],
                    });
                    nodes.push(Node {
                        phase: Execution::Normal,
                        operations: vec![Operation { code: 8, local }],
                        successors: Vec::new(),
                    });
                    nodes.push(Node {
                        phase,
                        operations: vec![Operation { code: 9, local }],
                        successors: Vec::new(),
                    });
                    tail = entry + 1;
                }
            }
        }
        let last = nodes.len();
        nodes[tail].successors.push(last);
        nodes.push(Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 255,
                local: Variable::First,
            }],
            successors: Vec::new(),
        });
        Self {
            owner: 0,
            nodes,
            types: [1, 1],
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Edit {
    Rename,
    LastOperation,
    LastAlias,
    Type,
    OrderedTargets,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Scope {
    Whole,
    BeforeLast,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Case {
    steps: Vec<Step>,
    edit: Edit,
    scope: Scope,
}

#[derive(Debug, PartialEq, Eq)]
struct Canonical {
    phase: Execution,
    operations: Vec<(u8, usize, u8)>,
    successors: Vec<usize>,
}

fn canonical(model: &Model, entry: usize, start: usize, boundary: Option<usize>) -> Vec<Canonical> {
    let mut order = Vec::new();
    let mut blocks = FxHashMap::default();
    let mut pending = vec![entry];
    while let Some(block) = pending.pop() {
        match (Some(block) == boundary, blocks.get(&block)) {
            (true, _) | (_, Some(_)) => continue,
            (false, None) => {}
        }
        blocks.insert(block, order.len());
        order.push(block);
        pending.extend(model.nodes[block].successors.iter().rev().copied());
    }
    if let Some(boundary) = boundary {
        blocks.insert(boundary, order.len());
    }
    let mut locals = Vec::new();
    let mut result = Vec::new();
    for block in order {
        let offset = match block == entry {
            true => start,
            false => 0,
        };
        let mut operations = Vec::new();
        for operation in &model.nodes[block].operations[offset..] {
            let number = match locals.iter().position(|local| *local == operation.local) {
                Some(number) => number,
                None => {
                    let number = locals.len();
                    locals.push(operation.local);
                    number
                }
            };
            let ty = model.types[match operation.local {
                Variable::First => 0,
                Variable::Second => 1,
            }];
            operations.push((operation.code, number, ty));
        }
        result.push(Canonical {
            phase: model.nodes[block].phase,
            operations,
            successors: model.nodes[block]
                .successors
                .iter()
                .map(|target| blocks[target])
                .collect(),
        });
    }
    result
}

#[hegel::test(print_blob = true)]
fn matching_agrees_with_independent_canonical_graphs(tc: hegel::TestCase) {
    let Case { steps, edit, scope } = tc.draw(hegel::generators::default::<Case>());
    let left = Model::from(steps);
    let mut right = left.clone();
    right.owner = 1;
    match edit {
        Edit::Rename => {
            for node in &mut right.nodes {
                for operation in &mut node.operations {
                    operation.local = match operation.local {
                        Variable::First => Variable::Second,
                        Variable::Second => Variable::First,
                    };
                }
            }
            right.types.swap(0, 1);
        }
        Edit::LastOperation => right.nodes.last_mut().unwrap().operations[0].code = 254,
        Edit::LastAlias => right.nodes.last_mut().unwrap().operations[0].local = Variable::Second,
        Edit::Type => right.types[0] = 2,
        Edit::OrderedTargets => right.nodes[0].successors.reverse(),
    }
    let boundary = match scope {
        Scope::Whole => None,
        Scope::BeforeLast => Some(left.nodes.len() - 1),
    };
    let expected = canonical(&left, 0, 0, boundary) == canonical(&right, 0, 0, boundary);
    let left_body = Body::try_from(Input::from(&left)).unwrap();
    let right_body = Body::try_from(Input::from(&right)).unwrap();
    let left_region = left_body
        .candidate(
            BasicBlock::from_usize(0),
            0,
            boundary.map(BasicBlock::from_usize),
            DUMMY_SP,
        )
        .unwrap();
    let right_region = right_body
        .candidate(
            BasicBlock::from_usize(0),
            0,
            boundary.map(BasicBlock::from_usize),
            DUMMY_SP,
        )
        .unwrap();
    with_matcher(|matcher| {
        let left_body_owner = left_body.owner;
        let left_body_id = matcher.register(left_body).unwrap();
        let right_body_id = matcher.register(right_body).unwrap();

        match matcher.insert(left_body_id, left_region).unwrap() {
            None => {}
            Some(_) => panic!("first candidate has no original"),
        }
        match (
            expected,
            matcher.insert(right_body_id, right_region).unwrap(),
        ) {
            (true, Some(original)) => assert_eq!(original.owner, left_body_owner),
            (false, None) => {}
            (expected, actual) => panic!(
                "{edit:?}/{scope:?}: expected match={expected}, got original={:?}; left={left:?}, right={right:?}",
                actual.map(|candidate| candidate.owner)
            ),
        }
    });
}

#[test]
fn matching_preserves_shared_targets_across_distinct_branch_ports() {
    let mut left = Model::from(Vec::new());
    left.nodes = vec![
        Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 0,
                local: Variable::First,
            }],
            successors: vec![1, 2],
        },
        Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 1,
                local: Variable::First,
            }],
            successors: vec![3, 4],
        },
        Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 1,
                local: Variable::First,
            }],
            successors: vec![3, 4],
        },
        Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 2,
                local: Variable::First,
            }],
            successors: Vec::new(),
        },
        Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 2,
                local: Variable::First,
            }],
            successors: Vec::new(),
        },
    ];
    let mut right = left.clone();
    right.owner = 1;
    right.nodes[2].successors.reverse();
    assert_ne!(canonical(&left, 0, 0, None), canonical(&right, 0, 0, None));
    let left = Body::try_from(Input::from(&left)).unwrap();
    let right = Body::try_from(Input::from(&right)).unwrap();
    with_matcher(|matcher| {
        let left_id = matcher.register(left).unwrap();
        let right_id = matcher.register(right).unwrap();

        matcher
            .insert(
                left_id,
                matcher
                    .candidate(left_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                    .unwrap(),
            )
            .unwrap();
        match matcher
            .insert(
                right_id,
                matcher
                    .candidate(right_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                    .unwrap(),
            )
            .unwrap()
        {
            None => {}
            Some(_) => panic!("a shared target cannot map to two different targets"),
        }
    });
}

#[test]
fn backedges_keep_the_root_statement_suffix() {
    let mut left = Model::from(Vec::new());
    left.nodes = vec![
        Node {
            phase: Execution::Normal,
            operations: vec![
                Operation {
                    code: 1,
                    local: Variable::First,
                },
                Operation {
                    code: 2,
                    local: Variable::First,
                },
            ],
            successors: vec![0, 1],
        },
        Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 3,
                local: Variable::First,
            }],
            successors: Vec::new(),
        },
    ];
    let mut right = left.clone();
    right.owner = 1;
    right.nodes[0].operations[0].code = 99;
    assert_eq!(
        canonical(&left, 0, 1, Some(1)),
        canonical(&right, 0, 1, Some(1))
    );
    let left = Body::try_from(Input::from(&left)).unwrap();
    let right = Body::try_from(Input::from(&right)).unwrap();
    with_matcher(|matcher| {
        let left_owner = left.owner;
        let left_id = matcher.register(left).unwrap();
        let right_id = matcher.register(right).unwrap();

        matcher
            .insert(
                left_id,
                matcher
                    .candidate(
                        left_id,
                        BasicBlock::from_usize(0),
                        1,
                        Some(BasicBlock::from_usize(1)),
                        DUMMY_SP,
                    )
                    .unwrap(),
            )
            .unwrap();
        match matcher
            .insert(
                right_id,
                matcher
                    .candidate(
                        right_id,
                        BasicBlock::from_usize(0),
                        1,
                        Some(BasicBlock::from_usize(1)),
                        DUMMY_SP,
                    )
                    .unwrap(),
            )
            .unwrap()
        {
            Some(original) => assert_eq!(original.owner, left_owner),
            None => panic!("a backedge must not re-include statements before the region"),
        }
    });
}

#[test]
fn nested_successful_regions_reuse_completed_pairs() {
    let depth = 1024;
    let nodes = (0..=depth)
        .map(|index| Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 0,
                local: Variable::First,
            }],
            successors: match index == depth {
                true => Vec::new(),
                false => vec![index + 1],
            },
        })
        .collect();
    let left = Model {
        owner: 0,
        nodes,
        types: [1, 1],
    };
    let mut right = left.clone();
    right.owner = 1;
    let left = Body::try_from(Input::from(&left)).unwrap();
    let right = Body::try_from(Input::from(&right)).unwrap();
    with_matcher(|matcher| {
        let left_owner = left.owner;
        let left_id = matcher.register(left).unwrap();
        let right_id = matcher.register(right).unwrap();

        for entry in 0..depth {
            match matcher
                .insert(
                    left_id,
                    matcher
                        .candidate(
                            left_id,
                            BasicBlock::from_usize(entry),
                            0,
                            Some(BasicBlock::from_usize(depth)),
                            DUMMY_SP,
                        )
                        .unwrap(),
                )
                .unwrap()
            {
                None => {}
                Some(_) => panic!("different region sizes are distinct"),
            }
        }
        assert_eq!(matcher.cache_entries().control_flow_pairs, 0);
        for entry in 0..depth {
            match matcher
                .insert(
                    right_id,
                    matcher
                        .candidate(
                            right_id,
                            BasicBlock::from_usize(entry),
                            0,
                            Some(BasicBlock::from_usize(depth)),
                            DUMMY_SP,
                        )
                        .unwrap(),
                )
                .unwrap()
            {
                Some(original) => assert_eq!(original.owner, left_owner),
                None => panic!("equivalent suffix region at {entry}"),
            }
            assert_eq!(matcher.cache_entries().control_flow_pairs, depth + 1);
        }
        assert_eq!(matcher.cache_entries().reachable_contexts, 2 * (depth + 1));
    });
}

#[test]
fn nested_late_mismatches_reuse_failed_pairs() {
    let depth = 1024;
    let nodes = (0..=depth)
        .map(|index| Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 0,
                local: Variable::First,
            }],
            successors: match index == depth {
                true => Vec::new(),
                false => vec![index + 1],
            },
        })
        .collect();
    let left = Model {
        owner: 0,
        nodes,
        types: [1, 1],
    };
    let mut right = left.clone();
    right.owner = 1;
    right.nodes[depth - 2].operations[0].local = Variable::Second;
    let left = Body::try_from(Input::from(&left)).unwrap();
    let right = Body::try_from(Input::from(&right)).unwrap();
    with_matcher(|matcher| {
        let left_id = matcher.register(left).unwrap();
        let right_id = matcher.register(right).unwrap();

        for entry in 0..depth - 1 {
            matcher
                .insert(
                    left_id,
                    matcher
                        .candidate(
                            left_id,
                            BasicBlock::from_usize(entry),
                            0,
                            Some(BasicBlock::from_usize(depth)),
                            DUMMY_SP,
                        )
                        .unwrap(),
                )
                .unwrap();
        }
        for entry in 0..depth - 1 {
            match matcher
                .insert(
                    right_id,
                    matcher
                        .candidate(
                            right_id,
                            BasicBlock::from_usize(entry),
                            0,
                            Some(BasicBlock::from_usize(depth)),
                            DUMMY_SP,
                        )
                        .unwrap(),
                )
                .unwrap()
            {
                None => {}
                Some(_) => panic!("late mismatch remains inside region {entry}"),
            }
            assert_eq!(matcher.cache_entries().control_flow_pairs, depth + 1);
        }
        assert_eq!(matcher.cache_entries().reachable_contexts, 2 * (depth + 1));
    });
}

#[hegel::test(print_blob = true)]
fn equivalent_registrations_keep_distinct_body_identities(tc: hegel::TestCase) {
    let steps = tc.draw(hegel::generators::default::<Vec<Step>>());
    let model = Model::from(steps);
    let left = Body::try_from(Input::from(&model)).unwrap();
    let right = Body::try_from(Input::from(&model)).unwrap();
    with_matcher(|matcher| {
        let left = matcher.register(left).unwrap();
        let right = matcher.register(right).unwrap();
        assert!(left != right);
        let left_candidate = matcher
            .candidate(left, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
            .unwrap();
        let right_candidate = matcher
            .candidate(right, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
            .unwrap();
        match matcher.insert(left, left_candidate).unwrap() {
            None => {}
            Some(_) => panic!("first candidate cannot match"),
        }
        let matched = matcher
            .insert(right, right_candidate)
            .unwrap()
            .expect("equivalent bodies match");
        assert_eq!(matched.owner.local_def_index.as_usize(), model.owner);
    });
}

#[test]
fn first_equivalent_source_candidate_remains_the_original() {
    let model = Model::from(Vec::new());
    let body = Body::try_from(Input::from(&model)).unwrap();
    let outer = DUMMY_SP.with_hi(BytePos(30)).with_lo(BytePos(1));
    let inner = DUMMY_SP.with_hi(BytePos(20)).with_lo(BytePos(10));
    with_matcher(|matcher| {
        let body_owner = body.owner;
        let body_id = matcher.register(body).unwrap();

        matcher
            .insert(
                body_id,
                matcher
                    .candidate(body_id, BasicBlock::from_usize(0), 0, None, outer)
                    .unwrap(),
            )
            .unwrap();
        let matched = matcher
            .insert(
                body_id,
                matcher
                    .candidate(body_id, BasicBlock::from_usize(0), 0, None, inner)
                    .unwrap(),
            )
            .unwrap()
            .expect("equivalent nested candidate");
        assert_eq!(matched.span, outer);
        let mut model = model;
        model.owner = 1;
        let other = Body::try_from(Input::from(&model)).unwrap();
        let other_id = matcher.register(other).unwrap();
        let matched = matcher
            .insert(
                other_id,
                matcher
                    .candidate(other_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                    .unwrap(),
            )
            .unwrap()
            .expect("equivalent other body");
        assert_eq!(matched.owner, body_owner);
        assert_eq!(matched.span, outer);
    });
}

#[test]
fn different_boundaries_do_not_reuse_an_incompatible_result() {
    let left = Model::from(Vec::new());
    let mut right = left.clone();
    right.owner = 1;
    let end = right.nodes.len() - 1;
    right.nodes[end].operations[0].code = 254;
    let left = Body::try_from(Input::from(&left)).unwrap();
    let right = Body::try_from(Input::from(&right)).unwrap();
    with_matcher(|matcher| {
        let left_owner = left.owner;
        let left_id = matcher.register(left).unwrap();
        let right_id = matcher.register(right).unwrap();

        matcher
            .insert(
                left_id,
                matcher
                    .candidate(left_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                    .unwrap(),
            )
            .unwrap();
        match matcher
            .insert(
                right_id,
                matcher
                    .candidate(right_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                    .unwrap(),
            )
            .unwrap()
        {
            None => {}
            Some(_) => panic!("whole regions differ at the final operation"),
        }
        matcher
            .insert(
                left_id,
                matcher
                    .candidate(
                        left_id,
                        BasicBlock::from_usize(0),
                        0,
                        Some(BasicBlock::from_usize(end)),
                        DUMMY_SP,
                    )
                    .unwrap(),
            )
            .unwrap();
        match matcher
            .insert(
                right_id,
                matcher
                    .candidate(
                        right_id,
                        BasicBlock::from_usize(0),
                        0,
                        Some(BasicBlock::from_usize(end)),
                        DUMMY_SP,
                    )
                    .unwrap(),
            )
            .unwrap()
        {
            Some(original) => assert_eq!(original.owner, left_owner),
            None => panic!("the differing continuation is outside both smaller regions"),
        }
    });
}

#[test]
fn a_relation_rejects_cross_block_local_alias_changes() {
    let mut left = Model::from(Vec::new());
    left.nodes = vec![
        Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 1,
                local: Variable::First,
            }],
            successors: vec![1],
        },
        Node {
            phase: Execution::Normal,
            operations: vec![Operation {
                code: 2,
                local: Variable::First,
            }],
            successors: Vec::new(),
        },
    ];
    let mut right = left.clone();
    right.owner = 1;
    right.nodes[1].operations[0].local = Variable::Second;
    let left = Body::try_from(Input::from(&left)).unwrap();
    let right = Body::try_from(Input::from(&right)).unwrap();
    with_matcher(|matcher| {
        let left_id = matcher.register(left).unwrap();
        let right_id = matcher.register(right).unwrap();

        matcher
            .insert(
                left_id,
                matcher
                    .candidate(left_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                    .unwrap(),
            )
            .unwrap();
        match matcher
            .insert(
                right_id,
                matcher
                    .candidate(right_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                    .unwrap(),
            )
            .unwrap()
        {
            None => {}
            Some(_) => panic!("one left local cannot correspond to two distinct right locals"),
        }
    });
}

#[test]
fn independent_functions_with_distinct_late_operations_do_not_compare_pairwise() {
    let functions = 64;
    let depth = 128;
    with_matcher(|matcher| {
        for owner in 0..functions {
            let mut nodes: Vec<_> = (0..depth)
                .map(|index| Node {
                    phase: Execution::Normal,
                    operations: vec![Operation {
                        code: 0,
                        local: Variable::First,
                    }],
                    successors: match index + 1 == depth {
                        true => Vec::new(),
                        false => vec![index + 1],
                    },
                })
                .collect();
            nodes[depth - 1].operations[0].code = u8::try_from(owner).unwrap();
            let model = Model {
                owner,
                nodes,
                types: [1, 1],
            };
            let body = Body::try_from(Input::from(&model)).unwrap();
            let body_id = matcher.register(body).unwrap();
            let candidate = matcher
                .candidate(body_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                .unwrap();
            match matcher.insert(body_id, candidate).unwrap() {
                None => {}
                Some(_) => panic!("each function has a distinct final operation"),
            }
        }
        let entries = matcher.cache_entries();
        assert_eq!(entries.control_flow_pairs, 0);
        assert_eq!(entries.reachable_contexts, functions * depth);
        assert!(entries.label_nodes <= functions * depth * (2 * u32::BITS as usize + 1));
    });
}

#[test]
fn independent_functions_with_distinct_local_types_do_not_compare_pairwise() {
    let functions = 64;
    let depth = 128;
    with_matcher(|matcher| {
        for owner in 0..functions {
            let nodes = (0..depth)
                .map(|index| Node {
                    phase: Execution::Normal,
                    operations: vec![Operation {
                        code: 0,
                        local: Variable::First,
                    }],
                    successors: match index + 1 == depth {
                        true => Vec::new(),
                        false => vec![index + 1],
                    },
                })
                .collect();
            let model = Model {
                owner,
                nodes,
                types: [u8::try_from(owner).unwrap(), 1],
            };
            let body = Body::try_from(Input::from(&model)).unwrap();
            let body_id = matcher.register(body).unwrap();
            let candidate = matcher
                .candidate(body_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                .unwrap();
            match matcher.insert(body_id, candidate).unwrap() {
                None => {}
                Some(_) => panic!("each function has a distinct local type"),
            }
        }
        let entries = matcher.cache_entries();
        assert_eq!(entries.control_flow_pairs, 0);
        assert_eq!(entries.reachable_contexts, functions * depth);
        assert!(entries.label_nodes <= functions * depth * (2 * u32::BITS as usize + 1));
    });
}

#[test]
fn same_label_alias_patterns_use_one_comparison_per_new_function() {
    let functions = 64usize;
    let depth = 128;
    with_matcher(|matcher| {
        let mut originals = Vec::new();
        for owner in 0..functions {
            let mut nodes: Vec<_> = (0..depth)
                .map(|index| Node {
                    phase: Execution::Normal,
                    operations: vec![Operation {
                        code: 0,
                        local: Variable::First,
                    }],
                    successors: match index + 1 == depth {
                        true => Vec::new(),
                        false => vec![index + 1],
                    },
                })
                .collect();
            for bit in 0..functions.ilog2() {
                nodes[depth - 1 - bit as usize].operations[0].local = match owner & (1 << bit) {
                    0 => Variable::First,
                    _ => Variable::Second,
                };
            }
            let model = Model {
                owner,
                nodes,
                types: [1, 1],
            };
            let body = Body::try_from(Input::from(&model)).unwrap();
            let body_id = matcher.register(body).unwrap();
            match matcher
                .insert(
                    body_id,
                    matcher
                        .candidate(body_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                        .unwrap(),
                )
                .unwrap()
            {
                None => {}
                Some(_) => panic!("distinct global alias patterns remain distinct"),
            }
            originals.push(model);
        }
        assert!(matcher.cache_entries().control_flow_pairs <= (functions - 1) * depth);
        for original in originals {
            let mut renamed = original.clone();
            renamed.owner += functions;
            for node in &mut renamed.nodes {
                node.operations[0].local = match node.operations[0].local {
                    Variable::First => Variable::Second,
                    Variable::Second => Variable::First,
                };
            }
            assert_eq!(
                canonical(&original, 0, 0, None),
                canonical(&renamed, 0, 0, None)
            );
            let body = Body::try_from(Input::from(&renamed)).unwrap();
            let body_id = matcher.register(body).unwrap();
            let matched = matcher
                .insert(
                    body_id,
                    matcher
                        .candidate(body_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                        .unwrap(),
                )
                .unwrap()
                .expect("renaming preserves the alias pattern");
            assert_eq!(matched.owner.local_def_index.index(), original.owner);
        }
    });
}

// shapelint: allow(literal-test-cases) These sizes form one cross-size matcher scaling gate.
#[test]
fn successive_late_shape_mismatches_bound_input_relative_work() {
    for bits in [8usize, 16, 32, 64] {
        let candidates = bits + 1;
        let input_discriminants = candidates * bits;
        with_matcher(|matcher| {
            for owner in 0..candidates {
                let nodes = (0..=bits)
                    .map(|index| Node {
                        phase: Execution::Normal,
                        operations: vec![Operation {
                            code: 0,
                            local: match index {
                                position if position < owner => Variable::Second,
                                _ => Variable::First,
                            },
                        }],
                        successors: match index == bits {
                            true => Vec::new(),
                            false => vec![index + 1],
                        },
                    })
                    .collect();
                let model = Model {
                    owner,
                    nodes,
                    types: [1, 1],
                };
                let body = Body::try_from(Input::from(&model)).unwrap();
                let body_id = matcher.register(body).unwrap();
                let None = matcher
                    .insert(
                        body_id,
                        matcher
                            .candidate(body_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                            .unwrap(),
                    )
                    .unwrap()
                else {
                    panic!("prefix shape {owner} must remain distinct")
                };
            }
            let entries = matcher.cache_entries();
            assert!(
                entries.maximum_decision_depth <= candidates,
                "decision depth must remain bounded by the one-vs-rest discriminant count at {bits}: {entries:?}"
            );
            assert!(
                entries.decision_steps <= input_discriminants,
                "candidate routing must remain linear in the generated body labels at {bits}: {entries:?}"
            );
        });
    }
}

#[test]
fn cyclic_alias_patterns_use_shared_concrete_witness_paths() {
    let functions = 16usize;
    let depth = 32;
    with_matcher(|matcher| {
        for owner in 0..functions {
            let mut nodes: Vec<_> = (0..depth)
                .map(|index| Node {
                    phase: Execution::Normal,
                    operations: vec![Operation {
                        code: 0,
                        local: Variable::First,
                    }],
                    successors: vec![(index + 1) % depth],
                })
                .collect();
            for bit in 0..functions.ilog2() {
                nodes[depth - 1 - bit as usize].operations[0].local = match owner & (1 << bit) {
                    0 => Variable::First,
                    _ => Variable::Second,
                };
            }
            let model = Model {
                owner,
                nodes,
                types: [1, 1],
            };
            let body = Body::try_from(Input::from(&model)).unwrap();
            let body_id = matcher.register(body).unwrap();
            match matcher
                .insert(
                    body_id,
                    matcher
                        .candidate(body_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                        .unwrap(),
                )
                .unwrap()
            {
                None => {}
                Some(_) => panic!("distinct cyclic alias patterns remain distinct"),
            }
        }
        assert!(matcher.cache_entries().control_flow_pairs <= (functions - 1) * depth);
    });
}

#[test]
fn same_label_cyclic_topologies_keep_distinct_classes_and_first_originals() {
    let functions = 4usize;
    with_matcher(|matcher| {
        let mut originals = Vec::new();
        for owner in 0..functions {
            let nodes = vec![
                Node {
                    phase: Execution::Normal,
                    operations: vec![Operation {
                        code: 0,
                        local: Variable::First,
                    }],
                    successors: vec![1, 2],
                },
                Node {
                    phase: Execution::Normal,
                    operations: vec![Operation {
                        code: 0,
                        local: Variable::First,
                    }],
                    successors: vec![3, 0],
                },
                Node {
                    phase: Execution::Normal,
                    operations: vec![Operation {
                        code: 0,
                        local: Variable::First,
                    }],
                    successors: vec![3, 0],
                },
                Node {
                    phase: Execution::Normal,
                    operations: vec![Operation {
                        code: 0,
                        local: Variable::First,
                    }],
                    successors: vec![0, owner],
                },
            ];
            let model = Model {
                owner,
                nodes,
                types: [1, 1],
            };
            let body = Body::try_from(Input::from(&model)).unwrap();
            let body_id = matcher.register(body).unwrap();
            match matcher
                .insert(
                    body_id,
                    matcher
                        .candidate(body_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                        .unwrap(),
                )
                .unwrap()
            {
                None => {}
                Some(_) => panic!("rooted ordered edges distinguish these topologies"),
            }
            originals.push(model);
        }
        assert!(
            matcher.cache_entries().control_flow_pairs <= (functions - 1) * functions * functions
        );
        for original in originals {
            let permutation = [0, 2, 1, 3];
            let mut renamed = original.clone();
            renamed.owner += functions;
            let nodes = original.nodes.iter().enumerate();
            for (index, node) in nodes {
                renamed.nodes[permutation[index]] = Node {
                    phase: node.phase,
                    operations: node.operations.clone(),
                    successors: node
                        .successors
                        .iter()
                        .map(|target| permutation[*target])
                        .collect(),
                };
            }
            assert_eq!(
                canonical(&original, 0, 0, None),
                canonical(&renamed, 0, 0, None)
            );
            let body = Body::try_from(Input::from(&renamed)).unwrap();
            let body_id = matcher.register(body).unwrap();
            let matched = matcher
                .insert(
                    body_id,
                    matcher
                        .candidate(body_id, BasicBlock::from_usize(0), 0, None, DUMMY_SP)
                        .unwrap(),
                )
                .unwrap()
                .expect("block renumbering preserves topology");
            assert_eq!(matched.owner.local_def_index.index(), original.owner);
        }
    });
}
