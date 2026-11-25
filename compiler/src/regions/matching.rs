mod routes;

use std::hash::Hash;
use std::marker::PhantomData;

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::graph::{DirectedGraph, Successors, scc::Sccs};
use rustc_data_structures::stable_hash::StableHasher;
use rustc_hir::def_id::LocalDefId;
use rustc_index::{Idx, IndexVec};
use rustc_middle::mir::{BasicBlock, Local};
use rustc_span::Span;

use crate::contracts::graph::CapacityError;
use crate::contracts::graph::sets::{self, Combination, SetId, Sets};
use crate::regions::Suffixes;
use crate::regions::matching::routes::{
    Context, Feature, Locator, Observation, Observations, Paths, Routes,
};
use crate::sequence::{Alignment, Mapper, PairedCache, PairedPart, Sequence, Sequences};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Capacity(#[from] CapacityError),
    #[error("region block {block:?} refers to missing block {target:?}")]
    MissingBlock {
        block: BasicBlock,
        target: BasicBlock,
    },
    #[error("region block {block:?} has no terminator description")]
    EmptyBlock { block: BasicBlock },
    #[error("region block {block:?} refers to local {local:?} without a type")]
    MissingType { block: BasicBlock, local: Local },
    #[error("region entry {block:?} at statement {start} is outside its body")]
    InvalidEntry { block: BasicBlock, start: usize },
    #[error("region boundary {block:?} is outside its body")]
    InvalidBoundary { block: BasicBlock },
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Phase {
    Execution,
    Cleanup,
}

pub struct Block {
    pub phase: Phase,
    pub suffixes: Suffixes,
    pub successors: Vec<BasicBlock>,
}

pub struct Input {
    pub owner: LocalDefId,
    pub coroutine: Fingerprint,
    pub blocks: Vec<Block>,
    pub types: FxHashMap<Local, Fingerprint>,
}

/// Owns normalized MIR descriptions independently of a compiler query borrow.
pub struct Body {
    pub owner: LocalDefId,
    coroutine: Fingerprint,
    blocks: Vec<Block>,
    types: FxHashMap<Local, Fingerprint>,
}

impl TryFrom<Input> for Body {
    type Error = Error;

    fn try_from(input: Input) -> Result<Self, Error> {
        let Input {
            owner,
            coroutine,
            blocks,
            types,
        } = input;
        let indexed_blocks = blocks.iter().enumerate();
        for (index, block) in indexed_blocks {
            let source = BasicBlock::from_usize(index);
            let Some(first) = block.suffixes.descriptions.first() else {
                return Err(Error::EmptyBlock { block: source });
            };
            for &target in &block.successors {
                if target.index() >= blocks.len() {
                    return Err(Error::MissingBlock {
                        block: source,
                        target,
                    });
                }
            }
            let locals = block.suffixes.bindings.iter(first.bindings);
            for &local in locals {
                if let None = types.get(&local) {
                    return Err(Error::MissingType {
                        block: source,
                        local,
                    });
                }
            }
        }
        Ok(Self {
            owner,
            coroutine,
            blocks,
            types,
        })
    }
}

impl Body {
    pub fn candidate(
        &self,
        entry: BasicBlock,
        start: usize,
        boundary: Option<BasicBlock>,
        span: Span,
    ) -> Result<Candidate, Error> {
        match self
            .blocks
            .get(entry.index())
            .and_then(|block| block.suffixes.descriptions.get(start))
        {
            Some(_) => {}
            None => {
                return Err(Error::InvalidEntry {
                    block: entry,
                    start,
                });
            }
        }
        if let Some(block) = boundary
            && block.index() >= self.blocks.len()
        {
            return Err(Error::InvalidBoundary { block });
        }
        let candidate = Candidate {
            entry,
            start,
            boundary,
            span,
        };
        Ok(candidate)
    }
}

#[derive(Clone, Copy)]
pub struct Candidate {
    pub span: Span,
    entry: BasicBlock,
    start: usize,
    boundary: Option<BasicBlock>,
}

rustc_index::newtype_index! {
    #[max = 0xffff_ffff]
    struct BodyKey {}
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct BodyId<'g> {
    key: BodyKey,
    brand: PhantomData<fn(&'g ()) -> &'g ()>,
}

#[derive(Clone, Copy)]
struct RegisteredCandidate {
    body: BodyKey,
    candidate: Candidate,
}

#[derive(Clone, Copy)]
pub struct Match {
    pub owner: LocalDefId,
    pub span: Span,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Binding {
    Block(BodyKey, BasicBlock),
    Local(BodyKey, Local),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct TypedLocal {
    binding: Binding,
    ty: Fingerprint,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct FrozenSuffix<'g> {
    fingerprint: Fingerprint,
    bindings: Sequence<'g, TypedLocal>,
    label: u128,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct FrozenBlock<'g> {
    phase: Phase,
    suffixes: Sequence<'g, FrozenSuffix<'g>>,
    successors: Sequence<'g, BasicBlock>,
    component: usize,
}

struct Registered<'g> {
    owner: LocalDefId,
    coroutine: Fingerprint,
    blocks: Sequence<'g, FrozenBlock<'g>>,
}

struct Frozen<'g> {
    blocks: Sequences<'g, FrozenBlock<'g>>,
    suffixes: Sequences<'g, FrozenSuffix<'g>>,
    successors: Sequences<'g, BasicBlock>,
}

struct FrozenEntry<'g> {
    block: FrozenBlock<'g>,
    suffix: FrozenSuffix<'g>,
}

impl<'g> Frozen<'g> {
    fn entry(
        &self,
        body: &Registered<'g>,
        entry: BasicBlock,
        start: usize,
        boundary: Option<BasicBlock>,
    ) -> Result<FrozenEntry<'g>, Error> {
        let invalid = Error::InvalidEntry {
            block: entry,
            start,
        };
        let Some(&block) = self.blocks.get(body.blocks, entry.index()) else {
            return Err(invalid);
        };
        let suffix = *self.suffixes.get(block.suffixes, start).ok_or(invalid)?;
        if let Some(block) = boundary
            && block.index() >= self.blocks.len(body.blocks)
        {
            return Err(Error::InvalidBoundary { block });
        }
        Ok(FrozenEntry { block, suffix })
    }
}

impl<'g> std::ops::Index<(Sequence<'g, FrozenBlock<'g>>, usize)> for Frozen<'g> {
    type Output = FrozenBlock<'g>;
    fn index(&self, (blocks, index): (Sequence<'g, FrozenBlock<'g>>, usize)) -> &Self::Output {
        self.blocks.get(blocks, index).expect("validated block")
    }
}
impl<'g> std::ops::Index<(Sequence<'g, FrozenSuffix<'g>>, usize)> for Frozen<'g> {
    type Output = FrozenSuffix<'g>;
    fn index(&self, (suffixes, index): (Sequence<'g, FrozenSuffix<'g>>, usize)) -> &Self::Output {
        self.suffixes
            .get(suffixes, index)
            .expect("validated suffix")
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Point {
    body: BodyKey,
    block: BasicBlock,
    start: usize,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Entry {
    block: BasicBlock,
    start: usize,
}

impl Entry {
    fn start_in(entry: Option<Self>, block: BasicBlock) -> usize {
        match entry {
            Some(entry) if entry.block == block => entry.start,
            _ => 0,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Query {
    left: Point,
    right: Point,
    left_boundary: Option<BasicBlock>,
    right_boundary: Option<BasicBlock>,
    left_entry: Option<Entry>,
    right_entry: Option<Entry>,
}

#[derive(Clone, Copy)]
struct Relation {
    pairs: SetId<'static, (Binding, Binding)>,
    left: SetId<'static, Binding>,
    right: SetId<'static, Binding>,
}
impl Relation {
    const EMPTY: Self = Self {
        pairs: SetId::EMPTY,
        left: SetId::EMPTY,
        right: SetId::EMPTY,
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Selector {
    Block,
    Local(usize),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Site {
    query: Query,
    selector: Selector,
}

type Pair = (Binding, Binding);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct SupportId(u32);

impl crate::arena::ArenaId for SupportId {
    fn from_index(index: u32) -> Self {
        Self(index)
    }
    fn index(self) -> u32 {
        self.0
    }
}

#[derive(Clone, Copy)]
struct Evidence {
    relation: Relation,
    support: Option<SupportId>,
}
impl Evidence {
    const EMPTY: Self = Self {
        relation: Relation::EMPTY,
        support: None,
    };
}

#[derive(Clone, Copy)]
enum Witness {
    Mismatch(Site),
    Alias {
        support: SupportId,
        first: Pair,
        second: Pair,
    },
}

#[derive(Clone, Copy)]
enum Proof {
    Different(Witness),
    Corresponding(Evidence),
}

#[derive(Clone, Copy)]
enum LocalResult {
    Different(usize),
    Corresponding(Evidence),
}

#[derive(Clone, Copy)]
struct LocalSummary {
    length: usize,
    result: LocalResult,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum SupportKind {
    Local(Pair),
    Concat(SupportId, SupportId, usize),
    At(Query, SupportId),
    Block(Query, Pair),
    Union(SupportId, SupportId),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Support {
    pairs: SetId<'static, Pair>,
    kind: SupportKind,
}

#[derive(Clone, Copy)]
enum Origin {
    Local(usize),
    Site(Site),
}

enum Correspondence {
    Bijective,
    Conflicting,
}

struct Relations {
    pairs: Sets<'static, Pair>,
    bindings: Sets<'static, Binding>,
    projections: FxHashMap<SetId<'static, Pair>, Relation>,
    supports: crate::arena::Intern<SupportId, Support>,
    origins: FxHashMap<(SupportId, Pair), Origin>,
}

impl Default for Relations {
    fn default() -> Self {
        Self {
            pairs: Sets::new(),
            bindings: Sets::new(),
            projections: FxHashMap::default(),
            supports: crate::arena::Intern::new(),
            origins: FxHashMap::default(),
        }
    }
}

impl Relations {
    fn pair(&mut self, left: Binding, right: Binding) -> Result<Relation, CapacityError> {
        let relation = Relation {
            pairs: self.pairs.insert(SetId::EMPTY, (left, right))?,
            left: self.bindings.insert(SetId::EMPTY, left)?,
            right: self.bindings.insert(SetId::EMPTY, right)?,
        };
        Ok(relation)
    }

    fn combine(&mut self, left: Relation, right: Relation) -> Result<Relation, CapacityError> {
        let relation = Relation {
            pairs: self
                .pairs
                .combine(Combination::Union, left.pairs, right.pairs)?,
            left: self
                .bindings
                .combine(Combination::Union, left.left, right.left)?,
            right: self
                .bindings
                .combine(Combination::Union, left.right, right.right)?,
        };
        Ok(relation)
    }

    fn correspondence(&self, relation: Relation) -> Correspondence {
        let pairs = self.pairs[relation.pairs].len;
        match (
            pairs == self.bindings[relation.left].len,
            pairs == self.bindings[relation.right].len,
        ) {
            (true, true) => Correspondence::Bijective,
            _ => Correspondence::Conflicting,
        }
    }

    fn projection(&mut self, root: SetId<'static, Pair>) -> Result<Relation, CapacityError> {
        enum Work {
            Visit(SetId<'static, Pair>),
            Build(SetId<'static, Pair>),
        }
        let mut pending = vec![Work::Visit(root)];
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(node) => {
                    if self.projections.contains_key(&node) {
                        continue;
                    }
                    match self.pairs[node].kind {
                        sets::NodeKind::Empty => {
                            self.projections.insert(node, Relation::EMPTY);
                        }
                        sets::NodeKind::Leaf((left, right)) => {
                            let relation = self.pair(left, right)?;
                            self.projections.insert(node, relation);
                        }
                        sets::NodeKind::Branch(left, right) => {
                            pending.push(Work::Build(node));
                            pending.push(Work::Visit(right));
                            pending.push(Work::Visit(left));
                        }
                    }
                }
                Work::Build(node) => {
                    let sets::NodeKind::Branch(left, right) = self.pairs[node].kind else {
                        unreachable!("only branches wait for projections");
                    };
                    let left = self.projections[&left];
                    let right = self.projections[&right];
                    let relation = self.combine(left, right)?;
                    self.projections.insert(node, relation);
                }
            }
        }
        Ok(self.projections[&root])
    }

    fn conflict(
        &mut self,
        mut left: SetId<'static, Pair>,
        mut right: SetId<'static, Pair>,
    ) -> Result<(Pair, Pair), CapacityError> {
        loop {
            match (self.pairs[left].kind, self.pairs[right].kind) {
                (sets::NodeKind::Empty, _) | (_, sets::NodeKind::Empty) => {
                    unreachable!("conflicting relations have nonempty pair sets");
                }
                (sets::NodeKind::Leaf(a), sets::NodeKind::Leaf(b)) => return Ok((a, b)),
                (sets::NodeKind::Branch(a, b), _) => {
                    left = match (a, b) {
                        (a, b) if a == SetId::EMPTY => b,
                        (a, b) if b == SetId::EMPTY => a,
                        (a, b) => {
                            let a_projection = self.projection(a)?;
                            let right_projection = self.projection(right)?;
                            let merged = self.combine(a_projection, right_projection)?;
                            match self.correspondence(merged) {
                                Correspondence::Conflicting => a,
                                Correspondence::Bijective => b,
                            }
                        }
                    };
                }
                (sets::NodeKind::Leaf(_), sets::NodeKind::Branch(a, b)) => {
                    right = match (a, b) {
                        (a, b) if a == SetId::EMPTY => b,
                        (a, b) if b == SetId::EMPTY => a,
                        (a, b) => {
                            let left_projection = self.projection(left)?;
                            let a_projection = self.projection(a)?;
                            let merged = self.combine(left_projection, a_projection)?;
                            match self.correspondence(merged) {
                                Correspondence::Conflicting => a,
                                Correspondence::Bijective => b,
                            }
                        }
                    };
                }
            }
        }
    }

    fn union(&mut self, left: Proof, right: Proof) -> Result<Proof, CapacityError> {
        let (left, right) = match (left, right) {
            (Proof::Different(witness), _) | (_, Proof::Different(witness)) => {
                return Ok(Proof::Different(witness));
            }
            (Proof::Corresponding(left), Proof::Corresponding(right)) => (left, right),
        };
        let relation = self.combine(left.relation, right.relation)?;
        let support = match (left.support, right.support) {
            (None, other) | (other, None) => other,
            (Some(a), Some(b)) => match (
                relation.pairs == left.relation.pairs,
                relation.pairs == right.relation.pairs,
            ) {
                (true, _) => Some(a),
                (_, true) => Some(b),
                (false, false) => {
                    let support = Support {
                        pairs: relation.pairs,
                        kind: SupportKind::Union(a, b),
                    };
                    Some(self.supports.intern(support, CapacityError::Values)?)
                }
            },
        };
        match self.correspondence(relation) {
            Correspondence::Bijective => Ok(Proof::Corresponding(Evidence { relation, support })),
            Correspondence::Conflicting => {
                let (first, second) = self.conflict(left.relation.pairs, right.relation.pairs)?;
                Ok(Proof::Different(Witness::Alias {
                    support: support.expect("conflict has support"),
                    first,
                    second,
                }))
            }
        }
    }

    fn supported(&self, relation: Relation, kind: SupportKind) -> Result<Evidence, CapacityError> {
        let support = Support {
            pairs: relation.pairs,
            kind,
        };
        Ok(Evidence {
            relation,
            support: Some(self.supports.intern(support, CapacityError::Values)?),
        })
    }

    fn local(
        &mut self,
        part: PairedPart<'_, TypedLocal, LocalSummary>,
    ) -> Result<LocalSummary, CapacityError> {
        let summary = match part {
            PairedPart::Leaf(left, right) => {
                let result = match left.ty == right.ty {
                    false => LocalResult::Different(0),
                    true => {
                        let relation = self.pair(left.binding, right.binding)?;
                        let evidence = self.supported(
                            relation,
                            SupportKind::Local((left.binding, right.binding)),
                        )?;
                        LocalResult::Corresponding(evidence)
                    }
                };
                LocalSummary { length: 1, result }
            }
            PairedPart::Branch(left, right) => {
                let result = match (left.result, right.result) {
                    (LocalResult::Different(index), _) => LocalResult::Different(index),
                    (_, LocalResult::Different(index)) => {
                        LocalResult::Different(left.length + index)
                    }
                    (LocalResult::Corresponding(a), LocalResult::Corresponding(b)) => {
                        let relation = self.combine(a.relation, b.relation)?;
                        let kind = SupportKind::Concat(
                            a.support.expect("left range"),
                            b.support.expect("right range"),
                            left.length,
                        );
                        LocalResult::Corresponding(self.supported(relation, kind)?)
                    }
                };
                LocalSummary {
                    length: left
                        .length
                        .checked_add(right.length)
                        .ok_or(CapacityError::Sequences)?,
                    result,
                }
            }
        };
        Ok(summary)
    }

    fn locate(&mut self, root: SupportId, pair: Pair) -> Result<Origin, CapacityError> {
        let mut pending = vec![(root, None)];
        while let Some((id, child)) = pending.pop() {
            if self.origins.contains_key(&(id, pair)) {
                continue;
            }
            let node = self.supports[id];
            let child = match child {
                Some(child) => child,
                None => {
                    let child = match node.kind {
                        SupportKind::Local(_) => {
                            self.origins.insert((id, pair), Origin::Local(0));
                            continue;
                        }
                        SupportKind::Block(query, _) => {
                            self.origins.insert(
                                (id, pair),
                                Origin::Site(Site {
                                    query,
                                    selector: Selector::Block,
                                }),
                            );
                            continue;
                        }
                        SupportKind::At(_, child) => child,
                        SupportKind::Concat(left, right, _) | SupportKind::Union(left, right) => {
                            let members = self.supports[left].pairs;
                            match self.pairs.contains(members, pair) {
                                Some(()) => left,
                                None => right,
                            }
                        }
                    };
                    pending.push((id, Some(child)));
                    pending.push((child, None));
                    continue;
                }
            };
            let origin = self.origins[&(child, pair)];
            let origin = match (node.kind, origin) {
                (SupportKind::At(query, _), Origin::Local(index)) => Origin::Site(Site {
                    query,
                    selector: Selector::Local(index),
                }),
                (SupportKind::Concat(left, _, offset), Origin::Local(index)) => {
                    Origin::Local(if child == left {
                        index
                    } else {
                        index.checked_add(offset).ok_or(CapacityError::Sequences)?
                    })
                }
                (SupportKind::Union(..), origin) => origin,
                _ => unreachable!("support origins follow their local and graph stages"),
            };
            self.origins.insert((id, pair), origin);
        }
        Ok(self.origins[&(root, pair)])
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Signature {
    Port(Fingerprint),
    Block {
        coroutine: Fingerprint,
        phase: Phase,
        suffix: Fingerprint,
        successors: usize,
        blocks: usize,
        labels: u128,
    },
}

struct Dependencies(Vec<Vec<usize>>);
impl DirectedGraph for Dependencies {
    type Node = usize;
    fn num_nodes(&self) -> usize {
        self.0.len()
    }
}
impl Successors for Dependencies {
    fn successors(&self, node: usize) -> impl Iterator<Item = usize> {
        self.0[node].iter().copied()
    }
}

/// Shares complete pair summaries, including the correspondence evidence needed
/// to distinguish aliases and shared control-flow targets.
pub struct Matcher<'g> {
    bodies: IndexVec<BodyKey, Registered<'g>>,
    originals: FxHashMap<Signature, DecisionId>,
    decisions: IndexVec<DecisionId, Decision>,
    routes: Routes,
    paths: Paths,
    observations: Observations,
    completed: Summaries<Query, Proof>,
    reached: Summaries<Reach, BlockSet>,
    reachable_blocks: Sets<'static, (BodyKey, BasicBlock)>,
    relations: Relations,
    paired: PairedCache<'g, TypedLocal, LocalSummary>,
    labels: Labels,
    local_sequences: crate::sequence::Sequences<'g, TypedLocal>,
    type_sequences: crate::sequence::Sequences<'g, Fingerprint>,
    frozen: Frozen<'g>,
    decision_steps: usize,
    maximum_decision_depth: usize,
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
struct DecisionId(usize);
impl Idx for DecisionId {
    fn new(index: usize) -> Self {
        Self(index)
    }
    fn index(self) -> usize {
        self.0
    }
}

enum Decision {
    Leaf(RegisteredCandidate),
    Branch {
        feature: Feature,
        outcomes: FxHashMap<Observation, DecisionId>,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CacheEntries {
    pub control_flow_pairs: usize,
    pub binding_pairs: usize,
    pub reachable_contexts: usize,
    pub label_nodes: usize,
    pub decision_steps: usize,
    pub maximum_decision_depth: usize,
    pub feature_reads: usize,
    pub feature_evaluations: usize,
    pub decision_nodes: usize,
}

pub fn with_matcher<R>(f: impl for<'g> FnOnce(&mut Matcher<'g>) -> R) -> R {
    let mut matcher = Matcher::new();
    f(&mut matcher)
}
impl<'g> Matcher<'g> {
    fn new() -> Self {
        Self {
            bodies: IndexVec::new(),
            originals: FxHashMap::default(),
            decisions: IndexVec::new(),
            routes: Routes::default(),
            paths: Paths::default(),
            observations: Observations::default(),
            completed: Summaries::default(),
            reached: Summaries::default(),
            reachable_blocks: Sets::new(),
            relations: Relations::default(),
            paired: PairedCache::default(),
            labels: Labels::default(),
            local_sequences: crate::sequence::Sequences::new(),
            type_sequences: crate::sequence::Sequences::new(),
            frozen: Frozen {
                blocks: Sequences::new(),
                suffixes: Sequences::new(),
                successors: Sequences::new(),
            },
            decision_steps: 0,
            maximum_decision_depth: 0,
        }
    }
    pub fn cache_entries(&self) -> CacheEntries {
        CacheEntries {
            control_flow_pairs: self.completed.completed.len(),
            binding_pairs: self.paired.len(),
            reachable_contexts: self.reached.completed.len(),
            label_nodes: self.labels.completed.len(),
            decision_steps: self.decision_steps,
            maximum_decision_depth: self.maximum_decision_depth,
            feature_reads: self.observations.reads,
            feature_evaluations: self.observations.evaluations,
            decision_nodes: self.decisions.len(),
        }
    }

    pub fn register(&mut self, body: Body) -> Result<BodyId<'g>, Error> {
        u32::try_from(self.bodies.len()).map_err(|_| CapacityError::Values)?;
        let key = self.bodies.next_index();
        let dependencies = Dependencies(
            body.blocks
                .iter()
                .map(|block| block.successors.iter().map(|block| block.index()).collect())
                .collect(),
        );
        let components: Sccs<usize, usize> = Sccs::new(&dependencies);
        let mut blocks = Vec::with_capacity(body.blocks.len());
        let indexed_blocks = body.blocks.iter().enumerate();
        for (index, block) in indexed_blocks {
            let mut locals = Mapper::new(|&local| TypedLocal {
                binding: Binding::Local(key, local),
                ty: body.types[&local],
            });
            let mut types = Mapper::new(|&local| body.types[&local]);
            let mut suffixes = Vec::with_capacity(block.suffixes.descriptions.len());
            for description in &block.suffixes.descriptions {
                let bindings = locals.map(
                    &block.suffixes.bindings,
                    &mut self.local_sequences,
                    description.bindings,
                )?;
                let types = types.map(
                    &block.suffixes.bindings,
                    &mut self.type_sequences,
                    description.bindings,
                )?;
                let mut hasher = StableHasher::new();
                (block.phase, description.fingerprint, block.successors.len()).hash(&mut hasher);
                types.hash(&mut hasher);
                let fingerprint: Fingerprint = hasher.finish();
                suffixes.push(FrozenSuffix {
                    fingerprint: description.fingerprint,
                    bindings,
                    label: u128::from_le_bytes(fingerprint.to_le_bytes()),
                });
            }
            blocks.push(FrozenBlock {
                phase: block.phase,
                suffixes: self.frozen.suffixes.from_iter(suffixes)?,
                successors: self
                    .frozen
                    .successors
                    .from_iter(block.successors.iter().copied())?,
                component: components.scc(index),
            });
        }
        let blocks = self.frozen.blocks.from_iter(blocks)?;
        self.bodies.push(Registered {
            owner: body.owner,
            coroutine: body.coroutine,
            blocks,
        });
        Ok(BodyId {
            key,
            brand: PhantomData,
        })
    }

    pub fn candidate(
        &self,
        body: BodyId<'g>,
        entry: BasicBlock,
        start: usize,
        boundary: Option<BasicBlock>,
        span: Span,
    ) -> Result<Candidate, Error> {
        let body = &self.bodies[body.key];
        self.frozen.entry(body, entry, start, boundary)?;
        Ok(Candidate {
            entry,
            start,
            boundary,
            span,
        })
    }

    pub fn insert(
        &mut self,
        body: BodyId<'g>,
        candidate: Candidate,
    ) -> Result<Option<Match>, Error> {
        let Candidate {
            span: _,
            entry,
            start,
            boundary,
        } = candidate;
        let right = Point {
            body: body.key,
            block: entry,
            start,
        };
        let registered = RegisteredCandidate {
            body: body.key,
            candidate,
        };
        let body = &self.bodies[body.key];
        let FrozenEntry { block, suffix } = self.frozen.entry(body, entry, start, boundary)?;
        let mut context = ReachContext {
            bodies: &self.bodies,
            sets: &mut self.reachable_blocks,
            frozen: &self.frozen,
        };
        let reach = Reach {
            body: right.body,
            block: entry,
            boundary,
        };
        let members = self.reached.solve(
            reach,
            SetId::EMPTY,
            &mut context,
            ReachContext::inspect,
            |context, left, right| context.sets.combine(Combination::Union, left, right),
        )?;
        let blocks = context.sets[members].len;
        let signature = match Some(entry) == boundary {
            true => Signature::Port(body.coroutine),
            false => {
                let labels =
                    self.labels
                        .sum(members, &self.reachable_blocks, &self.bodies, &self.frozen);
                let labels = labels
                    .wrapping_sub(self.frozen[(block.suffixes, 0)].label)
                    .wrapping_add(suffix.label);
                Signature::Block {
                    coroutine: body.coroutine,
                    phase: block.phase,
                    suffix: suffix.fingerprint,
                    successors: self.frozen.successors.len(block.successors),
                    blocks,
                    labels,
                }
            }
        };
        let right_context = Context {
            point: right,
            boundary,
            entry: match start {
                0 => None,
                start => Some(Entry {
                    block: entry,
                    start,
                }),
            },
        };
        let Some(&root) = self.originals.get(&signature) else {
            let index = self.decisions.push(Decision::Leaf(registered));
            self.originals.insert(signature, index);
            return Ok(None);
        };
        let mut index = root;
        let mut depth = 0usize;
        let original = loop {
            depth = depth.saturating_add(1);
            self.decision_steps = self.decision_steps.saturating_add(1);
            self.maximum_decision_depth = self.maximum_decision_depth.max(depth);
            let leaf = self.decisions.next_index();
            match &mut self.decisions[index] {
                Decision::Leaf(original) => break *original,
                Decision::Branch { feature, outcomes } => {
                    let observed = self.observations.read(
                        right_context,
                        *feature,
                        &self.bodies,
                        &self.paths,
                        &self.local_sequences,
                        &self.frozen,
                    )?;
                    match outcomes.entry(observed) {
                        std::collections::hash_map::Entry::Occupied(entry) => index = *entry.get(),
                        std::collections::hash_map::Entry::Vacant(entry) => {
                            entry.insert(leaf);
                            self.decisions.push(Decision::Leaf(registered));
                            return Ok(None);
                        }
                    }
                }
            }
        };
        let left = Point {
            body: original.body,
            block: original.candidate.entry,
            start: original.candidate.start,
        };
        let left_context = Context {
            point: left,
            boundary: original.candidate.boundary,
            entry: match original.candidate.start {
                0 => None,
                start => Some(Entry {
                    block: original.candidate.entry,
                    start,
                }),
            },
        };
        let query = Query {
            left,
            right,
            left_boundary: left_context.boundary,
            right_boundary: right_context.boundary,
            left_entry: left_context.entry,
            right_entry: right_context.entry,
        };
        let mut context = PairContext {
            bodies: &self.bodies,
            relations: &mut self.relations,
            paired: &mut self.paired,
            sequences: &self.local_sequences,
            frozen: &self.frozen,
        };
        let proof = self.completed.solve(
            query,
            Proof::Corresponding(Evidence::EMPTY),
            &mut context,
            PairContext::inspect,
            |context, left, right| context.relations.union(left, right),
        )?;
        let witness = match proof {
            Proof::Corresponding(_) => {
                return Ok(Some(Match {
                    owner: self.bodies[original.body].owner,
                    span: original.candidate.span,
                }));
            }
            Proof::Different(witness) => witness,
        };
        let feature = match witness {
            Witness::Mismatch(site) => {
                let path = self
                    .routes
                    .path(query, site.query, &self.completed, &mut self.paths)?;
                match site.selector {
                    Selector::Block => Feature::Shape(path),
                    Selector::Local(index) => Feature::Type { path, index },
                }
            }
            Witness::Alias {
                support,
                first,
                second,
            } => {
                let Origin::Site(first) = self.relations.locate(support, first)? else {
                    unreachable!("graph relation has query sites");
                };
                let Origin::Site(second) = self.relations.locate(support, second)? else {
                    unreachable!("graph relation has query sites");
                };
                let left_path =
                    self.routes
                        .path(query, first.query, &self.completed, &mut self.paths)?;
                let right_path =
                    self.routes
                        .path(query, second.query, &self.completed, &mut self.paths)?;
                Feature::Alias(
                    Locator {
                        path: left_path,
                        selector: first.selector,
                    },
                    Locator {
                        path: right_path,
                        selector: second.selector,
                    },
                )
            }
        };
        let a = self.observations.read(
            left_context,
            feature,
            &self.bodies,
            &self.paths,
            &self.local_sequences,
            &self.frozen,
        )?;
        let b = self.observations.read(
            right_context,
            feature,
            &self.bodies,
            &self.paths,
            &self.local_sequences,
            &self.frozen,
        )?;
        assert!(
            a != b,
            "exact mismatch witness distinguishes its source candidates"
        );
        let first = self.decisions.push(Decision::Leaf(original));
        let second = self.decisions.push(Decision::Leaf(registered));
        self.decisions[index] = Decision::Branch {
            feature,
            outcomes: FxHashMap::from_iter([(a, first), (b, second)]),
        };
        Ok(None)
    }
}

struct PairContext<'a, 'g> {
    bodies: &'a IndexVec<BodyKey, Registered<'g>>,
    relations: &'a mut Relations,
    paired: &'a mut PairedCache<'g, TypedLocal, LocalSummary>,
    sequences: &'a crate::sequence::Sequences<'g, TypedLocal>,
    frozen: &'a Frozen<'g>,
}

impl PairContext<'_, '_> {
    fn inspect(&mut self, query: Query) -> Result<(Proof, Vec<Query>), CapacityError> {
        let Query {
            left,
            right,
            left_boundary,
            right_boundary,
            left_entry,
            right_entry,
        } = query;
        let left_body = &self.bodies[left.body];
        let right_body = &self.bodies[right.body];
        if left_body.coroutine != right_body.coroutine {
            return Ok((
                Proof::Different(Witness::Mismatch(Site {
                    query,
                    selector: Selector::Block,
                })),
                Vec::new(),
            ));
        }
        match (
            Some(left.block) == left_boundary,
            Some(right.block) == right_boundary,
        ) {
            (true, true) => return Ok((Proof::Corresponding(Evidence::EMPTY), Vec::new())),
            (true, false) | (false, true) => {
                return Ok((
                    Proof::Different(Witness::Mismatch(Site {
                        query,
                        selector: Selector::Block,
                    })),
                    Vec::new(),
                ));
            }
            (false, false) => {}
        }
        let a = &self.frozen[(left_body.blocks, left.block.index())];
        let b = &self.frozen[(right_body.blocks, right.block.index())];
        if a.phase != b.phase
            || self.frozen[(a.suffixes, left.start)].fingerprint
                != self.frozen[(b.suffixes, right.start)].fingerprint
            || self.frozen.successors.len(a.successors) != self.frozen.successors.len(b.successors)
        {
            return Ok((
                Proof::Different(Witness::Mismatch(Site {
                    query,
                    selector: Selector::Block,
                })),
                Vec::new(),
            ));
        }
        let relations = &mut self.relations;
        let alignment = self.sequences.align(
            self.frozen[(a.suffixes, left.start)].bindings,
            self.frozen[(b.suffixes, right.start)].bindings,
        );
        let local = match alignment {
            Alignment::Aligned(pair) => {
                Alignment::Aligned(
                    self.paired
                        .fold(self.sequences, pair, None, |part| relations.local(part))?,
                )
            }
            Alignment::Empty => Alignment::Empty,
            Alignment::DifferentLengths => Alignment::DifferentLengths,
        };
        let local = match local {
            Alignment::Empty => Evidence::EMPTY,
            Alignment::DifferentLengths => {
                return Ok((
                    Proof::Different(Witness::Mismatch(Site {
                        query,
                        selector: Selector::Block,
                    })),
                    Vec::new(),
                ));
            }
            Alignment::Aligned(LocalSummary {
                result: LocalResult::Different(index),
                ..
            }) => {
                return Ok((
                    Proof::Different(Witness::Mismatch(Site {
                        query,
                        selector: Selector::Local(index),
                    })),
                    Vec::new(),
                ));
            }
            Alignment::Aligned(LocalSummary {
                result: LocalResult::Corresponding(evidence),
                ..
            }) => match evidence.support {
                Some(support) => {
                    relations.supported(evidence.relation, SupportKind::At(query, support))?
                }
                None => evidence,
            },
        };
        let pair = (
            Binding::Block(left.body, left.block),
            Binding::Block(right.body, right.block),
        );
        let relation = relations.pair(pair.0, pair.1)?;
        let block = relations.supported(relation, SupportKind::Block(query, pair))?;
        let proof = relations.union(Proof::Corresponding(block), Proof::Corresponding(local))?;
        let children = match proof {
            Proof::Different(_) => Vec::new(),
            Proof::Corresponding(_) => self
                .frozen
                .successors
                .iter(a.successors)
                .zip(self.frozen.successors.iter(b.successors))
                .map(|(&a, &b)| {
                    let left_entry = left_entry.filter(|entry| {
                        self.frozen[(left_body.blocks, entry.block.index())].component
                            == self.frozen[(left_body.blocks, a.index())].component
                    });
                    let right_entry = right_entry.filter(|entry| {
                        self.frozen[(right_body.blocks, entry.block.index())].component
                            == self.frozen[(right_body.blocks, b.index())].component
                    });
                    let left_start = Entry::start_in(left_entry, a);
                    let right_start = Entry::start_in(right_entry, b);
                    Query {
                        left: Point {
                            body: left.body,
                            block: a,
                            start: left_start,
                        },
                        right: Point {
                            body: right.body,
                            block: b,
                            start: right_start,
                        },
                        left_boundary,
                        right_boundary,
                        left_entry,
                        right_entry,
                    }
                })
                .collect(),
        };
        Ok((proof, children))
    }
}

type BlockSet = SetId<'static, (BodyKey, BasicBlock)>;

#[derive(Default)]
struct Labels {
    completed: FxHashMap<BlockSet, u128>,
}

impl Labels {
    fn sum<'g>(
        &mut self,
        root: BlockSet,
        sets: &Sets<'static, (BodyKey, BasicBlock)>,
        bodies: &IndexVec<BodyKey, Registered<'g>>,
        frozen: &Frozen<'g>,
    ) -> u128 {
        enum Work {
            Visit(BlockSet),
            Build(BlockSet),
        }
        let mut pending = vec![Work::Visit(root)];
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(node) => {
                    if self.completed.contains_key(&node) {
                        continue;
                    }
                    match sets[node].kind {
                        sets::NodeKind::Empty => {
                            self.completed.insert(node, 0);
                        }
                        sets::NodeKind::Leaf((body, block)) => {
                            let body = &bodies[body];
                            let label =
                                frozen[(frozen[(body.blocks, block.index())].suffixes, 0)].label;
                            self.completed.insert(node, label);
                        }
                        sets::NodeKind::Branch(left, right) => {
                            pending.push(Work::Build(node));
                            pending.push(Work::Visit(right));
                            pending.push(Work::Visit(left));
                        }
                    }
                }
                Work::Build(node) => {
                    let sets::NodeKind::Branch(left, right) = sets[node].kind else {
                        unreachable!("only branches wait for children");
                    };
                    let left = self.completed[&left];
                    let right = self.completed[&right];
                    self.completed.insert(node, left.wrapping_add(right));
                }
            }
        }
        self.completed[&root]
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Reach {
    body: BodyKey,
    block: BasicBlock,
    boundary: Option<BasicBlock>,
}

struct ReachContext<'a, 'g> {
    bodies: &'a IndexVec<BodyKey, Registered<'g>>,
    sets: &'a mut Sets<'static, (BodyKey, BasicBlock)>,
    frozen: &'a Frozen<'g>,
}

impl ReachContext<'_, '_> {
    fn inspect(&mut self, root: Reach) -> Result<(BlockSet, Vec<Reach>), CapacityError> {
        let Reach {
            body,
            block,
            boundary,
        } = root;
        if Some(block) == boundary {
            return Ok((SetId::EMPTY, Vec::new()));
        }
        let registered = &self.bodies[body];
        let members = self.sets.insert(SetId::EMPTY, (body, block))?;
        let children = self
            .frozen
            .successors
            .iter(self.frozen[(registered.blocks, block.index())].successors)
            .map(|&block| Reach {
                body,
                block,
                boundary,
            })
            .collect();
        Ok((members, children))
    }
}

rustc_index::newtype_index! {
    #[max = 0xffff_ffff]
    #[orderable]
    struct ComponentId {}
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct LocalComponent(usize);
impl Idx for LocalComponent {
    fn new(index: usize) -> Self {
        Self(index)
    }
    fn index(self) -> usize {
        self.0
    }
}

#[derive(Clone, Copy)]
struct Component<K> {
    hub: (K, Sequence<'static, K>),
    others: Sequence<'static, (K, Sequence<'static, K>)>,
}
struct Summaries<K, V> {
    completed: FxHashMap<K, V>,
    groups: FxHashMap<K, ComponentId>,
    components: IndexVec<ComponentId, Component<K>>,
    nodes: Sequences<'static, (K, Sequence<'static, K>)>,
    children: Sequences<'static, K>,
}
impl<K, V> Default for Summaries<K, V> {
    fn default() -> Self {
        Self {
            completed: FxHashMap::default(),
            groups: FxHashMap::default(),
            components: IndexVec::new(),
            nodes: Sequences::new(),
            children: Sequences::new(),
        }
    }
}

impl<K: Copy + Eq + Hash, V: Copy> Summaries<K, V> {
    fn solve<C>(
        &mut self,
        root: K,
        empty: V,
        context: &mut C,
        mut inspect: impl FnMut(&mut C, K) -> Result<(V, Vec<K>), CapacityError>,
        mut union: impl FnMut(&mut C, V, V) -> Result<V, CapacityError>,
    ) -> Result<V, CapacityError> {
        if let Some(proof) = self.completed.get(&root) {
            return Ok(*proof);
        }
        struct Node<K, V> {
            query: K,
            proof: V,
            children: Vec<K>,
        }
        let mut indices = FxHashMap::default();
        let mut nodes = Vec::new();
        let mut pending = vec![root];
        while let Some(query) = pending.pop() {
            if self.completed.contains_key(&query) || indices.contains_key(&query) {
                continue;
            }
            let index = nodes.len();
            indices.insert(query, index);
            let (proof, children) = inspect(context, query)?;
            pending.extend(children.iter().rev().copied());
            nodes.push(Node {
                query,
                proof,
                children,
            });
        }
        let graph = Dependencies(
            nodes
                .iter()
                .map(|node| {
                    node.children
                        .iter()
                        .filter_map(|child| indices.get(child).copied())
                        .collect()
                })
                .collect(),
        );
        let components: Sccs<usize, LocalComponent> = Sccs::new(&graph);
        let mut groups = IndexVec::from_fn_n(|_| None, components.num_sccs());
        let indexed_nodes = nodes.iter().enumerate();
        for (index, node) in indexed_nodes {
            let group = &mut groups[components.scc(index)];
            let children = self.children.from_iter(node.children.iter().copied())?;
            match group {
                Some((_, others)) => Vec::push(others, (node.query, children)),
                None => *group = Some(((node.query, children), Vec::new())),
            }
        }
        let mut identities = Vec::with_capacity(nodes.len());
        let mut frozen = Vec::with_capacity(groups.len());
        let new_components = (self.components.len()..).zip(groups.into_iter().flatten());
        for (index, (hub, others)) in new_components {
            let id =
                ComponentId::from_u32(u32::try_from(index).map_err(|_| CapacityError::Queries)?);
            identities.push((hub.0, id));
            identities.extend(others.iter().map(|(query, _)| (*query, id)));
            frozen.push(Component {
                hub,
                others: self.nodes.from_iter(others)?,
            });
        }
        let mut proofs = IndexVec::from_elem_n(empty, components.num_sccs());
        let indexed_nodes = nodes.iter().enumerate();
        for (index, node) in indexed_nodes {
            let component = components.scc(index);
            proofs[component] = union(context, proofs[component], node.proof)?;
            for child in &node.children {
                if let Some(proof) = self.completed.get(child) {
                    proofs[component] = union(context, proofs[component], *proof)?;
                }
            }
        }
        for component in components.all_sccs() {
            for &successor in components.successors(component) {
                proofs[component] = union(context, proofs[component], proofs[successor])?;
            }
        }
        self.groups.extend(identities);
        self.components.extend(frozen);
        let indexed_nodes = nodes.into_iter().enumerate();
        for (index, node) in indexed_nodes {
            self.completed
                .insert(node.query, proofs[components.scc(index)]);
        }
        Ok(self.completed[&root])
    }
}
