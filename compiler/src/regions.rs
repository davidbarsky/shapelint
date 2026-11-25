pub mod matching;
pub use matching::Candidate;

use crate::sequence::{Sequence, Sequences};
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_data_structures::graph::vec_graph::VecGraph;
use rustc_data_structures::graph::{
    DirectedGraph, Predecessors, StartNode, Successors, dominators,
};
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::LocalDefId;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Expr, ExprKind, LoopSource, MatchSource};
use rustc_index::IndexVec;
use rustc_middle::mir::visit::{MutVisitor, PlaceContext, TyContext};
use rustc_middle::mir::{
    BasicBlock, Body, Local, Location, RETURN_PLACE, START_BLOCK, Statement, Terminator,
    TerminatorKind,
};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeFoldable, TypeFolder, TypeSuperFoldable};
use rustc_span::Span;
use std::num::NonZeroU32;

#[derive(Clone, Copy)]
enum Control {
    Loop(Span),
    Branch(Span),
}

struct Controls<'tcx> {
    typeck: &'tcx ty::TypeckResults<'tcx>,
    regions: Vec<Control>,
    operations: usize,
}

impl<'hir> Visitor<'hir> for Controls<'_> {
    fn visit_expr(&mut self, expression: &'hir Expr<'hir>) {
        let span = expression.span;
        let before = match expression.kind {
            ExprKind::If(condition, yes, no) if !span.from_expansion() => {
                self.visit_expr(condition);
                let before = self.operations;
                self.visit_expr(yes);
                if let Some(no) = no {
                    self.visit_expr(no);
                }
                before
            }
            ExprKind::Match(value, arms, MatchSource::Normal | MatchSource::Postfix)
                if !span.from_expansion() =>
            {
                self.visit_expr(value);
                let before = self.operations;
                for arm in arms {
                    self.visit_arm(arm);
                }
                before
            }
            _ => {
                let before = self.operations;
                intravisit::walk_expr(self, expression);
                match expression.kind {
                    ExprKind::Loop(_, _, LoopSource::ForLoop, _) => {
                        self.regions.push(Control::Loop(span))
                    }
                    _ if span.from_expansion() => {}
                    ExprKind::Loop(..) => self.regions.push(Control::Loop(span)),
                    ExprKind::Call(callee, _)
                        if let ExprKind::Path(ref path) = callee.kind
                            && let Res::Def(DefKind::Ctor(..), _) =
                                self.typeck.qpath_res(path, callee.hir_id) => {}
                    // Count each source action once, including the expressions used to perform it.
                    ExprKind::Call(..)
                    | ExprKind::MethodCall(..)
                    | ExprKind::Assign(..)
                    | ExprKind::AssignOp(..) => self.operations = before.saturating_add(1),
                    _ => {}
                }
                return;
            }
        };
        const MIN_BRANCH_OPERATIONS: usize = 2;
        if (before..self.operations).len() >= MIN_BRANCH_OPERATIONS {
            self.regions.push(Control::Branch(span));
        }
    }
}

// A reverse view of normal execution edges supplies region boundaries. Fingerprinting still
// walks every edge in the MIR body, including cleanup and coroutine cancellation.
struct Exits {
    edges: VecGraph<BasicBlock, true>,
    exit: BasicBlock,
}

impl DirectedGraph for Exits {
    type Node = BasicBlock;
    fn num_nodes(&self) -> usize {
        self.edges.num_nodes()
    }
}
impl StartNode for Exits {
    fn start_node(&self) -> BasicBlock {
        self.exit
    }
}
impl Successors for Exits {
    fn successors(&self, node: BasicBlock) -> impl Iterator<Item = BasicBlock> {
        self.edges.successors(node).iter().copied()
    }
}
impl Predecessors for Exits {
    fn predecessors(&self, node: BasicBlock) -> impl Iterator<Item = BasicBlock> {
        self.edges.predecessors(node).iter().copied()
    }
}

// A prefix minimum over high endpoints answers span-containment queries after the
// low endpoints have been swept in descending order. Minima retain input order.
fn first_contained(points: &[Span], queries: &[Span]) -> Vec<Option<usize>> {
    let mut order: Vec<_> = points.iter().copied().enumerate().collect();
    order.sort_unstable_by_key(|(_, span)| std::cmp::Reverse(span.lo()));
    let mut order = order.into_iter().peekable();
    let mut highs: Vec<_> = points.iter().map(|span| span.hi()).collect();
    highs.sort_unstable();
    highs.dedup();
    let mut minima = vec![points.len(); highs.len()];
    let mut entries = vec![None; queries.len()];
    let mut queries: Vec<_> = queries.iter().zip(&mut entries).collect();
    queries.sort_unstable_by_key(|(span, _)| std::cmp::Reverse(span.lo()));
    for (span, entry) in queries {
        while let Some((rank, point)) = order.next_if(|(_, point)| point.lo() >= span.lo()) {
            let mut position = highs.partition_point(|&high| high < point.hi());
            while let Some(minimum) = minima.get_mut(position) {
                *minimum = (*minimum).min(rank);
                let Some(next) = position.checked_add(1) else {
                    break;
                };
                position |= next;
            }
        }
        let end = highs.partition_point(|&high| high <= span.hi());
        let (mut prefix, _) = minima.split_at(end);
        let mut rank = points.len();
        while let Some((minimum, previous)) = prefix.split_last() {
            rank = rank.min(*minimum);
            (prefix, _) = previous.split_at(prefix.len() & previous.len());
        }
        *entry = (rank < points.len()).then_some(rank);
    }
    entries
}

fn control_entries(
    body: &Body<'_>,
    order: &[BasicBlock],
    headers: &FxHashMap<BasicBlock, Vec<BasicBlock>>,
    controls: &[Control],
) -> Vec<Option<BasicBlock>> {
    let mut loops = Vec::new();
    let mut branches = Vec::new();
    for &block in order {
        if headers.contains_key(&block) {
            loops.push(block);
        }
        if let TerminatorKind::SwitchInt { .. } = body.basic_blocks[block].terminator().kind {
            branches.push(block);
        }
    }
    let spans: Vec<_> = controls
        .iter()
        .map(|control| {
            let (Control::Loop(span) | Control::Branch(span)) = control;
            *span
        })
        .collect();
    let loop_spans: Vec<_> = loops
        .iter()
        .map(|block| body.basic_blocks[*block].terminator().source_info.span)
        .collect();
    let branch_spans: Vec<_> = branches
        .iter()
        .map(|block| body.basic_blocks[*block].terminator().source_info.span)
        .collect();
    let loop_entries = first_contained(&loop_spans, &spans);
    let branch_entries = first_contained(&branch_spans, &spans);
    controls
        .iter()
        .enumerate()
        .map(|(index, control)| match control {
            Control::Loop(_) => loop_entries[index].map(|rank| loops[rank]),
            Control::Branch(_) => branch_entries[index].map(|rank| branches[rank]),
        })
        .collect()
}

struct SpanAncestors {
    jumps: IndexVec<BasicBlock, Vec<(BasicBlock, Span)>>,
}

impl SpanAncestors {
    fn new(
        body: &Body<'_>,
        order: &[BasicBlock],
        dominators: &dominators::Dominators<BasicBlock>,
    ) -> Self {
        let mut jumps = IndexVec::<BasicBlock, Vec<(BasicBlock, Span)>>::from_elem_n(
            Vec::new(),
            body.basic_blocks.len(),
        );
        for &block in order {
            let Some(parent) = dominators.immediate_dominator(block) else {
                continue;
            };
            let mut target = parent;
            let mut span = body.basic_blocks[parent].terminator().source_info.span;
            jumps[block].push((target, span));
            for level in 0.. {
                let Some(&(ancestor, ancestor_span)) = jumps[target].get(level) else {
                    break;
                };
                span = span
                    .with_lo(span.lo().min(ancestor_span.lo()))
                    .with_hi(span.hi().max(ancestor_span.hi()));
                target = ancestor;
                jumps[block].push((target, span));
            }
        }
        Self { jumps }
    }

    fn entry(&self, mut block: BasicBlock, span: Span) -> BasicBlock {
        for level in (0..self.jumps[block].len()).rev() {
            if let Some(&(ancestor, extent)) = self.jumps[block].get(level)
                && span.contains(extent)
            {
                block = ancestor;
            }
        }
        block
    }
}

rustc_index::newtype_index! {
    #[max = 0xffff_ffff]
    struct BindingId {}
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum SplitBit {
    Low(NonZeroU32),
    High(NonZeroU32),
}

impl SplitBit {
    fn between(left: usize, right: usize) -> Option<Self> {
        let differing = (left ^ right) as u64;
        if let Some(high) = NonZeroU32::new((differing >> u32::BITS) as u32) {
            return Some(Self::High(high.isolate_highest_one()));
        }
        NonZeroU32::new(differing as u32).map(|low| Self::Low(low.isolate_highest_one()))
    }

    fn select<T>(self, position: usize, left: T, right: T) -> T {
        let masked = match self {
            Self::Low(mask) => position as u32 & mask.get(),
            Self::High(mask) => ((position as u64 >> u32::BITS) as u32) & mask.get(),
        };
        if masked == 0 { left } else { right }
    }

    fn branch(self, left: BindingId, right: BindingId) -> Binding {
        match self {
            Self::Low(mask) => Binding::Low { mask, left, right },
            Self::High(mask) => Binding::High { mask, left, right },
        }
    }
}

#[derive(Clone, Copy)]
enum Binding {
    Local {
        position: usize,
        local: Local,
    },
    Low {
        mask: NonZeroU32,
        left: BindingId,
        right: BindingId,
    },
    High {
        mask: NonZeroU32,
        left: BindingId,
        right: BindingId,
    },
}

struct BindingPath {
    leaf: BindingId,
    position: usize,
    branches: Vec<BindingStep>,
}

struct BindingStep {
    id: BindingId,
    bit: SplitBit,
    left: BindingId,
    right: BindingId,
}

#[derive(Default)]
struct Bindings(IndexVec<BindingId, Binding>);

impl Bindings {
    fn push(&mut self, node: Binding) -> Result<BindingId, crate::contracts::graph::CapacityError> {
        u32::try_from(self.0.len())
            .map_err(|_| crate::contracts::graph::CapacityError::Sequences)?;
        Ok(self.0.push(node))
    }

    // Patricia branches descend through distinct bits, bounding path copying by usize::BITS.
    fn path(&self, root: BindingId, position: usize) -> BindingPath {
        let mut cursor = root;
        let mut path = Vec::new();
        loop {
            let (bit, left, right) = match self.0[cursor] {
                Binding::Local { position, .. } => {
                    return BindingPath {
                        leaf: cursor,
                        position,
                        branches: path,
                    };
                }
                Binding::Low { mask, left, right } => (SplitBit::Low(mask), left, right),
                Binding::High { mask, left, right } => (SplitBit::High(mask), left, right),
            };
            path.push(BindingStep {
                id: cursor,
                bit,
                left,
                right,
            });
            cursor = bit.select(position, left, right);
        }
    }

    fn insert(
        &mut self,
        root: Option<BindingId>,
        position: usize,
        local: Local,
    ) -> Result<BindingId, crate::contracts::graph::CapacityError> {
        let leaf = self.push(Binding::Local { position, local })?;
        let Some(root) = root else { return Ok(leaf) };
        let BindingPath {
            leaf: mut cursor,
            position: found,
            branches: mut path,
        } = self.path(root, position);
        let mut result = leaf;
        if let Some(bit) = SplitBit::between(found, position) {
            while let Some(parent) = path.last() {
                if parent.bit > bit {
                    break;
                }
                cursor = parent.id;
                path.pop();
            }
            let (left, right) = bit.select(position, (leaf, cursor), (cursor, leaf));
            result = self.push(bit.branch(left, right))?;
        }
        self.rebuild(result, position, path)
    }

    fn remove(
        &mut self,
        root: BindingId,
        position: usize,
    ) -> Result<Option<BindingId>, crate::contracts::graph::CapacityError> {
        let BindingPath {
            position: found,
            branches: mut path,
            ..
        } = self.path(root, position);
        assert_eq!(
            found, position,
            "only the current first occurrence is removed"
        );
        let Some(BindingStep {
            bit, left, right, ..
        }) = path.pop()
        else {
            return Ok(None);
        };
        let sibling = bit.select(position, right, left);
        self.rebuild(sibling, position, path).map(Some)
    }

    fn rebuild(
        &mut self,
        mut result: BindingId,
        position: usize,
        path: Vec<BindingStep>,
    ) -> Result<BindingId, crate::contracts::graph::CapacityError> {
        let ancestors = path.into_iter().rev();
        for BindingStep {
            bit, left, right, ..
        } in ancestors
        {
            let (left, right) = bit.select(position, (result, right), (left, result));
            result = self.push(bit.branch(left, right))?;
        }
        Ok(result)
    }
}

pub struct Captured {
    pub body: matching::Body,
    pub candidates: Vec<matching::Candidate>,
}

pub struct Atom {
    pub fingerprint: Fingerprint,
    pub locals: Vec<Local>,
}

pub struct Description {
    pub fingerprint: Fingerprint,
    bindings: Sequence<'static, Local>,
}

/// Preserves alpha-equivalence and first-use bindings for nonempty atom-aligned suffixes.
pub struct Suffixes {
    descriptions: Vec<Description>,
    bindings: Sequences<'static, Local>,
}

impl TryFrom<Vec<Atom>> for Suffixes {
    type Error = crate::contracts::graph::CapacityError;
    fn try_from(parts: Vec<Atom>) -> Result<Self, Self::Error> {
        use std::hash::Hash;

        let mut descriptions = Vec::with_capacity(parts.len());
        let mut bindings = Bindings::default();
        let mut active: Option<(BindingId, FxHashMap<Local, usize>)> = None;
        let count = parts
            .iter()
            .try_fold(0usize, |count, part| count.checked_add(part.locals.len()))
            .ok_or(crate::contracts::graph::CapacityError::Sequences)?;
        let mut positions = (0..count).rev();
        let mut tail: Option<Fingerprint> = None;
        let parts = parts.into_iter().rev();
        for Atom {
            fingerprint,
            locals,
        } in parts
        {
            let mut distances = Vec::with_capacity(locals.len());
            let occurrences = locals.into_iter().rev().zip(&mut positions);
            for (local, position) in occurrences {
                let distance = match &mut active {
                    Some((root, next)) => {
                        let (remaining, distance) = match next.insert(local, position) {
                            Some(following) => (
                                bindings.remove(*root, following)?,
                                following
                                    .checked_sub(position)
                                    .ok_or(crate::contracts::graph::CapacityError::Sequences)?,
                            ),
                            None => (Some(*root), 0),
                        };
                        *root = bindings.insert(remaining, position, local)?;
                        distance
                    }
                    None => {
                        active = Some((
                            bindings.insert(None, position, local)?,
                            FxHashMap::from_iter([(local, position)]),
                        ));
                        0
                    }
                };
                distances.push(distance);
            }
            distances.reverse();
            let mut hasher = StableHasher::new();
            fingerprint.hash(&mut hasher);
            distances.hash(&mut hasher);
            tail.hash(&mut hasher);
            let fingerprint = hasher.finish();
            descriptions.push((fingerprint, active.as_ref().map(|(root, _)| *root)));
            tail = Some(fingerprint);
        }
        descriptions.reverse();
        let mut arena = Sequences::new();
        let mut sequences =
            IndexVec::<BindingId, Sequence<'static, Local>>::with_capacity(bindings.0.len());
        for binding in bindings.0 {
            let sequence = match binding {
                Binding::Local { local, .. } => arena.push(Sequence::EMPTY, local)?,
                Binding::Low { left, right, .. } | Binding::High { left, right, .. } => {
                    arena.append(sequences[left], sequences[right])?
                }
            };
            sequences.push(sequence);
        }
        let descriptions = descriptions
            .into_iter()
            .map(|(fingerprint, bindings)| Description {
                fingerprint,
                bindings: bindings.map(|root| sequences[root]).unwrap_or_default(),
            })
            .collect();
        Ok(Self {
            descriptions,
            bindings: arena,
        })
    }
}

impl Suffixes {
    // shapelint: allow(shallow-helper) The iterator pairs a suffix with its private source arena.
    pub fn bindings(&self, start: usize) -> impl DoubleEndedIterator<Item = Local> {
        self.bindings
            .iter(self.descriptions[start].bindings)
            .copied()
    }
}

impl std::ops::Index<usize> for Suffixes {
    type Output = Description;

    fn index(&self, start: usize) -> &Self::Output {
        &self.descriptions[start]
    }
}

struct BlockDescription {
    suffixes: Suffixes,
    successors: Vec<BasicBlock>,
}

enum Part<'a, 'tcx> {
    Statement(&'a mut Statement<'tcx>),
    Terminator(&'a mut Terminator<'tcx>),
}

struct Descriptions<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    body: &'a Body<'tcx>,
    types: FxHashMap<Local, Fingerprint>,
}

impl<'tcx> Descriptions<'_, 'tcx> {
    fn block(
        &mut self,
        block: BasicBlock,
    ) -> Result<BlockDescription, crate::contracts::graph::CapacityError> {
        let mut normalize = Normalize {
            tcx: self.tcx,
            locals: FxHashMap::default(),
            order: Vec::new(),
            body: self.body,
        };
        let mut data = self.body.basic_blocks[block].clone();
        let terminator = data
            .terminator
            .as_mut()
            .expect("MIR block has a terminator");
        let successors = terminator.successors().collect();
        let mut target = 0;
        terminator.successors_mut(|block| {
            *block = BasicBlock::from_usize(target);
            target += 1;
        });
        let mut parts = Vec::new();
        let statements = data
            .statements
            .iter_mut()
            .map(Part::Statement)
            .chain(std::iter::once(Part::Terminator(terminator)))
            .enumerate();
        for (statement_index, mut part) in statements {
            let location = Location {
                block,
                statement_index,
            };
            match &mut part {
                Part::Statement(statement) => normalize.visit_statement(statement, location),
                Part::Terminator(terminator) => normalize.visit_terminator(terminator, location),
            }
            let fingerprint = self.tcx.with_stable_hashing_context(|mut context| {
                let mut hasher = StableHasher::new();
                context.while_hashing_spans(false, |context| match part {
                    Part::Statement(statement) => statement.kind.stable_hash(context, &mut hasher),
                    Part::Terminator(terminator) => {
                        terminator.kind.stable_hash(context, &mut hasher);
                        if let TerminatorKind::Return = terminator.kind {
                            normalize.locals[&RETURN_PLACE].stable_hash(context, &mut hasher);
                        }
                    }
                });
                hasher.finish()
            });
            let locals = std::mem::take(&mut normalize.order);
            for &local in &locals {
                self.types.entry(local).or_insert_with(|| {
                    let ty = self.body.local_decls[local].ty.fold_with(&mut normalize);
                    let ty = self.tcx.erase_and_anonymize_regions(ty);
                    self.tcx.with_stable_hashing_context(|mut context| {
                        let mut hasher = StableHasher::new();
                        context.while_hashing_spans(false, |context| {
                            ty.stable_hash(context, &mut hasher);
                        });
                        hasher.finish()
                    })
                });
            }
            normalize.locals.clear();
            parts.push(Atom {
                fingerprint,
                locals,
            });
        }
        Ok(BlockDescription {
            suffixes: Suffixes::try_from(parts)?,
            successors,
        })
    }
}

pub fn candidates<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    body: &Body<'tcx>,
) -> Result<Option<Captured>, matching::Error> {
    let next_block = body.basic_blocks.len();
    // VecGraph stores forward and reverse node tables followed by a terminal BasicBlock index.
    if next_block >= BasicBlock::MAX_AS_U32 as usize / 2 {
        return Err(crate::contracts::graph::CapacityError::Queries.into());
    }
    let exit = BasicBlock::from_usize(next_block);
    let Some(hir) = tcx.hir_maybe_body_owned_by(def) else {
        return Ok(None);
    };
    let root = tcx.typeck_root_def_id(def.to_def_id());
    let mut controls = Controls {
        typeck: tcx.typeck(root.expect_local()),
        regions: Vec::new(),
        operations: 0,
    };
    controls.visit_body(hir);
    controls.regions.retain(|control| {
        let (Control::Loop(span) | Control::Branch(span)) = control;
        match crate::diagnostics::source_span(tcx, def.to_def_id(), *span) {
            Some(_) => true,
            None => false,
        }
    });
    if controls.regions.is_empty() {
        return Ok(None);
    }
    let order = rustc_middle::mir::traversal::preorder(body)
        .map(|(block, _)| block)
        .collect::<Vec<_>>();
    let dominators = body.basic_blocks.dominators();
    let mut headers: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
    let mut edges = Vec::new();
    for block in &order {
        let data = &body.basic_blocks[*block];
        let mut normal = data
            .terminator()
            .successors()
            .filter(|target| {
                if body.basic_blocks[*target].is_cleanup {
                    return false;
                }
                match data.terminator().kind {
                    TerminatorKind::Yield {
                        drop: Some(drop), ..
                    }
                    | TerminatorKind::Drop {
                        drop: Some(drop), ..
                    } => *target != drop,
                    _ => true,
                }
            })
            .peekable();
        if let None = normal.peek() {
            edges.push((exit, *block));
        }
        for target in normal {
            edges.push((target, *block));
            if dominators.dominates(target, *block) {
                headers.entry(target).or_default().push(*block);
            }
        }
    }
    let count = exit.as_u32() as usize + 1;
    let exits = Exits {
        edges: VecGraph::new(count, edges),
        exit,
    };
    let postdominators = dominators::dominators(&exits);
    let mut regions = Vec::new();
    if !headers.is_empty()
        && let Some(_) = controls.regions.iter().find(|control| match control {
            Control::Loop(_) => true,
            Control::Branch(_) => false,
        })
    {
        regions.push((START_BLOCK, 0, None, body.span));
    }
    let entries = control_entries(body, &order, &headers, &controls.regions);
    let ancestors = SpanAncestors::new(body, &order, dominators);
    let loops = crate::loops::Forest::new(&body.basic_blocks, dominators, &order, &headers);
    let boundaries = crate::loops::Exits::new(&loops, &postdominators, count);
    let mut selected = Vec::new();
    let controls = controls.regions.into_iter().zip(entries);
    for (control, block) in controls {
        let span = match control {
            Control::Loop(span) | Control::Branch(span) => span,
        };
        let Some(block) = block else {
            continue;
        };
        let boundary = match control {
            Control::Branch(_) => postdominators.immediate_dominator(block),
            Control::Loop(_) => boundaries.boundary(&loops, block),
        };
        let boundary = boundary.filter(|target| *target != exit);
        let entry = ancestors.entry(block, span);
        selected.push((entry, 0, boundary, span));
    }
    let mut by_entry: FxHashMap<BasicBlock, Vec<(Span, &mut usize)>> = FxHashMap::default();
    for (entry, start, _, span) in &mut selected {
        by_entry.entry(*entry).or_default().push((*span, start));
    }
    for (entry, selected) in by_entry {
        let points: Vec<_> = body.basic_blocks[entry]
            .statements
            .iter()
            .map(|statement| statement.source_info.span)
            .collect();
        let queries: Vec<_> = selected.iter().map(|(span, _)| *span).collect();
        let matches = selected.into_iter().zip(first_contained(&points, &queries));
        for ((_, destination), start) in matches {
            *destination = start.unwrap_or(points.len());
        }
    }
    regions.extend(selected);
    let mut seen = FxHashSet::default();
    regions.retain(|&(entry, start, boundary, _)| seen.insert((entry, start, boundary)));
    if regions.is_empty() {
        return Ok(None);
    }
    let mut descriptions = Descriptions {
        tcx,
        body,
        types: FxHashMap::default(),
    };
    let mut blocks = Vec::with_capacity(body.basic_blocks.len());
    for (block, data) in body.basic_blocks.iter_enumerated() {
        let BlockDescription {
            suffixes,
            successors,
        } = descriptions.block(block)?;
        let phase = match data.is_cleanup {
            true => matching::Phase::Cleanup,
            false => matching::Phase::Execution,
        };
        blocks.push(matching::Block {
            phase,
            suffixes,
            successors,
        });
    }
    let coroutine = tcx.with_stable_hashing_context(|mut context| {
        let mut hasher = StableHasher::new();
        context.while_hashing_spans(false, |context| {
            tcx.coroutine_kind(def).stable_hash(context, &mut hasher)
        });
        hasher.finish()
    });
    let normalized = matching::Body::try_from(matching::Input {
        owner: def,
        coroutine,
        blocks,
        types: descriptions.types,
    })?;
    let candidates = regions
        .into_iter()
        .map(|(entry, start, boundary, span)| normalized.candidate(entry, start, boundary, span))
        .collect::<Result<_, _>>()?;
    Ok(Some(Captured {
        body: normalized,
        candidates,
    }))
}

struct Normalize<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    locals: FxHashMap<Local, Local>,
    order: Vec<Local>,
    body: &'a Body<'tcx>,
}

impl<'tcx> Normalize<'_, 'tcx> {
    fn local(&mut self, local: Local) -> Local {
        if let Some(number) = self.locals.get(&local) {
            return *number;
        }
        let number = Local::from_usize(self.locals.len());
        self.order.push(local);
        self.locals.insert(local, number);
        number
    }
}

impl<'tcx> TypeFolder<TyCtxt<'tcx>> for Normalize<'_, 'tcx> {
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_ty(&mut self, ty: Ty<'tcx>) -> Ty<'tcx> {
        match *ty.kind() {
            // The body's own coroutine identity contains its function name. Compare its captured
            // field types instead; other coroutine and closure identities remain significant.
            ty::Coroutine(def, args) if def == self.body.source.def_id() => {
                args.as_coroutine().tupled_upvars_ty().fold_with(self)
            }
            _ => ty.super_fold_with(self),
        }
    }
}

impl<'tcx> MutVisitor<'tcx> for Normalize<'_, 'tcx> {
    fn visit_terminator(&mut self, terminator: &mut Terminator<'tcx>, location: Location) {
        match terminator.kind {
            TerminatorKind::Return => {
                self.local(RETURN_PLACE);
            }
            _ => self.super_terminator(terminator, location),
        }
    }

    fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_local(&mut self, local: &mut Local, _: PlaceContext, _: Location) {
        *local = self.local(*local);
    }

    fn visit_ty(&mut self, ty: &mut Ty<'tcx>, _: TyContext) {
        *ty = self.tcx.erase_and_anonymize_regions(ty.fold_with(self));
    }

    fn visit_args(&mut self, args: &mut ty::GenericArgsRef<'tcx>, _: Location) {
        *args = self.tcx.erase_and_anonymize_regions(args.fold_with(self));
    }

    fn visit_region(&mut self, region: &mut ty::Region<'tcx>, _: Location) {
        *region = self.tcx.lifetimes.re_erased;
    }
}
