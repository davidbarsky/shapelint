use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{CrateNum, DefId};
use rustc_middle::ty::TyCtxt;

use crate::contracts::graph::{
    ConditionId, ConditionNode, ExprId, ExprNode, Graph, NodeId, TargetNode,
};
use crate::contracts::{Call, CheckBasis};

#[derive(Clone, Copy)]
pub enum Scope {
    Library,
    Target,
}

pub enum Exposure {
    Internal,
    External,
}

pub fn exposure(tcx: TyCtxt<'_>, def: DefId, scope: Scope) -> Exposure {
    match tcx.def_kind(def) {
        DefKind::Fn | DefKind::AssocFn => {
            if !tcx
                .fn_sig(def)
                .instantiate_identity()
                .skip_binder()
                .abi()
                .is_rustic_abi()
            {
                return Exposure::External;
            }
        }
        DefKind::Static { .. } => {}
        _ => return Exposure::Internal,
    }
    if tcx.codegen_fn_attrs(def).contains_extern_indicator() {
        return Exposure::External;
    }
    match scope {
        Scope::Library if tcx.visibility(def).is_public() => Exposure::External,
        Scope::Library | Scope::Target => Exposure::Internal,
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct SiteId(u32);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct EscapedFunction(DefId);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct CoveredCrate(CrateNum);

pub struct Callers<'g> {
    scope: Scope,
    escapes: crate::persistent::Set<'g, EscapedFunction>,
    escape_sets: crate::persistent::Sets<'g, EscapedFunction>,
    coverage: crate::persistent::Set<'g, CoveredCrate>,
    coverage_sets: crate::persistent::Sets<'g, CoveredCrate>,
    coverage_cache: std::cell::RefCell<Option<FxHashMap<CrateNum, Option<()>>>>,
    sites: crate::persistent::Map<'g, DefId, crate::sequence::Sequence<'g, SiteId>>,
    site_maps: crate::persistent::Maps<'g, DefId, crate::sequence::Sequence<'g, SiteId>>,
    site_lists: crate::sequence::Sequences<'g, SiteId>,
    calls: crate::sequence::Sequence<
        'g,
        (DefId, Call<'g, ExprId<'g>, ConditionId<'g>, TargetNode<'g>>),
    >,
    call_lists: crate::sequence::Sequences<
        'g,
        (DefId, Call<'g, ExprId<'g>, ConditionId<'g>, TargetNode<'g>>),
    >,
}

impl<'g> Callers<'g> {
    pub fn try_new(
        scope: Scope,
        values: &impl std::ops::Index<
            crate::values::InstanceId<'g>,
            Output = crate::values::InstanceNode<'g>,
        >,
        calls: Vec<(DefId, Call<'g, ExprId<'g>, ConditionId<'g>, TargetNode<'g>>)>,
        escapes: FxHashSet<DefId>,
        coverage: &FxHashSet<CrateNum>,
    ) -> Result<Self, crate::contracts::graph::CapacityError> {
        let mut sites = crate::persistent::Map::EMPTY;
        let mut site_maps = crate::persistent::Maps::new();
        let mut site_lists = crate::sequence::Sequences::new();
        let indexed_calls = calls.iter().enumerate();
        for (index, (_, call)) in indexed_calls {
            if let Some(def) = call.target.definition(values) {
                let index = u32::try_from(index)
                    .map_err(|_| crate::contracts::graph::CapacityError::Values)?;
                let previous = site_maps
                    .get(sites, &def)
                    .copied()
                    .unwrap_or(crate::sequence::Sequence::EMPTY);
                let previous = site_lists.push(previous, SiteId(index))?;
                site_maps.insert(&mut sites, def, previous)?;
            }
        }
        let mut call_lists = crate::sequence::Sequences::new();
        let calls = call_lists.from_iter(calls)?;
        let mut escape_sets = crate::persistent::Maps::new();
        let mut escaped = crate::persistent::Map::EMPTY;
        for def in escapes {
            escape_sets.insert(&mut escaped, EscapedFunction(def), ())?;
        }
        let mut coverage_sets = crate::persistent::Maps::new();
        let mut covered = crate::persistent::Map::EMPTY;
        for krate in coverage {
            coverage_sets.insert(&mut covered, CoveredCrate(*krate), ())?;
        }
        Ok(Self {
            scope,
            escapes: escaped,
            escape_sets,
            sites,
            site_maps,
            site_lists,
            calls,
            call_lists,
            coverage: covered,
            coverage_sets,
            coverage_cache: std::cell::RefCell::default(),
        })
    }

    /// Returned sites cover the function's callers within the declared boundary.
    /// A target boundary still permits foreign entry points and escaping callbacks.
    pub fn complete(
        &self,
        tcx: TyCtxt<'_>,
        def: DefId,
    ) -> Option<impl Iterator<Item = &(DefId, Call<'g, ExprId<'g>, ConditionId<'g>, TargetNode<'g>>)>>
    {
        match tcx.def_kind(def) {
            DefKind::Fn | DefKind::AssocFn => {}
            _ => return None,
        }
        if let Some(()) = self.escape_sets.get(self.escapes, &EscapedFunction(def)) {
            return None;
        }
        if let Exposure::External = exposure(tcx, def, self.scope) {
            return None;
        }
        if let Some(_) = tcx
            .trait_of_assoc(def)
            .or_else(|| tcx.trait_impl_of_assoc(def))
        {
            return None;
        }
        match self.scope {
            Scope::Library if !def.is_local() => return None,
            Scope::Target if !def.is_local() => {
                let mut cached = self.coverage_cache.borrow_mut();
                let coverage = cached.get_or_insert_with(|| {
                    let mut suffixes = FxHashMap::default();
                    let mut covered = Some(());
                    // Dependency order excludes earlier crates as callers.
                    let crates = tcx.postorder_cnums(()).iter().rev();
                    for krate in crates {
                        covered = covered.and(
                            self.coverage_sets
                                .get(self.coverage, &CoveredCrate(*krate))
                                .copied(),
                        );
                        suffixes.insert(*krate, covered);
                    }
                    suffixes
                });
                match coverage.get(&def.krate) {
                    Some(Some(())) => {}
                    Some(None) | None => return None,
                }
            }
            Scope::Library | Scope::Target => {}
        }
        self.site_maps.get(self.sites, &def).map(|sites| {
            self.site_lists.iter(*sites).map(|index| {
                self.call_lists
                    .get(self.calls, index.0 as usize)
                    .expect("indexed call exists")
            })
        })
    }
}

fn nested_evaluation<'g>(
    graph: &Graph<'g>,
    memo: &mut FxHashMap<NodeId<'g>, Option<()>>,
    root: NodeId<'g>,
) -> Option<()> {
    enum Work<'g> {
        Visit(NodeId<'g>),
        Build(NodeId<'g>, Vec<NodeId<'g>>),
    }
    let mut pending = vec![Work::Visit(root)];
    while let Some(work) = pending.pop() {
        match work {
            Work::Visit(node) => {
                if memo.contains_key(&node) {
                    continue;
                }
                let demand = match node {
                    NodeId::Expr(id) => match &graph[id] {
                        ExprNode::Call(..) | ExprNode::Global(_) | ExprNode::Partition { .. } => {
                            Some(())
                        }
                        ExprNode::Serialized { .. }
                        | ExprNode::Unknown
                        | ExprNode::Function(_)
                        | ExprNode::Typed(..)
                        | ExprNode::Alternatives(_)
                        | ExprNode::Select(..)
                        | ExprNode::Opaque(_)
                        | ExprNode::Argument(_)
                        | ExprNode::Number(_)
                        | ExprNode::Range(_)
                        | ExprNode::Text(_)
                        | ExprNode::Field(..)
                        | ExprNode::Element(..)
                        | ExprNode::Closure(..)
                        | ExprNode::Aggregate(_)
                        | ExprNode::Variant(..)
                        | ExprNode::Length(_)
                        | ExprNode::Trimmed(_)
                        | ExprNode::Found { .. }
                        | ExprNode::MatchIndex { .. }
                        | ExprNode::Matches { .. }
                        | ExprNode::MatchEntry(_)
                        | ExprNode::Tokens { .. }
                        | ExprNode::Token(_)
                        | ExprNode::NextToken(_)
                        | ExprNode::Cursor { .. }
                        | ExprNode::Slice { .. }
                        | ExprNode::Arithmetic(..)
                        | ExprNode::Test(_) => None,
                    },
                    NodeId::Condition(id) => match &graph[id] {
                        ConditionNode::Returned(..) => Some(()),
                        ConditionNode::Unknown
                        | ConditionNode::Compare(..)
                        | ConditionNode::Boundary(..)
                        | ConditionNode::NotBoundary(..)
                        | ConditionNode::Variant(..)
                        | ConditionNode::NotVariant(..) => None,
                    },
                    NodeId::Choice(_) => None,
                };
                if let Some(()) = demand {
                    memo.insert(node, demand);
                    continue;
                }
                let mut children = Vec::new();
                graph.visit_children(node, |child| children.push(child));
                pending.push(Work::Build(node, children.clone()));
                pending.extend(children.into_iter().map(Work::Visit));
            }
            Work::Build(node, children) => {
                let demand = children.iter().find_map(|child| memo[child]);
                memo.insert(node, demand);
            }
        }
    }
    memo[&root]
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct IndexedCall<'g>(Call<'g, ExprId<'g>, ConditionId<'g>, TargetNode<'g>>);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ReverseCaller(DefId);

pub struct CallIndex<'a, 'g> {
    sites: crate::persistent::Map<'g, DefId, crate::sequence::Sequence<'g, IndexedCall<'g>>>,
    site_maps: crate::persistent::Maps<'g, DefId, crate::sequence::Sequence<'g, IndexedCall<'g>>>,
    calls: crate::sequence::Sequences<'g, IndexedCall<'g>>,
    reverse: crate::persistent::Map<'g, DefId, crate::sequence::Sequence<'g, ReverseCaller>>,
    reverse_maps: crate::persistent::Maps<'g, DefId, crate::sequence::Sequence<'g, ReverseCaller>>,
    reverse_sequences: crate::sequence::Sequences<'g, ReverseCaller>,
    opaque: crate::persistent::Set<'g, DefId>,
    opaque_sets: crate::persistent::Sets<'g, DefId>,
    marker: std::marker::PhantomData<&'a ()>,
}

impl<'a, 'g> CallIndex<'a, 'g> {
    pub fn try_new(
        tcx: TyCtxt<'_>,
        summaries: &FxHashMap<DefId, crate::contracts::summaries::SummaryId<'g>>,
        graph: &Graph<'g>,
    ) -> Result<Self, crate::contracts::graph::CapacityError> {
        let mut call_sequences = crate::sequence::Sequences::new();
        let mut nodes = FxHashMap::default();
        let mut sites = crate::persistent::Map::EMPTY;
        let mut site_maps = crate::persistent::Maps::new();
        let mut reverse = crate::persistent::Map::EMPTY;
        let mut reverse_maps = crate::persistent::Maps::new();
        let mut reverse_sequences = crate::sequence::Sequences::new();
        let mut opaque = crate::persistent::Map::EMPTY;
        let mut opaque_sets = crate::persistent::Maps::new();
        for (owner, summary) in summaries {
            let summary = graph[*summary];
            for call in graph.items(summary.calls) {
                match call.target {
                    TargetNode::Direct(instance) => {
                        let instance = graph[instance];
                        if instance.dispatch != crate::values::Dispatch::Item {
                            opaque_sets.insert(&mut opaque, *owner, ())?;
                            continue;
                        }
                        if instance.args != crate::values::GenericsId::EMPTY {
                            opaque_sets.insert(&mut opaque, *owner, ())?;
                        }
                        if let Some(_) = tcx.trait_of_assoc(instance.def) {
                            opaque_sets.insert(&mut opaque, *owner, ())?;
                        }
                        let previous = reverse_maps
                            .get(reverse, &instance.def)
                            .copied()
                            .unwrap_or(crate::sequence::Sequence::EMPTY);
                        let previous = reverse_sequences.push(previous, ReverseCaller(*owner))?;
                        reverse_maps.insert(&mut reverse, instance.def, previous)?;
                        match summaries.get(&instance.def) {
                            Some(callee) => {
                                let callee = graph[*callee];
                                if crate::sequence::Sequences::len(graph.as_ref(), callee.checks)
                                    != 0
                                {
                                    let previous = site_maps
                                        .get(sites, owner)
                                        .copied()
                                        .unwrap_or(crate::sequence::Sequence::EMPTY);
                                    let previous =
                                        call_sequences.push(previous, IndexedCall(*call))?;
                                    site_maps.insert(&mut sites, *owner, previous)?;
                                }
                                if callee.escaped_arguments
                                    != crate::contracts::graph::sets::SetId::EMPTY
                                {
                                    opaque_sets.insert(&mut opaque, *owner, ())?;
                                }
                            }
                            None => {
                                opaque_sets.insert(&mut opaque, *owner, ())?;
                            }
                        }
                    }
                    TargetNode::Indirect(_) => {
                        opaque_sets.insert(&mut opaque, *owner, ())?;
                    }
                }
            }
        }
        for (owner, summary) in summaries {
            if let Some(()) = opaque_sets.get(opaque, owner) {
                continue;
            }
            let summary = graph[*summary];
            'calls: for call in graph.items(summary.calls) {
                for argument in graph.items(call.arguments) {
                    if let Some(()) = nested_evaluation(graph, &mut nodes, NodeId::Expr(*argument))
                    {
                        opaque_sets.insert(&mut opaque, *owner, ())?;
                        break 'calls;
                    }
                }
                let basis = match &call.basis {
                    CheckBasis::Expression => None,
                    CheckBasis::ControlFlow(basis) => Some(basis),
                };
                let guards = graph
                    .items(call.guards)
                    .chain(basis.into_iter().flat_map(|basis| graph.items(*basis)));
                for guard in guards {
                    if let Some(()) =
                        nested_evaluation(graph, &mut nodes, NodeId::Condition(*guard))
                    {
                        opaque_sets.insert(&mut opaque, *owner, ())?;
                        break 'calls;
                    }
                }
            }
        }
        Ok(Self {
            sites,
            site_maps,
            calls: call_sequences,
            reverse,
            reverse_maps,
            reverse_sequences,
            opaque,
            opaque_sets,
            marker: std::marker::PhantomData,
        })
    }

    pub fn calls(
        &self,
        owner: DefId,
    ) -> impl Iterator<Item = Call<'g, ExprId<'g>, ConditionId<'g>, TargetNode<'g>>> + '_ {
        let sequence = self
            .site_maps
            .get(self.sites, &owner)
            .copied()
            .unwrap_or(crate::sequence::Sequence::EMPTY);
        self.calls.iter(sequence).map(|call| call.0)
    }

    pub fn relevant(&self, candidates: &FxHashSet<DefId>) -> FxHashSet<DefId> {
        let mut relevant = FxHashSet::default();
        let opaque = self.opaque_sets.iter(self.opaque).map(|(def, ())| *def);
        self.include_callers(&mut relevant, candidates.iter().copied().chain(opaque));
        relevant
    }

    pub(crate) fn include_callers(
        &self,
        relevant: &mut FxHashSet<DefId>,
        seeds: impl Iterator<Item = DefId>,
    ) {
        let mut pending: Vec<_> = seeds.filter(|def| relevant.insert(*def)).collect();
        while let Some(def) = pending.pop() {
            if let Some(callers) = self.reverse_maps.get(self.reverse, &def) {
                for caller in self.reverse_sequences.iter(*callers) {
                    if relevant.insert(caller.0) {
                        pending.push(caller.0);
                    }
                }
            }
        }
    }
}
