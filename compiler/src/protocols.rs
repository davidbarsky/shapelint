pub use crate::contracts::graph::flows::{Flow, Obligation, Return};
use crate::contracts::graph::{
    AlternativeId, CapacityError, ConditionId, FlowId, Graph, GuardContextId,
};

use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir::Place;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{Span, Symbol};
use shapelint::CompilerEvidence;

use crate::contracts::{Consumer, Operation, Truth};
use crate::{diagnostics, states};

mod projection;

pub enum Action {
    Invalidate,
    Establish,
    Require,
}
pub struct Declaration {
    pub name: Symbol,
    pub action: Action,
}

/// Records protocol names independently of operation signature validation.
///
/// Signature checking can request MIR, so the driver publishes these names first
/// and aborts on declaration errors before emitting analysis.
pub struct Catalog {
    pub names: Vec<Symbol>,
    declarations: Vec<LocalDefId>,
}

impl Catalog {
    pub fn collect(tcx: TyCtxt<'_>) -> Self {
        let mut names = FxIndexSet::default();
        let mut declarations = Vec::new();
        for owner in tcx.hir_body_owners() {
            if let Some((declaration, _)) = annotation(tcx, owner.to_def_id()) {
                names.insert(declaration.name);
                declarations.push(owner);
            }
        }
        let catalog = Self {
            names: names.into_iter().collect(),
            declarations,
        };
        catalog
    }

    pub fn check_signatures(&self, tcx: TyCtxt<'_>) {
        for def in &self.declarations {
            let _ = declaration(tcx, def.to_def_id());
        }
        tcx.dcx().abort_if_errors();
    }
}

pub fn declaration(tcx: TyCtxt<'_>, def: DefId) -> Option<Declaration> {
    let (declaration, span) = annotation(tcx, def)?;
    let signature = tcx.fn_sig(def).instantiate_identity().skip_binder();
    match (
        signature.inputs().first().map(|ty| ty.kind()),
        signature.output().is_unit(),
    ) {
        (Some(ty::Ref(..)), true) => Some(declaration),
        _ => {
            tcx.dcx().span_err(span, "a protocol operation takes its resource by reference first and returns (); establish applies only on normal return");
            None
        }
    }
}

fn annotation(tcx: TyCtxt<'_>, def: DefId) -> Option<(Declaration, Span)> {
    let path = [Symbol::intern("shapelint"), Symbol::intern("protocol")];
    let mut attributes = tcx.get_attrs_by_path(def, &path);
    let attribute = attributes.next()?;
    let parsed = attribute.meta_item_list().and_then(|items| {
        let [name, action] = items.as_slice() else {
            return None;
        };
        let name = name.ident()?.name;
        let action = match action.ident()?.name.as_str() {
            "invalidate" => Action::Invalidate,
            "establish" => Action::Establish,
            "require" => Action::Require,
            _ => return None,
        };
        Some(Declaration { name, action })
    });
    if let None = parsed {
        tcx.dcx().span_err(
            attribute.span(),
            "expected shapelint::protocol(name, invalidate | establish | require)",
        );
    }
    if let Some(_) = attributes.next() {
        tcx.dcx().span_err(
            attribute.span(),
            "a protocol operation declares exactly one transition",
        );
        return None;
    }
    parsed.map(|declaration| (declaration, attribute.span()))
}

pub struct Stores<'tcx, 'g, 'p> {
    flows: crate::persistent::Maps<'p, (Symbol, Place<'tcx>), FlowId<'g>>,
    locals: crate::persistent::Maps<
        'p,
        rustc_middle::mir::Local,
        crate::persistent::Set<'p, (Symbol, Place<'tcx>)>,
    >,
    keys: crate::persistent::Sets<'p, (Symbol, Place<'tcx>)>,
    incoming_places: crate::persistent::Maps<'p, rustc_middle::mir::Local, Place<'tcx>>,
    incoming_names: crate::persistent::Sets<'p, Symbol>,
}

impl<'tcx, 'g, 'p> Stores<'tcx, 'g, 'p> {
    pub(crate) fn new() -> Self {
        Self {
            flows: crate::persistent::Maps::new(),
            locals: crate::persistent::Maps::new(),
            keys: crate::persistent::Maps::new(),
            incoming_places: crate::persistent::Maps::new(),
            incoming_names: crate::persistent::Maps::new(),
        }
    }
}

pub fn with_stores<'tcx, 'g, T>(
    graph: &mut Graph<'g>,
    f: impl for<'p> FnOnce(&mut Stores<'tcx, 'g, 'p>, &mut Graph<'g>) -> T,
) -> T {
    let mut stores = Stores::new();
    f(&mut stores, graph)
}

#[derive(Clone, Copy)]
pub struct State<'tcx, 'g, 'p> {
    flows: crate::persistent::Map<'p, (Symbol, Place<'tcx>), FlowId<'g>>,
    locals: crate::persistent::Map<
        'p,
        rustc_middle::mir::Local,
        crate::persistent::Set<'p, (Symbol, Place<'tcx>)>,
    >,
    incoming_places: crate::persistent::Map<'p, rustc_middle::mir::Local, Place<'tcx>>,
    incoming_names: crate::persistent::Set<'p, Symbol>,
    incoming_flow: Option<FlowId<'g>>,
}

impl PartialEq for State<'_, '_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.flows == other.flows
            && self.incoming_places == other.incoming_places
            && self.incoming_names == other.incoming_names
            && self.incoming_flow == other.incoming_flow
    }
}
impl Eq for State<'_, '_, '_> {}
impl std::hash::Hash for State<'_, '_, '_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.flows, state);
        std::hash::Hash::hash(&self.incoming_places, state);
        std::hash::Hash::hash(&self.incoming_names, state);
        std::hash::Hash::hash(&self.incoming_flow, state);
    }
}
impl Default for State<'_, '_, '_> {
    fn default() -> Self {
        Self {
            flows: crate::persistent::Map::EMPTY,
            locals: crate::persistent::Map::EMPTY,
            incoming_places: crate::persistent::Map::EMPTY,
            incoming_names: crate::persistent::Map::EMPTY,
            incoming_flow: None,
        }
    }
}

impl<'tcx, 'g, 'p> State<'tcx, 'g, 'p> {
    fn incoming(
        &self,
        stores: &Stores<'tcx, 'g, 'p>,
        key: (Symbol, Place<'tcx>),
    ) -> Option<FlowId<'g>> {
        let Some(place) = stores
            .incoming_places
            .get(self.incoming_places, &key.1.local)
        else {
            return None;
        };
        if *place != key.1 {
            return None;
        }
        let Some(&()) = stores.incoming_names.get(self.incoming_names, &key.0) else {
            return None;
        };
        self.incoming_flow
    }

    fn flow(
        &self,
        stores: &Stores<'tcx, 'g, 'p>,
        key: (Symbol, Place<'tcx>),
        unknown: FlowId<'g>,
    ) -> FlowId<'g> {
        stores
            .flows
            .get(self.flows, &key)
            .copied()
            .or_else(|| self.incoming(stores, key))
            .unwrap_or(unknown)
    }

    /// Returns the persistent entries needed to represent this state.
    ///
    /// Incoming flows are stored as a product of argument places and names;
    /// explicit entries are materialized only when an operation changes one.
    pub fn storage_entries(&self, stores: &Stores<'tcx, 'g, 'p>) -> usize {
        stores.flows.len(self.flows)
            + stores.incoming_places.len(self.incoming_places)
            + stores.incoming_names.len(self.incoming_names)
    }

    fn insert(
        &mut self,
        stores: &mut Stores<'tcx, 'g, 'p>,
        key: (Symbol, Place<'tcx>),
        flow: FlowId<'g>,
    ) -> Result<(), CapacityError> {
        let mut flows = self.flows;
        if let None = stores.flows.insert(&mut flows, key, flow)? {
            let mut keys = stores
                .locals
                .get(self.locals, &key.1.local)
                .copied()
                .unwrap_or(crate::persistent::Set::EMPTY);
            stores.keys.insert(&mut keys, key, ())?;
            stores.locals.insert(&mut self.locals, key.1.local, keys)?;
        }
        self.flows = flows;
        Ok(())
    }

    pub fn initial(
        stores: &mut Stores<'tcx, 'g, 'p>,
        graph: &mut Graph<'g>,
        tcx: TyCtxt<'tcx>,
        body: &rustc_middle::mir::Body<'tcx>,
        names: &[Symbol],
    ) -> Result<Self, CapacityError> {
        let mut state = Self::default();
        for local in body.args_iter() {
            if body.local_decls[local].ty.is_ref() {
                if let None = state.incoming_flow {
                    state.incoming_flow = Some(graph.intern_flow(Flow::Incoming)?);
                    for name in names {
                        stores
                            .incoming_names
                            .insert(&mut state.incoming_names, *name, ())?;
                    }
                }
                let resource = Place::from(local)
                    .project_deeper(&[rustc_middle::mir::ProjectionElem::Deref], tcx);
                stores
                    .incoming_places
                    .insert(&mut state.incoming_places, local, resource)?;
            }
        }
        Ok(state)
    }

    pub fn merge(
        &mut self,
        stores: &mut Stores<'tcx, 'g, 'p>,
        graph: &mut Graph<'g>,
        other: &Self,
        join: crate::contracts::Join,
        decision: Option<ConditionId<'g>>,
    ) -> Result<(), CapacityError> {
        self.merge_with(stores, graph, other, |graph, left, right| {
            graph.join_flow(left, right, join, decision)
        })
    }

    pub(crate) fn merge_with(
        &mut self,
        stores: &mut Stores<'tcx, 'g, 'p>,
        graph: &mut Graph<'g>,
        other: &Self,
        mut join: impl FnMut(
            &mut Graph<'g>,
            FlowId<'g>,
            FlowId<'g>,
        ) -> Result<FlowId<'g>, CapacityError>,
    ) -> Result<(), CapacityError> {
        let mut names = FxIndexSet::default();
        for (name, ()) in stores.incoming_names.iter(self.incoming_names) {
            names.insert(*name);
        }
        for (name, ()) in stores.incoming_names.iter(other.incoming_names) {
            names.insert(*name);
        }
        let names: Vec<_> = names.into_iter().collect();
        let mut incoming_locals: FxIndexSet<_> = crate::persistent::Differences::from((
            &stores.incoming_places,
            self.incoming_places,
            other.incoming_places,
        ))
        .map(|(local, _)| *local)
        .collect();
        if self.incoming_names != other.incoming_names {
            for (local, _) in stores.incoming_places.iter(self.incoming_places) {
                incoming_locals.insert(*local);
            }
            for (local, _) in stores.incoming_places.iter(other.incoming_places) {
                incoming_locals.insert(*local);
            }
        }
        let changes: Vec<_> =
            crate::persistent::Differences::from((&stores.flows, self.flows, other.flows))
                .map(|(resource, change)| {
                    (
                        *resource,
                        match change {
                            crate::persistent::Difference::Left(flow) => {
                                crate::persistent::Difference::Left(*flow)
                            }
                            crate::persistent::Difference::Right(flow) => {
                                crate::persistent::Difference::Right(*flow)
                            }
                            crate::persistent::Difference::Both(left, right) => {
                                crate::persistent::Difference::Both(*left, *right)
                            }
                        },
                    )
                })
                .collect();
        if incoming_locals.is_empty() && changes.is_empty() {
            return Ok(());
        }
        let unknown = graph.intern_flow(Flow::Unknown)?;
        let mut merged = Vec::new();
        for local in incoming_locals.iter() {
            let mut resources = Vec::new();
            if let Some(resource) = stores.incoming_places.get(self.incoming_places, local) {
                resources.push(*resource);
            }
            if let Some(resource) = stores.incoming_places.get(other.incoming_places, local) {
                if !resources.contains(resource) {
                    resources.push(*resource);
                }
            }
            for resource in resources {
                for name in &names {
                    let key = (*name, resource);
                    let left = self.flow(stores, key, unknown);
                    let right = other.flow(stores, key, unknown);
                    merged.push((key, join(graph, left, right)?));
                }
            }
        }
        for (resource, change) in changes {
            let (left, right) = match change {
                crate::persistent::Difference::Left(flow) => {
                    (flow, other.flow(stores, resource, unknown))
                }
                crate::persistent::Difference::Right(flow) => {
                    (self.flow(stores, resource, unknown), flow)
                }
                crate::persistent::Difference::Both(left, right) => (left, right),
            };
            merged.push((resource, join(graph, left, right)?));
        }
        for local in incoming_locals {
            stores
                .incoming_places
                .remove(&mut self.incoming_places, &local)?;
        }
        for (resource, flow) in merged {
            self.insert(stores, resource, flow)?;
        }
        Ok(())
    }

    pub fn forget(
        &mut self,
        stores: &mut Stores<'tcx, 'g, 'p>,
        place: Place<'tcx>,
    ) -> Result<(), CapacityError> {
        if place.projection.is_empty() {
            stores
                .incoming_places
                .remove(&mut self.incoming_places, &place.local)?;
            let mut locals = self.locals;
            if let Some(keys) = stores.locals.remove(&mut locals, &place.local)? {
                let keys: Vec<_> = stores.keys.iter(keys).map(|(key, ())| *key).collect();
                let mut flows = self.flows;
                for key in keys {
                    stores.flows.remove(&mut flows, &key)?;
                }
                self.flows = flows;
                self.locals = locals;
            }
        }
        Ok(())
    }

    pub fn call(
        &mut self,
        stores: &mut Stores<'tcx, 'g, 'p>,
        graph: &mut Graph<'g>,
        tcx: TyCtxt<'tcx>,
        owner: DefId,
        callee: Option<DefId>,
        resources: &[(usize, Place<'tcx>)],
        names: &[Symbol],
        span: Span,
        guards: &crate::sequence::Sequence<'g, ConditionId<'g>>,
    ) -> Result<Option<Obligation<'g, ConditionId<'g>, FlowId<'g>>>, CapacityError> {
        let declared = callee.and_then(|callee| declaration(tcx, callee));
        if let Some(Declaration { name, action }) = declared {
            let Some((_, resource)) = resources.iter().find(|(argument, _)| *argument == 0) else {
                return Ok(None);
            };
            let unknown = graph.intern_flow(Flow::Unknown)?;
            let key = (name, *resource);
            let flow = self.flow(stores, key, unknown);
            let flow = match action {
                Action::Invalidate => graph.intern_flow(Flow::Dirty { def: owner, span })?,
                Action::Establish => graph.intern_flow(Flow::Ready)?,
                Action::Require => {
                    if let None = stores.flows.get(self.flows, &key) {
                        if let None = self.incoming(stores, key) {
                            self.insert(stores, key, unknown)?;
                        }
                    }
                    let obligation = Obligation {
                        name,
                        span,
                        flow,
                        guards: *guards,
                    };
                    return Ok(Some(obligation));
                }
            };
            self.insert(stores, (name, *resource), flow)?;
            return Ok(None);
        }
        let mut seen = FxHashSet::default();
        let mut aliased = FxHashSet::default();
        for (_, resource) in resources {
            if !seen.insert(*resource) {
                aliased.insert(*resource);
            }
        }
        let mut next = *self;
        for (argument, resource) in resources {
            for name in names {
                let unknown = graph.intern_flow(Flow::Unknown)?;
                let flow = next.flow(stores, (*name, *resource), unknown);
                let flow = match callee {
                    Some(callee) if callee.is_local() && !aliased.contains(resource) => graph
                        .intern_flow(Flow::Call {
                            callee,
                            argument: *argument,
                            input: flow,
                        })?,
                    _ => unknown,
                };
                next.insert(stores, (*name, *resource), flow)?;
            }
        }
        *self = next;
        Ok(None)
    }

    pub fn returns(
        &self,
        stores: &Stores<'tcx, 'g, 'p>,
        arg_count: usize,
    ) -> Vec<Return<FlowId<'g>>> {
        let mut returned: Vec<_> = stores
            .flows
            .iter(self.flows)
            .filter_map(|((name, resource), flow)| {
                let argument = resource.local.index().checked_sub(1)?;
                if argument >= arg_count || resource.projection.len() != 1 {
                    return None;
                }
                Some(Return {
                    name: *name,
                    argument,
                    flow: *flow,
                })
            })
            .collect();
        for (local, resource) in stores.incoming_places.iter(self.incoming_places) {
            let Some(argument) = local.index().checked_sub(1) else {
                continue;
            };
            if argument >= arg_count || resource.projection.len() != 1 {
                continue;
            }
            for (name, ()) in stores.incoming_names.iter(self.incoming_names) {
                let None = stores.flows.get(self.flows, &(*name, *resource)) else {
                    continue;
                };
                if let Some(flow) = self.incoming_flow {
                    returned.push(Return {
                        name: *name,
                        argument,
                        flow,
                    });
                }
            }
        }
        returned
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Effect {
    Unchanged,
    Ready,
    Dirty(DefId, Span),
    Unknown,
}

impl Effect {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unchanged, Self::Unchanged) => Self::Unchanged,
            (Self::Ready, Self::Ready) => Self::Ready,
            (Self::Dirty(def, span), Self::Dirty(..)) => Self::Dirty(def, span),
            _ => Self::Unknown,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Subject<'g> {
    Flow(FlowId<'g>),
    Prefix(AlternativeId<'g>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Demand {
    Effect,
    Witness,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Query<'g> {
    subject: Subject<'g>,
    demand: Demand,
    name: Symbol,
    guards: GuardContextId<'g>,
}

struct Queries<'a, 'p, 'g> {
    graph: &'a mut Graph<'g>,
    returns: FxHashMap<(DefId, Symbol, usize), AlternativeId<'g>>,
    values: FxHashMap<Query<'g>, Effect>,
    empty: GuardContextId<'g>,
    projection: projection::Projection<'p, 'g>,
}

impl<'a, 'p, 'g> Queries<'a, 'p, 'g> {
    fn try_new(
        graph: &'a mut Graph<'g>,
        summaries: &FxHashMap<DefId, crate::contracts::summaries::SummaryId<'g>>,
    ) -> Result<Self, CapacityError> {
        let mut returns = FxHashMap::default();
        for (callee, summary) in summaries {
            let summary = graph[*summary];
            let mut returned = graph.scan(summary.protocol_returns);
            while let Some(returned) = returned.next() {
                let key = (*callee, returned.name, returned.argument);
                let prefix = graph.intern_alternative(returns.get(&key).copied(), returned.flow)?;
                returns.insert(key, prefix);
            }
        }
        let empty = GuardContextId::from(crate::sequence::Sequence::EMPTY);
        let mut roots: Vec<_> = returns.values().copied().map(Subject::Prefix).collect();
        let mut guards = Vec::new();
        for summary in summaries.values() {
            let summary = graph[*summary];
            for check in graph.items(summary.protocol_checks) {
                roots.push(Subject::Flow(check.flow));
                guards.push(check.guards);
            }
        }
        let projection = projection::Projection::try_new(graph, roots, guards)?;
        Ok(Self {
            graph,
            returns,
            values: FxHashMap::default(),
            empty,
            projection,
        })
    }
}

impl<'p, 'g> crate::contracts::schedule::Engine for Queries<'_, 'p, 'g> {
    type Query = Query<'g>;
    type Answer = Effect;
    type Error = CapacityError;
    type Frame = Query<'g>;

    fn lookup(
        &mut self,
        query: &Query<'g>,
    ) -> Result<crate::contracts::schedule::Lookup<Effect>, CapacityError> {
        let guards = self
            .projection
            .project(self.graph, query.subject, query.guards)?;
        let query = Query { guards, ..*query };
        Ok(match self.values.get(&query) {
            Some(answer) => crate::contracts::schedule::Lookup::Ready(*answer),
            None => crate::contracts::schedule::Lookup::Missing,
        })
    }

    fn enter(&mut self, query: Query<'g>) -> Result<Query<'g>, CapacityError> {
        let guards = self
            .projection
            .project(self.graph, query.subject, query.guards)?;
        let query = Query { guards, ..query };
        // Every demanded effect dependency is Unknown-strict: joins preserve
        // Unknown, and calls inspect their input only after an Unchanged callee.
        // A demanded cycle therefore stays Unknown; no completed prefix retries.
        // Witness dependencies follow the acyclic flow/prefix graph and only
        // cross into effects, never the reverse.
        self.values.insert(query, Effect::Unknown);
        Ok(query)
    }

    fn finish(
        &mut self,
        query: Query<'g>,
        answer: Effect,
    ) -> crate::contracts::schedule::Finished<Query<'g>, Effect> {
        self.values.insert(query, answer);
        crate::contracts::schedule::Finished::Ready(answer)
    }

    async fn execute(
        session: crate::contracts::schedule::Session<'_, Self>,
        query: Query<'g>,
    ) -> Result<Effect, CapacityError> {
        let guards = session.with(|engine| {
            engine
                .projection
                .project(engine.graph, query.subject, query.guards)
        })?;
        let query = Query { guards, ..query };
        let flow = match query.subject {
            Subject::Prefix(prefix) => {
                let (previous, value) = session.with(|engine| {
                    let prefix = &engine.graph[prefix];
                    (prefix.previous, prefix.value)
                });
                let previous = match previous {
                    Some(previous) => Some(
                        session
                            .query(Query {
                                subject: Subject::Prefix(previous),
                                ..query
                            })
                            .await?,
                    ),
                    None => None,
                };
                if let (Demand::Witness, Some(effect @ Effect::Dirty(..))) =
                    (query.demand, previous)
                {
                    return Ok(effect);
                }
                let next = session
                    .query(Query {
                        subject: Subject::Flow(value),
                        ..query
                    })
                    .await?;
                return Ok(match (query.demand, previous) {
                    (Demand::Effect, Some(previous)) => previous.join(next),
                    (Demand::Witness, _) | (Demand::Effect, None) => next,
                });
            }
            Subject::Flow(flow) => session.with(|engine| engine.graph[flow].clone()),
        };
        Ok(match flow {
            Flow::Incoming => Effect::Unchanged,
            Flow::Unknown => Effect::Unknown,
            Flow::Ready => Effect::Ready,
            Flow::Dirty { def, span } => Effect::Dirty(def, span),
            Flow::Alternatives(None) => Effect::Unknown,
            Flow::Alternatives(Some(prefix)) => {
                session
                    .query(Query {
                        subject: Subject::Prefix(prefix),
                        ..query
                    })
                    .await?
            }
            Flow::Select(condition, yes, no) => {
                let truth = session.with(|engine| {
                    engine
                        .graph
                        .prove_in_context(condition, query.guards)
                        .map(Truth::from)
                })?;
                match truth {
                    Truth::Proven => {
                        session
                            .query(Query {
                                subject: Subject::Flow(yes),
                                ..query
                            })
                            .await?
                    }
                    Truth::Refuted => {
                        session
                            .query(Query {
                                subject: Subject::Flow(no),
                                ..query
                            })
                            .await?
                    }
                    Truth::Unknown(_) => {
                        let (selected, otherwise) = match query.demand {
                            Demand::Effect => (query.guards, query.guards),
                            Demand::Witness => session.with(|engine| {
                                let negated = engine.graph.negate(condition)?;
                                Ok((
                                    GuardContextId(engine.graph.push(query.guards.0, condition)?),
                                    GuardContextId(engine.graph.push(query.guards.0, negated)?),
                                ))
                            })?,
                        };
                        let yes = session
                            .query(Query {
                                subject: Subject::Flow(yes),
                                guards: selected,
                                ..query
                            })
                            .await?;
                        match (query.demand, yes) {
                            (Demand::Witness, effect @ Effect::Dirty(..)) => effect,
                            (demand, yes) => {
                                let no = session
                                    .query(Query {
                                        subject: Subject::Flow(no),
                                        guards: otherwise,
                                        ..query
                                    })
                                    .await?;
                                match demand {
                                    Demand::Effect => yes.join(no),
                                    Demand::Witness => no,
                                }
                            }
                        }
                    }
                }
            }
            Flow::Call {
                callee,
                argument,
                input,
            } => {
                if let Demand::Witness = query.demand {
                    return session
                        .query(Query {
                            demand: Demand::Effect,
                            ..query
                        })
                        .await;
                }
                let returned = session.with(|engine| {
                    engine
                        .returns
                        .get(&(callee, query.name, argument))
                        .map(|prefix| (*prefix, engine.empty))
                });
                let Some((prefix, guards)) = returned else {
                    return Ok(Effect::Unknown);
                };
                let effect = session
                    .query(Query {
                        subject: Subject::Prefix(prefix),
                        guards,
                        ..query
                    })
                    .await?;
                match effect {
                    Effect::Unchanged => {
                        session
                            .query(Query {
                                subject: Subject::Flow(input),
                                ..query
                            })
                            .await?
                    }
                    effect => effect,
                }
            }
        })
    }
}

pub fn findings<'g>(
    tcx: TyCtxt<'_>,
    graph: &mut Graph<'g>,
    summaries: &FxHashMap<DefId, crate::contracts::summaries::SummaryId<'g>>,
    sources: &diagnostics::Sources,
) -> Result<Vec<(rustc_hir::def_id::LocalDefId, states::Finding)>, CapacityError> {
    Queries::try_new(graph, summaries)?.findings(tcx, summaries, sources)
}

impl<'g> Queries<'_, '_, 'g> {
    fn findings(
        mut self,
        tcx: TyCtxt<'_>,
        summaries: &FxHashMap<DefId, crate::contracts::summaries::SummaryId<'g>>,
        sources: &diagnostics::Sources,
    ) -> Result<Vec<(rustc_hir::def_id::LocalDefId, states::Finding)>, CapacityError> {
        let mut findings = Vec::new();
        for (owner, summary) in summaries {
            let Some(local) = owner.as_local() else {
                continue;
            };
            let summary = self.graph[*summary];
            let mut obligations = self.graph.scan(summary.protocol_checks);
            while let Some(obligation) = obligations.next() {
                let guards = GuardContextId::from(obligation.guards);
                let query = Query {
                    subject: Subject::Flow(obligation.flow),
                    demand: Demand::Witness,
                    name: obligation.name,
                    guards,
                };
                let Effect::Dirty(def, origin) =
                    crate::contracts::schedule::evaluate(&mut self, query)?
                else {
                    continue;
                };
                if let None = diagnostics::source_span(tcx, *owner, obligation.span) {
                    continue;
                }
                if let None = diagnostics::source_span(tcx, def, origin) {
                    continue;
                }
                let mut origin = Consumer {
                    def,
                    span: origin,
                    operation: Operation::Condition,
                }
                .source(tcx, sources);
                origin.label.message = format!(
                    "this operation invalidates `{}` for the same resource",
                    obligation.name
                );
                findings.push((
                    local,
                    states::Finding {
                        span: obligation.span,
                        evidence: CompilerEvidence::ProtocolBypass {
                            protocol: obligation.name.to_string(),
                            origin,
                        },
                    },
                ));
            }
        }
        findings.sort_by_key(|(def, finding)| (tcx.def_span(*def).lo(), finding.span.lo()));
        Ok(findings)
    }
}
