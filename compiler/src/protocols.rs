pub use crate::contracts::graph::flows::{Flow, Obligation, Return};
use crate::contracts::graph::{CapacityError, ConditionId, FlowId, Graph};

use rustc_data_structures::fx::{FxHashSet, FxIndexSet};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::mir::Place;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{Span, Symbol};

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
