use crate::contracts::graph::{
    CapacityError, ConditionId, ConditionNode, ExprId, ExprNode, Graph, TargetNode,
};
use crate::contracts::operations::GraphInvalidation;
use crate::persistent::{Difference, Differences, Set};
use crate::states::places::Table;
use crate::values::StoreValue;

use crate::calls::Target;
use crate::contracts::{self, Expr, Join, Order, Truth};
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::mir::visit::Visitor;
use rustc_middle::mir::{
    AggregateKind, AssertKind, BasicBlock, BinOp, Body, CastKind, Location, Operand, Place,
    ProjectionElem, RETURN_PLACE, Rvalue, START_BLOCK, StatementKind, TerminatorKind, UnOp,
};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;
use shapelint::CompilerEvidence;

mod borrowed_clones;
pub use crate::diagnostics::Finding;
pub use borrowed_clones::borrowed_clones;
mod demand;
pub mod facts;
pub mod incoming;
mod library;
mod names;
mod places;
pub mod schedule;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Fact {
    Variant(VariantIdx),
    Scalar(u128),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Value<'tcx> {
    Direct(ValueKind<'tcx>),
    Negated(ValueKind<'tcx>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ValueKind<'tcx> {
    Known(Fact),
    Origin(Place<'tcx>),
    Reference(Place<'tcx>),
    Discriminant(Place<'tcx>),
    Predicate {
        place: Place<'tcx>,
        variant: VariantIdx,
    },
}

type Invalidated<'g> = contracts::InvalidatedFact<ConditionId<'g>>;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct State<'tcx, 's, 'g> {
    basis: contracts::CheckBasis<crate::contracts::graph::evidence::Evidence<'g>>,
    protocols: crate::protocols::State<'tcx, 'g, 's>,
    escaped_serializations: Set<'s, Span>,
    values: places::Tracked<'tcx, 's, Value<'tcx>>,
    guards: places::Tracked<'tcx, 's, Fact>,
    facts: facts::Facts<'tcx, 's, 'g>,
    invalidated: places::Tracked<'tcx, 's, ()>,
    moved: places::Tracked<'tcx, 's, ()>,
}

impl Default for State<'_, '_, '_> {
    fn default() -> Self {
        Self {
            basis: contracts::CheckBasis::default(),
            protocols: crate::protocols::State::default(),
            escaped_serializations: Set::EMPTY,
            values: places::Tracked::default(),
            guards: places::Tracked::default(),
            facts: facts::Facts::default(),
            invalidated: places::Tracked::default(),
            moved: places::Tracked::default(),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct StateId<'s>(u32, std::marker::PhantomData<fn(&'s mut ()) -> &'s mut ()>);

struct States<'tcx, 's, 'g> {
    values: Vec<State<'tcx, 's, 'g>>,
    ids: hashbrown::HashTable<(u64, StateId<'s>)>,
}
impl<'tcx, 's, 'g> States<'tcx, 's, 'g> {
    fn new() -> Self {
        Self {
            values: Vec::new(),
            ids: hashbrown::HashTable::new(),
        }
    }
    fn intern(&mut self, value: State<'tcx, 's, 'g>) -> Result<StateId<'s>, CapacityError> {
        use std::hash::{Hash, Hasher};
        let mut hasher = rustc_data_structures::fx::FxHasher::default();
        value.hash(&mut hasher);
        let hash = hasher.finish();
        if let Some((_, id)) = self
            .ids
            .find(hash, |(_, id)| self.values[id.0 as usize] == value)
        {
            return Ok(*id);
        }
        let id = StateId(
            u32::try_from(self.values.len()).map_err(|_| CapacityError::States)?,
            std::marker::PhantomData,
        );
        self.values.push(value);
        self.ids.insert_unique(hash, (hash, id), |(hash, _)| *hash);
        Ok(id)
    }
}
impl<'tcx, 's, 'g> std::ops::Index<StateId<'s>> for States<'tcx, 's, 'g> {
    type Output = State<'tcx, 's, 'g>;
    fn index(&self, id: StateId<'s>) -> &Self::Output {
        &self.values[id.0 as usize]
    }
}

#[derive(Default)]
struct Moves<'tcx>(Vec<Place<'tcx>>);

impl<'tcx> Visitor<'tcx> for Moves<'tcx> {
    fn visit_operand(&mut self, operand: &Operand<'tcx>, _: Location) {
        if let Operand::Move(place) = operand {
            self.0.push(*place);
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct StateType {
    pub definition: DefId,
    fingerprint: Fingerprint,
}

impl StateType {
    fn from_ty<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, ty: ty::Ty<'tcx>) -> Option<Self> {
        let ty::Adt(adt, _) = *ty.kind() else {
            return None;
        };
        if !adt.is_struct() {
            return None;
        }
        let fingerprint = tcx.with_stable_hashing_context(|mut context| {
            let mut hasher = StableHasher::new();
            tcx.erase_and_anonymize_regions(ty)
                .stable_hash(&mut context, &mut hasher);
            tcx.param_env(body.source.def_id())
                .stable_hash(&mut context, &mut hasher);
            hasher.finish()
        });
        Some(Self {
            definition: adt.did(),
            fingerprint,
        })
    }
}

pub struct Invariant {
    pub owner: StateType,
    pub guards: Vec<(FieldIdx, Fact)>,
    pub field: FieldIdx,
    pub required: VariantIdx,
    pub span: Span,
}

pub struct Construction {
    pub owner: StateType,
    pub fields: FxHashMap<FieldIdx, Fact>,
    pub span: Span,
}

pub struct Observations<
    'g,
    E = Expr,
    C = contracts::Condition,
    T = Target,
    F = std::convert::Infallible,
> {
    pub writes: contracts::Writes<'g>,
    pub contracts: contracts::Summary<'g, E, C, T, F>,
    pub findings: Vec<Finding>,
    pub invariants: Vec<Invariant>,
    pub constructions: Vec<Construction>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    pub block_transfers: usize,
    /// Counts repeat visits to transparent outer blocks that forward a nested loop's exit state.
    pub nested_exit_forwards: usize,
    pub statement_dispatches: usize,
    pub statement_transfers: usize,
    pub merges: usize,
    /// Counts newly attached dependency graph nodes during fact merges.
    pub attachments: usize,
    /// Counts indexed place uses, including unique-definition bookkeeping.
    pub clone_use_visits: usize,
    /// Counts use-list visits and memo lookups while tracing clone receivers.
    pub clone_origin_lookups: usize,
    pub clone_argument_lookups: usize,
    pub clone_call_block_visits: usize,
    pub clone_call_set_checks: usize,
    /// Counts one MIR projection-type step per place candidate query.
    pub place_prefix_type_steps: usize,
    /// Counts enum variants visited while constructing discriminant indexes.
    pub discriminant_index_visits: usize,
    /// Counts discriminant-to-variant lookups during switch refinement.
    pub discriminant_index_lookups: usize,
}

#[derive(Default)]
struct DiscriminantIndex {
    variants: FxHashMap<DefId, FxHashMap<u128, VariantIdx>>,
    visits: usize,
    lookups: usize,
}

impl DiscriminantIndex {
    fn variant(&mut self, tcx: TyCtxt<'_>, adt: DefId, chosen: u128) -> Option<VariantIdx> {
        self.lookups = self.lookups.saturating_add(1);
        if let None = self.variants.get(&adt) {
            let variants = tcx
                .adt_def(adt)
                .discriminants(tcx)
                .map(|(variant, discriminant)| (discriminant.val, variant))
                .collect::<FxHashMap<_, _>>();
            self.visits = self.visits.saturating_add(variants.len());
            self.variants.insert(adt, variants);
        }
        self.variants
            .get(&adt)
            .and_then(|variants| variants.get(&chosen).copied())
    }
}

pub struct Capture<'g, E, C, T, F> {
    pub observations: Observations<'g, E, C, T, F>,
    pub work: Work,
}

impl<E, C, T, F> Default for Observations<'_, E, C, T, F> {
    fn default() -> Self {
        Self {
            writes: contracts::Writes::default(),
            contracts: contracts::Summary::default(),
            findings: Vec::new(),
            invariants: Vec::new(),
            constructions: Vec::new(),
        }
    }
}

impl<'tcx, 's, 'g> State<'tcx, 's, 'g> {
    fn merge(
        &mut self,
        mut state: Self,
        def: DefId,
        join: Join,
        graph: &mut Graph<'g>,
        context: &mut facts::Context<'tcx, 's, 'g>,
    ) -> Result<usize, CapacityError> {
        self.basis = match (&self.basis, &state.basis) {
            (contracts::CheckBasis::Expression, contracts::CheckBasis::Expression) => {
                contracts::CheckBasis::Expression
            }
            (contracts::CheckBasis::Expression, contracts::CheckBasis::ControlFlow(_))
            | (contracts::CheckBasis::ControlFlow(_), contracts::CheckBasis::Expression) => {
                contracts::CheckBasis::ControlFlow(
                    crate::contracts::graph::evidence::Evidence::default(),
                )
            }
            (
                contracts::CheckBasis::ControlFlow(left),
                contracts::CheckBasis::ControlFlow(right),
            ) => contracts::CheckBasis::ControlFlow(graph.combine_evidence(
                crate::contracts::graph::sets::Combination::Intersection,
                *left,
                *right,
            )?),
        };
        let partitions: Vec<_> =
            Differences::from((&context.symbols, self.facts.symbols, state.facts.symbols))
                .filter_map(|(place, difference)| {
                    let Difference::Both(value, incoming) = difference else {
                        return None;
                    };
                    match (&graph[*value], &graph[*incoming]) {
                        (
                            ExprNode::Tokens { text, consumed },
                            ExprNode::Tokens {
                                text: incoming,
                                consumed: next,
                            },
                        ) if text == incoming && consumed != next => {
                            Some((*place, *text, *consumed, *next))
                        }
                        _ => None,
                    }
                })
                .collect();
        for (place, text, consumed, next) in partitions {
            let cursor = graph.intern_expr(ExprNode::Cursor {
                def,
                local: place.local,
            })?;
            for (state, count) in [(&mut *self, consumed), (&mut state, next)] {
                let replaced = state.facts.replace_symbols(count, cursor, graph, context)?;
                state.facts.invalidate(
                    GraphInvalidation::Local(place.local),
                    graph,
                    context,
                    facts::Scope::Live,
                    |place| replaced.get(&place).map(|_| ()),
                )?;
                state.facts.insert(
                    place,
                    graph.intern_expr(ExprNode::Tokens {
                        text,
                        consumed: cursor,
                    })?,
                    graph,
                    context,
                )?;
            }
        }
        context.escaped.overlay(
            &mut self.escaped_serializations,
            state.escaped_serializations,
        )?;
        self.invalidated
            .union(&state.invalidated, &mut context.paths)?;
        self.moved.intersection(&state.moved, &mut context.paths)?;
        let hull = match join {
            Join::Hull => Some(
                self.facts
                    .condition_differences(&state.facts, graph, context)?,
            ),
            Join::Widen => None,
        };
        let right = state.facts.conditions;
        let resolved = std::cell::OnceCell::new();
        let decision = |graph: &mut Graph<'g>| {
            *resolved.get_or_init(|| {
                if let Some((left_only, right_only)) = hull {
                    if let Some(condition) = facts::complementary(graph, left_only, right_only) {
                        return Ok(Some(condition));
                    }
                    for condition in graph.scan(left_only) {
                        if graph.truth(condition, &right)? == Truth::Refuted {
                            return Ok(Some(condition));
                        }
                    }
                }
                Ok::<_, CapacityError>(None)
            })
        };
        self.protocols.merge_with(
            &mut context.protocols,
            graph,
            &state.protocols,
            |graph, left, right| {
                if left == right {
                    return Ok(left);
                }
                let selector = decision(graph)?;
                graph.join_flow(left, right, join, selector)
            },
        )?;
        self.values
            .intersection(&state.values, &mut context.paths)?;
        self.guards
            .intersection(&state.guards, &mut context.paths)?;
        let changes: Vec<_> =
            Differences::from((&context.symbols, self.facts.symbols, state.facts.symbols))
                .map(|(key, change)| {
                    (
                        *key,
                        match change {
                            Difference::Left(value) => Difference::Left(*value),
                            Difference::Right(value) => Difference::Right(*value),
                            Difference::Both(left, right) => Difference::Both(*left, *right),
                        },
                    )
                })
                .collect();
        for (key, change) in changes {
            match change {
                Difference::Left(_) => {
                    self.facts.remove(&key, graph, context)?;
                }
                Difference::Right(_) => {}
                Difference::Both(value, incoming) => {
                    let result = match decision(graph)? {
                        Some(condition) => {
                            graph.intern_expr(ExprNode::Select(condition, value, incoming))?
                        }
                        _ => graph.join(value, incoming, join)?,
                    };
                    self.facts.insert(key, result, graph, context)?;
                }
            }
        }
        let union = match hull {
            Some((left_only, right_only)) => {
                context.join_conditions(&left_only, &right_only, graph)?
            }
            None => None,
        };
        self.facts.merge(&state.facts, union, graph, context)
    }

    fn expression(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        place: Place<'tcx>,
        graph: &mut Graph<'g>,
        context: &mut facts::Context<'tcx, 's, 'g>,
    ) -> Result<ExprId<'g>, CapacityError> {
        let mut place = context.paths.resolve(&self.values, tcx, place);
        while let ty::Ref(..) = place.ty(&body.local_decls, tcx).ty.kind() {
            place = context.paths.resolve(
                &self.values,
                tcx,
                place.project_deeper(&[ProjectionElem::Deref], tcx),
            );
        }
        let tracked = self.facts.tracked(place, context);
        for written in self
            .invalidated
            .conflicting_writes(place, tcx, body, &mut context.paths)
        {
            match tracked {
                Some((key, _))
                    if key.local == written.local
                        && key.projection.starts_with(written.projection) => {}
                _ => return graph.intern_expr(ExprNode::Unknown),
            }
        }
        let tracked = tracked.filter(|(_, value)| match graph[*value] {
            ExprNode::Unknown => false,
            _ => true,
        });
        let (mut expression, consumed) = match tracked {
            None => {
                let (origin, consumed) = context.names.origin(tcx, place, &context.paths, graph)?;
                (graph.intern_expr(ExprNode::Opaque(origin))?, consumed)
            }
            Some((key, value)) => (value, key.projection.len()),
        };
        let projections = place.projection.iter().enumerate().skip(consumed);
        for (index, projection) in projections {
            expression = match projection {
                ProjectionElem::Deref => {
                    let base = Place {
                        local: place.local,
                        projection: tcx.mk_place_elems(&place.projection[..index]),
                    };
                    match base.ty(&body.local_decls, tcx).ty.kind() {
                        ty::Ref(..) => expression,
                        _ => graph.intern_expr(ExprNode::Unknown)?,
                    }
                }
                ProjectionElem::Downcast(_, variant) => graph.downcast(expression, variant.index()),
                ProjectionElem::Field(index, _) => graph.field(expression, index.index())?,
                ProjectionElem::Index(local) => {
                    let index = self.expression(tcx, body, Place::from(local), graph, context)?;
                    graph.intern_expr(ExprNode::Element(expression, index))?
                }
                ProjectionElem::ConstantIndex {
                    offset,
                    from_end: false,
                    ..
                } => {
                    let index = graph.intern_expr(ExprNode::Number(u128::from(offset)))?;
                    graph.intern_expr(ExprNode::Element(expression, index))?
                }
                ProjectionElem::ConstantIndex { from_end: true, .. } => {
                    let index = graph.intern_expr(ExprNode::Unknown)?;
                    graph.intern_expr(ExprNode::Element(expression, index))?
                }
                _ => graph.intern_expr(ExprNode::Unknown)?,
            };
        }
        Ok(expression)
    }

    fn argument(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        operand: &Operand<'tcx>,
        graph: &mut Graph<'g>,
        context: &mut facts::Context<'tcx, 's, 'g>,
    ) -> Result<ExprId<'g>, CapacityError> {
        let node = match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                return self.expression(tcx, body, *place, graph, context);
            }
            Operand::Constant(constant) => {
                let ty = constant.const_.ty();
                if let ty::FnDef(def, args) = ty.kind() {
                    let instance = context.captures.capture_instance(
                        body.typing_env(tcx),
                        *def,
                        args.skip_binder(),
                    )?;
                    return graph.intern_expr(ExprNode::Function(instance));
                }

                if let ty::Uint(_) | ty::Int(_) | ty::Bool = ty.kind() {
                    return graph.intern_expr(
                        match constant
                            .const_
                            .try_eval_scalar_int(tcx, body.typing_env(tcx))
                        {
                            Some(value) => ExprNode::Number(value.to_bits_unchecked()),
                            None => ExprNode::Unknown,
                        },
                    );
                }
                if ty.is_char()
                    && let Some(value) = constant
                        .const_
                        .try_eval_scalar_int(tcx, body.typing_env(tcx))
                {
                    let value = char::from_u32(value.to_bits_unchecked() as u32)
                        .expect("a char constant is a Unicode scalar");
                    let text = graph.intern_value(value.to_string().as_str())?;
                    return graph.intern_expr(ExprNode::Text(text));
                }
                if let ty::Ref(_, inner, _) = ty.kind()
                    && inner.is_str()
                    && let Ok(value) =
                        constant
                            .const_
                            .eval(tcx, body.typing_env(tcx), constant.span)
                    && let Some(bytes) = value.try_get_slice_bytes_for_diagnostics(tcx)
                    && let Ok(text) = std::str::from_utf8(bytes)
                {
                    let text = graph.intern_value(text)?;
                    return graph.intern_expr(ExprNode::Text(text));
                }
                if let rustc_middle::mir::Const::Unevaluated(value, _) = constant.const_
                    && let None = value.promoted
                    && let rustc_hir::def::DefKind::Const | rustc_hir::def::DefKind::AssocConst =
                        tcx.def_kind(value.def)
                {
                    let args = value
                        .args
                        .iter()
                        .map(|argument| context.captures.capture_generic(argument))
                        .collect::<Result<Vec<_>, _>>()?;
                    let instance =
                        graph.instance_with_args(value.def, args, crate::values::Dispatch::Item)?;
                    return graph.intern_expr(ExprNode::Global(instance));
                }
                if let rustc_middle::mir::Const::Val(
                    rustc_middle::mir::ConstValue::Scalar(
                        rustc_middle::mir::interpret::Scalar::Ptr(pointer, _),
                    ),
                    _,
                ) = constant.const_
                {
                    let (provenance, offset) = pointer.prov_and_relative_offset();
                    match tcx.global_alloc(provenance.alloc_id()) {
                        rustc_middle::mir::interpret::GlobalAlloc::Function { instance } => {
                            let instance = context.captures.capture_instance(
                                body.typing_env(tcx),
                                instance.def_id(),
                                instance.args,
                            )?;
                            return graph.intern_expr(ExprNode::Function(instance));
                        }
                        rustc_middle::mir::interpret::GlobalAlloc::Static(def)
                            if let rustc_hir::def::DefKind::Static {
                                mutability: rustc_hir::Mutability::Not,
                                ..
                            } = tcx.def_kind(def)
                                && let Some(()) = frozen(
                                    tcx,
                                    body,
                                    tcx.type_of(def).instantiate_identity().skip_normalization(),
                                    &mut context.frozen,
                                ) =>
                        {
                            let args = crate::values::GenericsId::EMPTY;
                            let instance = graph.intern_value(crate::values::InstanceNode {
                                def,
                                args,
                                dispatch: crate::values::Dispatch::Item,
                            })?;
                            let value = graph.intern_expr(ExprNode::Global(instance))?;
                            return match offset.bytes() {
                                0 => Ok(value),
                                _ => {
                                    let index = graph.intern_expr(ExprNode::Unknown)?;
                                    graph.intern_expr(ExprNode::Element(value, index))
                                }
                            };
                        }
                        _ => {}
                    }
                }
                ExprNode::Unknown
            }
            Operand::RuntimeChecks(_) => ExprNode::Unknown,
        };
        graph.intern_expr(node)
    }

    fn widen(
        &mut self,
        value: ExprId<'g>,
        size: rustc_abi::Size,
        graph: &mut Graph<'g>,
        context: &mut facts::Context<'tcx, 's, 'g>,
    ) -> Result<ExprId<'g>, CapacityError> {
        let upper = size.unsigned_int_max();
        Ok(match graph[value] {
            ExprNode::Number(_) => value,
            ExprNode::Range(range) if range.upper <= upper => value,
            _ if let Some(()) = graph.known(contracts::graph::NodeId::Expr(value)) => {
                let maximum = graph.intern_expr(ExprNode::Number(upper))?;
                let bound = graph.intern_condition(ConditionNode::Compare(
                    Order::LessEqual,
                    value,
                    maximum,
                ))?;
                self.facts.condition(bound, graph, context)?;
                value
            }
            _ => graph.intern_expr(ExprNode::Range(contracts::Interval { lower: 0, upper }))?,
        })
    }

    fn rvalue(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        rvalue: &Rvalue<'tcx>,
        graph: &mut Graph<'g>,
        context: &mut facts::Context<'tcx, 's, 'g>,
    ) -> Result<ExprId<'g>, CapacityError> {
        let node = match rvalue {
            Rvalue::Use(operand, _) => return self.argument(tcx, body, operand, graph, context),
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => {
                return self.expression(tcx, body, *place, graph, context);
            }
            Rvalue::Discriminant(place) => {
                let ty::Adt(adt, _) = place.ty(&body.local_decls, tcx).ty.kind() else {
                    return graph.intern_expr(ExprNode::Unknown);
                };
                let value = self.expression(tcx, body, *place, graph, context)?;
                let mut discriminants = adt.discriminants(tcx).collect::<Vec<_>>();
                let Some((_, last)) = discriminants.pop() else {
                    return graph.intern_expr(ExprNode::Unknown);
                };
                let mut result = graph.intern_expr(ExprNode::Number(last.val))?;
                let preceding = discriminants.into_iter().rev();
                for (variant, discriminant) in preceding {
                    let condition =
                        graph.intern_condition(ConditionNode::Variant(value, variant.index()))?;
                    let number = graph.intern_expr(ExprNode::Number(discriminant.val))?;
                    result = graph.intern_expr(ExprNode::Select(condition, number, result))?;
                }
                return Ok(result);
            }
            Rvalue::Cast(CastKind::IntToInt, operand, target) => {
                let source = operand.ty(&body.local_decls, tcx);
                if let (ty::Uint(_), ty::Uint(_)) = (source.kind(), target.kind()) {
                    let from = source.int_size_and_signed(tcx).0;
                    let to = target.int_size_and_signed(tcx).0;
                    if from <= to {
                        let value = self.argument(tcx, body, operand, graph, context)?;
                        if from == to {
                            return Ok(value);
                        }
                        return self.widen(value, from, graph, context);
                    }
                }
                ExprNode::Unknown
            }
            Rvalue::Cast(CastKind::PointerCoercion(..), operand, target) => {
                let value = self.argument(tcx, body, operand, graph, context)?;
                match target.peel_refs().kind() {
                    ty::Dynamic(..) => {
                        let ty = context
                            .captures
                            .capture_type(operand.ty(&body.local_decls, tcx).peel_refs())?;
                        match graph[ty] {
                            crate::values::TypeNode::Unknown => return Ok(value),
                            _ => ExprNode::Typed(ty, value),
                        }
                    }
                    _ => return Ok(value),
                }
            }
            Rvalue::UnaryOp(UnOp::PtrMetadata, operand) => {
                match operand.ty(&body.local_decls, tcx).kind() {
                    ty::Ref(_, pointee, _) | ty::RawPtr(pointee, _)
                        if let ty::Slice(_) | ty::Str = pointee.kind() =>
                    {
                        ExprNode::Length(self.argument(tcx, body, operand, graph, context)?)
                    }
                    _ => ExprNode::Unknown,
                }
            }
            Rvalue::UnaryOp(UnOp::Not, operand) if operand.ty(&body.local_decls, tcx).is_bool() => {
                let value = self.argument(tcx, body, operand, graph, context)?;
                ExprNode::Test(graph.from_expr(value, 0)?)
            }
            Rvalue::BinaryOp(op, operands) => {
                let ty = operands.0.ty(&body.local_decls, tcx);
                let signed_order = match (ty.kind(), op) {
                    (ty::Uint(_) | ty::Bool, _) | (ty::Int(_), BinOp::Eq | BinOp::Ne) => None,
                    (ty::Int(_), BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge) => {
                        Some(ty.int_size_and_signed(tcx).0)
                    }
                    _ => return graph.intern_expr(ExprNode::Unknown),
                };
                let left = self.argument(tcx, body, &operands.0, graph, context)?;
                let right = self.argument(tcx, body, &operands.1, graph, context)?;
                let (left, right) = match signed_order {
                    Some(size) => (
                        signed_rank(graph, left, size)?,
                        signed_rank(graph, right, size)?,
                    ),
                    None => (left, right),
                };
                let condition = match op {
                    BinOp::Add | BinOp::Sub | BinOp::AddWithOverflow | BinOp::SubWithOverflow => {
                        let ty::Uint(integer) = *operands.0.ty(&body.local_decls, tcx).kind()
                        else {
                            unreachable!("integer arithmetic has unsigned operands here")
                        };
                        let arithmetic = match op {
                            BinOp::Add | BinOp::AddWithOverflow => {
                                contracts::Arithmetic::Add(integer)
                            }
                            BinOp::Sub | BinOp::SubWithOverflow => {
                                contracts::Arithmetic::Subtract(integer)
                            }
                            _ => unreachable!("matched arithmetic operations"),
                        };
                        let value =
                            graph.intern_expr(ExprNode::Arithmetic(arithmetic, left, right))?;
                        return match op {
                            BinOp::AddWithOverflow | BinOp::SubWithOverflow => {
                                let unknown = graph.intern_expr(ExprNode::Unknown)?;
                                let values = crate::sequence::Sequences::from_iter(
                                    graph.as_mut(),
                                    [value, unknown],
                                )?;
                                graph.intern_expr(ExprNode::Aggregate(values))
                            }
                            _ => Ok(value),
                        };
                    }
                    BinOp::Lt => ConditionNode::Compare(Order::Less, left, right),
                    BinOp::Le => ConditionNode::Compare(Order::LessEqual, left, right),
                    BinOp::Gt => ConditionNode::Compare(Order::Less, right, left),
                    BinOp::Ge => ConditionNode::Compare(Order::LessEqual, right, left),
                    BinOp::Eq => ConditionNode::Compare(Order::Equal, left, right),
                    BinOp::Ne => ConditionNode::Compare(Order::NotEqual, left, right),
                    _ => return graph.intern_expr(ExprNode::Unknown),
                };
                ExprNode::Test(graph.intern_condition(condition)?)
            }
            Rvalue::Aggregate(kind, operands) => {
                let fields = operands
                    .iter()
                    .map(|operand| self.argument(tcx, body, operand, graph, context))
                    .collect::<Result<Vec<_>, _>>()?;
                let fields = crate::sequence::Sequences::from_iter(graph.as_mut(), fields)?;
                match **kind {
                    AggregateKind::Adt(def, variant, ..) if tcx.adt_def(def).is_enum() => {
                        ExprNode::Variant(def, variant.index(), fields)
                    }
                    AggregateKind::Adt(def, ..) if tcx.adt_def(def).is_struct() => {
                        ExprNode::Aggregate(fields)
                    }
                    AggregateKind::Closure(def, args) => {
                        let captures = args.as_closure().upvar_tys();
                        for capture in captures.iter() {
                            match capture.kind() {
                                ty::Ref(_, inner, rustc_hir::Mutability::Not) => {
                                    if let None = frozen(tcx, body, *inner, &mut context.frozen) {
                                        return graph.intern_expr(ExprNode::Unknown);
                                    }
                                }
                                ty::Ref(_, _, rustc_hir::Mutability::Mut) | ty::RawPtr(..) => {
                                    return graph.intern_expr(ExprNode::Unknown);
                                }
                                _ => {
                                    if let None = frozen(tcx, body, capture, &mut context.frozen) {
                                        return graph.intern_expr(ExprNode::Unknown);
                                    }
                                }
                            }
                        }
                        ExprNode::Closure(def, fields)
                    }
                    AggregateKind::Tuple | AggregateKind::Array(_) => ExprNode::Aggregate(fields),
                    _ => ExprNode::Unknown,
                }
            }
            _ => ExprNode::Unknown,
        };
        graph.intern_expr(node)
    }

    fn operand(
        &self,
        tcx: TyCtxt<'tcx>,
        operand: &Operand<'tcx>,
        paths: &places::Paths<'tcx, 's>,
    ) -> Option<Value<'tcx>> {
        match operand {
            Operand::Copy(place) | Operand::Move(place) => {
                let place = paths.resolve(&self.values, tcx, *place);
                Some(paths.value(&self.values, place))
            }
            Operand::Constant(constant) => constant.const_.try_to_scalar_int().map(|value| {
                Value::Direct(ValueKind::Known(Fact::Scalar(value.to_bits_unchecked())))
            }),
            Operand::RuntimeChecks(_) => None,
        }
    }

    fn branch_condition(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        discriminant: &Operand<'tcx>,
        symbol: ExprId<'g>,
        chosen: u128,
        discriminants: &mut DiscriminantIndex,
        graph: &mut Graph<'g>,
        context: &mut facts::Context<'tcx, 's, 'g>,
    ) -> Result<ConditionId<'g>, CapacityError> {
        if let Some(Value::Direct(ValueKind::Discriminant(place))) =
            self.operand(tcx, discriminant, &context.paths)
            && let ty::Adt(adt, _) = place.ty(&body.local_decls, tcx).ty.kind()
            && let Some(variant) = discriminants.variant(tcx, adt.did(), chosen)
        {
            let value = self.expression(tcx, body, place, graph, context)?;
            return graph.intern_condition(ConditionNode::Variant(value, variant.index()));
        }
        graph.from_expr(symbol, chosen)
    }

    fn forget(
        &mut self,
        place: Place<'tcx>,
        graph: &mut Graph<'g>,
        context: &mut facts::Context<'tcx, 's, 'g>,
    ) -> Result<(), CapacityError> {
        self.protocols.forget(&mut context.protocols, place)?;
        self.moved
            .remove_prefix(place, places::Overlap::Prefixes, &mut context.paths)?;
        self.invalidated
            .remove_prefix(place, places::Overlap::Descendants, &mut context.paths)?;
        if let Some(_) = place
            .projection
            .iter()
            .find(|projection| *projection == ProjectionElem::Deref)
        {
            // An unresolved pointer may alias any tracked location.
            self.values = Default::default();
            self.guards = Default::default();
            self.facts = Default::default();
            return Ok(());
        }
        self.facts.invalidate(
            GraphInvalidation::Local(place.local),
            graph,
            context,
            facts::Scope::All,
            |_| None,
        )?;
        self.facts.forget_places(place, graph, context)?;
        self.values.forget(place, &mut context.paths)?;
        self.guards.forget(place, &mut context.paths)?;
        Ok(())
    }

    fn assign(
        &mut self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        destination: Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        graph: &mut Graph<'g>,
        context: &mut facts::Context<'tcx, 's, 'g>,
    ) -> Result<(), CapacityError> {
        let destination = context.paths.resolve(&self.values, tcx, destination);
        let projections = destination.projection.iter().enumerate();
        for (index, projection) in projections {
            if let ProjectionElem::Field(..) = projection {
                let base = Place {
                    local: destination.local,
                    projection: tcx.mk_place_elems(&destination.projection[..index]),
                };
                if let ty::Adt(adt, _) = *base.ty(&body.local_decls, tcx).ty.kind()
                    && adt.is_union()
                {
                    self.values = Default::default();
                    self.guards = Default::default();
                    self.facts.clear_symbols(graph, context)?;
                    self.facts.clear_conditions(graph, context)?;
                }
            }
        }
        let mut symbol = self.rvalue(tcx, body, rvalue, graph, context)?;
        let mut fields = Vec::new();
        let value = match rvalue {
            Rvalue::Use(operand, _) => {
                if let Operand::Copy(source) | Operand::Move(source) = operand {
                    let source = context.paths.resolve(&self.values, tcx, *source);
                    for (place, value) in self.values.descendants(source, &context.paths) {
                        if place.local == source.local
                            && place.projection.starts_with(source.projection)
                            && place.projection.len() > source.projection.len()
                        {
                            fields.push((
                                destination.project_deeper(
                                    &place.projection[source.projection.len()..],
                                    tcx,
                                ),
                                value,
                            ));
                        }
                    }
                }
                self.operand(tcx, operand, &context.paths)
            }
            Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => Some(Value::Direct(
                ValueKind::Reference(context.paths.resolve(&self.values, tcx, *place)),
            )),
            Rvalue::Discriminant(place) => {
                let place = context.paths.resolve(&self.values, tcx, *place);
                let place = match context.paths.value(&self.values, place) {
                    Value::Direct(ValueKind::Origin(origin)) => origin,
                    _ => place,
                };
                Some(Value::Direct(ValueKind::Discriminant(place)))
            }
            Rvalue::UnaryOp(UnOp::Not, operand) if operand.ty(&body.local_decls, tcx).is_bool() => {
                self.operand(tcx, operand, &context.paths)
                    .map(|value| match value {
                        Value::Direct(value) => Value::Negated(value),
                        Value::Negated(value) => Value::Direct(value),
                    })
            }
            Rvalue::Aggregate(kind, operands) => match **kind {
                AggregateKind::Adt(def, variant, args, _, _) => {
                    let adt = tcx.adt_def(def);
                    if adt.is_union() {
                        self.values = Default::default();
                        self.guards = Default::default();
                        self.facts.clear_symbols(graph, context)?;
                        self.facts.clear_conditions(graph, context)?;
                        return Ok(());
                    }
                    let base = if adt.is_enum() {
                        destination.project_deeper(&[ProjectionElem::Downcast(None, variant)], tcx)
                    } else {
                        destination
                    };
                    for (index, operand) in operands.iter_enumerated() {
                        if let Some(value) = self.operand(tcx, operand, &context.paths) {
                            let field = FieldIdx::from_usize(index.index());
                            let ty = adt.variant(variant).fields[field]
                                .ty(tcx, args)
                                .skip_normalization();
                            fields.push((
                                base.project_deeper(&[ProjectionElem::Field(field, ty)], tcx),
                                value,
                            ));
                        }
                    }
                    Some(Value::Direct(ValueKind::Known(Fact::Variant(variant))))
                }
                _ => None,
            },
            _ => None,
        };
        self.forget(destination, graph, context)?;
        symbol = self.facts.invalidate_expression(
            symbol,
            GraphInvalidation::Local(destination.local),
            graph,
            context,
        )?;
        if let Some(value) = value {
            self.values.insert(destination, value, &mut context.paths)?;
        }
        for (place, value) in fields {
            self.values.insert(place, value, &mut context.paths)?;
        }
        self.facts.insert(destination, symbol, graph, context)?;
        Ok(())
    }

    fn refine(
        &mut self,
        place: Place<'tcx>,
        fact: Fact,
        paths: &mut places::Paths<'tcx, 's>,
    ) -> Result<Option<()>, CapacityError> {
        if let Value::Direct(ValueKind::Known(known)) = paths.value(&self.values, place)
            && known != fact
        {
            return Ok(None);
        }
        self.values
            .insert(place, Value::Direct(ValueKind::Known(fact)), paths)?;
        self.guards.insert(place, fact, paths)?;
        Ok(Some(()))
    }
}

#[derive(Clone, Copy)]
enum Method {
    Predicate(VariantIdx),
    Extract(VariantIdx),
    Borrow,
    Take,
    Replace,
    VecPush,
}

fn method(tcx: TyCtxt<'_>, def: DefId) -> Option<Method> {
    if let Some(()) = crate::standard::vec_push(tcx, def) {
        return Some(Method::VecPush);
    }
    let owner = crate::standard::method_owner(tcx, def)?;
    let name = tcx.item_name(def);
    let name = name.as_str();
    match owner {
        crate::standard::OptionOrResult::Option => match name {
            "is_some" => Some(Method::Predicate(VariantIdx::from_usize(1))),
            "is_none" => Some(Method::Predicate(VariantIdx::from_usize(0))),
            "unwrap" | "expect" | "unwrap_unchecked" => {
                Some(Method::Extract(VariantIdx::from_usize(1)))
            }
            "as_ref" | "as_mut" => Some(Method::Borrow),
            "take" => Some(Method::Take),
            "replace" => Some(Method::Replace),
            _ => None,
        },
        crate::standard::OptionOrResult::Result => match name {
            "is_ok" => Some(Method::Predicate(VariantIdx::from_usize(0))),
            "is_err" => Some(Method::Predicate(VariantIdx::from_usize(1))),
            "unwrap" | "expect" | "unwrap_unchecked" => {
                Some(Method::Extract(VariantIdx::from_usize(0)))
            }
            "unwrap_err" | "expect_err" | "unwrap_err_unchecked" => {
                Some(Method::Extract(VariantIdx::from_usize(1)))
            }
            "as_ref" | "as_mut" => Some(Method::Borrow),
            _ => None,
        },
    }
}

/// Signed MIR scalars are stored as their bit patterns. Flipping the sign bit maps signed
/// order onto the graph's unsigned order, including at the minimum representable value.
fn signed_rank<'g>(
    graph: &mut Graph<'g>,
    value: ExprId<'g>,
    size: rustc_abi::Size,
) -> Result<ExprId<'g>, CapacityError> {
    let sign = size.truncate(size.signed_int_min() as u128);
    if let ExprNode::Number(bits) = graph[value] {
        return graph.intern_expr(ExprNode::Number(bits ^ sign));
    }
    let sign = graph.intern_expr(ExprNode::Number(sign))?;
    graph.intern_expr(ExprNode::Arithmetic(
        contracts::Arithmetic::WrappingSubtract(size.bits()),
        value,
        sign,
    ))
}

fn addition_condition<'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    graph: &mut Graph<'g>,
    left: ExprId<'g>,
    right: ExprId<'g>,
) -> Result<ConditionId<'g>, CapacityError> {
    if let ty::Uint(ty::UintTy::Usize) = ty.kind()
        && let Some(_) = graph.match_end_text(left, right)
    {
        // The match and its width form a byte range inside one str.
        return graph.intern_condition(ConditionNode::Compare(Order::Equal, left, left));
    }
    let (size, signed) = ty.int_size_and_signed(tcx);
    let (left, right) = match graph[left] {
        ExprNode::Number(_) => (right, left),
        _ => (left, right),
    };
    if let ExprNode::Number(0) = graph[right] {
        return graph.intern_condition(ConditionNode::Compare(Order::Equal, right, right));
    }
    let maximum = size.unsigned_int_max();
    let constant = match graph[right] {
        ExprNode::Number(bits) => Some(bits),
        _ => None,
    };
    let bound = match constant {
        Some(bits) => graph.intern_expr(ExprNode::Number(size.truncate(!bits)))?,
        None => {
            let maximum = graph.intern_expr(ExprNode::Number(maximum))?;
            let operation = match *ty.kind() {
                ty::Uint(unsigned) => contracts::Arithmetic::Subtract(unsigned),
                _ => contracts::Arithmetic::WrappingSubtract(size.bits()),
            };
            graph.intern_expr(ExprNode::Arithmetic(operation, maximum, right))?
        }
    };
    if !signed {
        return graph.intern_condition(ConditionNode::Compare(Order::LessEqual, left, bound));
    }
    let rank = signed_rank(graph, left, size)?;
    let below_bound =
        graph.intern_condition(ConditionNode::Compare(Order::LessEqual, rank, bound))?;
    // For a nonnegative addend the upper bound is MAX - addend. A negative
    // addend requires rank >= -addend, equivalently rank > !addend.
    match constant {
        Some(bits) if size.sign_extend(bits) < 0 => graph.negate(below_bound),
        Some(_) => Ok(below_bound),
        None => {
            let right_rank = signed_rank(graph, right, size)?;
            let zero_rank = graph.intern_expr(ExprNode::Number(
                size.truncate(size.signed_int_min() as u128),
            ))?;
            let nonnegative = graph.intern_condition(ConditionNode::Compare(
                Order::LessEqual,
                zero_rank,
                right_rank,
            ))?;
            let nonnegative = graph.intern_expr(ExprNode::Test(nonnegative))?;
            let below_bound = graph.intern_expr(ExprNode::Test(below_bound))?;
            graph.intern_condition(ConditionNode::Compare(
                Order::Equal,
                nonnegative,
                below_bound,
            ))
        }
    }
}

fn shift_condition<'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    value_ty: ty::Ty<'tcx>,
    count_ty: ty::Ty<'tcx>,
    graph: &mut Graph<'g>,
    count: ExprId<'g>,
) -> Result<ConditionId<'g>, CapacityError> {
    let bits = u128::from(value_ty.int_size_and_signed(tcx).0.bits());
    let (size, signed) = count_ty.int_size_and_signed(tcx);
    if !signed {
        let bits = graph.intern_expr(ExprNode::Number(bits))?;
        return graph.intern_condition(ConditionNode::Compare(Order::Less, count, bits));
    }
    let rank = signed_rank(graph, count, size)?;
    let sign = size.truncate(size.signed_int_min() as u128);
    let zero_rank = graph.intern_expr(ExprNode::Number(sign))?;
    let nonnegative =
        graph.intern_condition(ConditionNode::Compare(Order::LessEqual, zero_rank, rank))?;
    if bits > size.signed_int_max() as u128 {
        return Ok(nonnegative);
    }
    let limit = graph.intern_expr(ExprNode::Number(sign + bits))?;
    let below_width = graph.intern_condition(ConditionNode::Compare(Order::Less, rank, limit))?;
    let yes = graph.intern_expr(ExprNode::Test(below_width))?;
    let no = graph.intern_expr(ExprNode::Number(0))?;
    let valid = graph.intern_expr(ExprNode::Select(nonnegative, yes, no))?;
    graph.from_expr(valid, 1)
}

struct Field<'tcx> {
    base: Place<'tcx>,
    owner: StateType,
    index: FieldIdx,
}

fn field<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, place: Place<'tcx>) -> Option<Field<'tcx>> {
    let (ProjectionElem::Field(index, _), prefix) = place.projection.split_last()? else {
        return None;
    };
    let base = Place {
        local: place.local,
        projection: tcx.mk_place_elems(prefix),
    };
    let owner = StateType::from_ty(tcx, body, base.ty(&body.local_decls, tcx).ty)?;
    Some(Field {
        base,
        owner,
        index: *index,
    })
}

pub fn describe(tcx: TyCtxt<'_>, adt: DefId, field: FieldIdx, fact: Fact) -> String {
    let field = &tcx.adt_def(adt).non_enum_variant().fields[field];
    let value = match fact {
        Fact::Scalar(value) => {
            if tcx
                .type_of(field.did)
                .instantiate_identity()
                .skip_normalization()
                .is_bool()
            {
                match value {
                    0 => "false".into(),
                    1 => "true".into(),
                    _ => value.to_string(),
                }
            } else {
                value.to_string()
            }
        }
        Fact::Variant(variant) => match *tcx
            .type_of(field.did)
            .instantiate_identity()
            .skip_normalization()
            .kind()
        {
            ty::Adt(adt, _) => adt.variant(variant).name.to_string(),
            _ => "an enum variant whose type could not be resolved".into(),
        },
    };
    format!(
        "{}.{} = {value}",
        crate::diagnostics::item(tcx, adt),
        field.name
    )
}

fn extract<'tcx, 's, E, C, T, F>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    state: &State<'tcx, 's, '_>,
    place: Place<'tcx>,
    required: VariantIdx,
    span: Span,
    observations: &mut Observations<'_, E, C, T, F>,
    paths: &places::Paths<'tcx, 's>,
) {
    let ty::Adt(adt, _) = *place.ty(&body.local_decls, tcx).ty.peel_refs().kind() else {
        return;
    };
    let required_name = adt.variant(required).name.to_string();
    match paths.value(&state.values, place) {
        Value::Direct(ValueKind::Known(Fact::Variant(observed))) if observed != required => {
            observations.findings.push(Finding {
                span,
                evidence: CompilerEvidence::InvalidVariant {
                    observed: adt.variant(observed).name.to_string(),
                    required: format!("requires {required_name}"),
                },
            });
        }
        Value::Direct(ValueKind::Known(Fact::Variant(_))) => {}
        _ => {
            let Some(Field {
                base,
                owner,
                index: payload,
            }) = field(tcx, body, place)
            else {
                return;
            };
            let mut guards = Vec::new();
            for (guard, fact) in state.guards.descendants(base, paths) {
                if let Some(Field {
                    base: guard_base,
                    owner: guard_owner,
                    index,
                }) = field(tcx, body, guard)
                    && guard_base == base
                    && guard_owner == owner
                    && index != payload
                {
                    guards.push((index, fact));
                }
            }
            if guards.is_empty() {
                return;
            }
            guards.sort_by_key(|(index, _)| *index);
            let guard = guards
                .iter()
                .map(|(index, fact)| describe(tcx, owner.definition, *index, *fact))
                .collect::<Vec<_>>()
                .join(" and ");
            observations.findings.push(Finding {
                span,
                evidence: CompilerEvidence::UnencodedInvariant {
                    guard,
                    required: describe(tcx, owner.definition, payload, Fact::Variant(required)),
                },
            });
            // A relationship with an external predicate cannot be applied to every constructor.
            if guards.len() == paths.table().len(state.guards.values) {
                observations.invariants.push(Invariant {
                    owner,
                    guards,
                    field: payload,
                    required,
                    span,
                });
            }
        }
    }
}

fn scalar<'tcx, 's>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    state: &State<'tcx, 's, '_>,
    value: &Value<'tcx>,
    paths: &places::Paths<'tcx, 's>,
) -> Option<u128> {
    let base = match value {
        Value::Direct(base) | Value::Negated(base) => base,
    };
    let scalar = match base {
        ValueKind::Known(Fact::Scalar(value)) => Some(*value),
        ValueKind::Predicate { place, variant } => match paths.value(&state.values, *place) {
            Value::Direct(ValueKind::Known(Fact::Variant(known))) => {
                Some(u128::from(known == *variant))
            }
            _ => None,
        },
        ValueKind::Discriminant(place) => match paths.value(&state.values, *place) {
            Value::Direct(ValueKind::Known(Fact::Variant(variant))) => {
                match *place.ty(&body.local_decls, tcx).ty.kind() {
                    ty::Adt(adt, _) => Some(adt.discriminant_for_variant(tcx, variant).val),
                    _ => None,
                }
            }
            _ => None,
        },
        ValueKind::Known(Fact::Variant(_)) | ValueKind::Origin(_) | ValueKind::Reference(_) => None,
    };
    match value {
        Value::Direct(_) => scalar,
        Value::Negated(_) => scalar.map(|value| u128::from(value == 0)),
    }
}

fn switch<'tcx, 's>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    state: &mut State<'tcx, 's, '_>,
    value: &Value<'tcx>,
    chosen: u128,
    discriminants: &mut DiscriminantIndex,
    paths: &mut places::Paths<'tcx, 's>,
) -> Result<Option<()>, CapacityError> {
    let (value, chosen) = match value {
        Value::Direct(value) => (value, chosen),
        Value::Negated(value) => (value, u128::from(chosen == 0)),
    };
    match value {
        ValueKind::Known(Fact::Scalar(known)) if *known != chosen => Ok(None),
        ValueKind::Known(_) => Ok(Some(())),
        ValueKind::Origin(place) => state.refine(*place, Fact::Scalar(chosen), paths),
        ValueKind::Predicate { place, variant } => {
            let variant = if chosen == 0 {
                VariantIdx::from_usize(1 - variant.index())
            } else {
                *variant
            };
            state.refine(*place, Fact::Variant(variant), paths)
        }
        ValueKind::Discriminant(place) => {
            let ty::Adt(adt, _) = *place.ty(&body.local_decls, tcx).ty.kind() else {
                return Ok(Some(()));
            };
            let Some(variant) = discriminants.variant(tcx, adt.did(), chosen) else {
                return Ok(None);
            };
            state.refine(*place, Fact::Variant(variant), paths)
        }
        ValueKind::Reference(_) => Ok(Some(())),
    }
}

pub fn analyze<'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    mut graph: &mut Graph<'g>,
    names: &[rustc_span::Symbol],
    sources: &crate::diagnostics::Sources,
) -> Result<
    Capture<'g, ExprId<'g>, ConditionId<'g>, TargetNode<'g>, crate::contracts::graph::FlowId<'g>>,
    CapacityError,
> {
    let values = crate::values::Values::share(graph.as_ref());
    facts::with_context(tcx, body, sources, values, |mut context| {
        let demand = demand::Demand::new(tcx, body);
        let source = std::sync::Arc::clone(&context.names.source);
        let dominators = body.basic_blocks.dominators();
        let mut headers: FxHashMap<BasicBlock, Vec<BasicBlock>> = FxHashMap::default();
        let order: Vec<_> = rustc_middle::mir::traversal::preorder(body)
            .map(|(block, _)| block)
            .collect();
        for &latch in &order {
            let successors = body.basic_blocks[latch].terminator().successors();
            for header in successors {
                if dominators.dominates(header, latch) {
                    headers.entry(header).or_default().push(latch);
                }
            }
        }
        let loops = crate::loops::Forest::new(&body.basic_blocks, dominators, &order, &headers);
        let mut incoming: FxHashMap<BasicBlock, StateId<'_>> = FxHashMap::default();
        let mut states = States::new();
        let mut prefix_maps =
            crate::persistent::Maps::<u128, StateId<'_>, crate::persistent::Ordered>::new();
        let mut initial = State::default();
        initial.protocols =
            crate::protocols::State::initial(&mut context.protocols, &mut graph, tcx, body, names)?;
        for local in body.args_iter() {
            initial.facts.insert(
                Place::from(local),
                graph.intern_expr(ExprNode::Argument(local.index() - 1))?,
                &graph,
                &mut context,
            )?;
        }
        let initial = states.intern(initial)?;
        let mut prefixes: IndexVec<BasicBlock, incoming::Incoming<'_, StateId<'_>>> =
            IndexVec::from_fn_n(
                |block| {
                    incoming::Incoming::new(match block {
                        START_BLOCK => Some(initial),
                        _ => None,
                    })
                },
                body.basic_blocks.len(),
            );
        let mut positions: IndexVec<BasicBlock, FxHashMap<BasicBlock, Vec<usize>>> =
            IndexVec::from_fn_n(|_| FxHashMap::default(), body.basic_blocks.len());
        let mut transparent_exits = FxHashMap::default();
        let predecessors = body.basic_blocks.predecessors().iter_enumerated();
        for (target, predecessors) in predecessors {
            if headers.len() > 1
                && let [source] = predecessors.as_slice()
                && let Some(outer) = loops[target].innermost
                && outer != target
                && let Some(inner) = loops[*source].innermost
                && loops[inner].parent == Some(outer)
            {
                let data = &body.basic_blocks[target];
                if let TerminatorKind::Goto { target: successor } = data.terminator().kind
                    && data
                        .statements
                        .iter()
                        .enumerate()
                        .all(|(statement_index, statement)| match statement.kind {
                            StatementKind::Assign(_) => demand
                                .assignment(Location {
                                    block: target,
                                    statement_index,
                                })
                                .is_none(),
                            StatementKind::SetDiscriminant { .. } | StatementKind::Intrinsic(_) => {
                                false
                            }
                            StatementKind::StorageLive(_)
                            | StatementKind::StorageDead(_)
                            | StatementKind::PlaceMention(_)
                            | StatementKind::FakeRead(_)
                            | StatementKind::AscribeUserType(..)
                            | StatementKind::Coverage(_)
                            | StatementKind::ConstEvalCounter
                            | StatementKind::Nop
                            | StatementKind::BackwardIncompatibleDropHint { .. } => true,
                        })
                {
                    transparent_exits.insert(target, successor);
                }
            }
            let predecessors = predecessors.iter().enumerate();
            for (position, predecessor) in predecessors {
                positions[target]
                    .entry(*predecessor)
                    .or_default()
                    .push(position);
            }
        }
        let mut edges: IndexVec<BasicBlock, FxHashMap<BasicBlock, StateId<'_>>> =
            IndexVec::from_fn_n(|_| FxHashMap::default(), body.basic_blocks.len());
        let mut pending = schedule::Schedule::new(
            &body.basic_blocks,
            body.basic_blocks.reverse_postorder(),
            START_BLOCK,
        );
        let mut events = FxHashMap::default();
        let mut work = Work::default();
        let mut discriminants = DiscriminantIndex::default();
        while let Some(block) = pending.pop() {
            let mut merged = prefixes[block].fold(&mut prefix_maps, |current, state| {
                let mut left = states[*current];
                let right = states[*state];
                work.merges = work.merges.saturating_add(1);
                work.attachments = work.attachments.saturating_add(left.merge(
                    right,
                    body.source.def_id(),
                    Join::Hull,
                    &mut graph,
                    &mut context,
                )?);
                *current = states.intern(left)?;
                Ok::<_, CapacityError>(())
            })?;
            if headers.contains_key(&block)
                && let (Some(previous), Some(next)) = (incoming.get(&block), &mut merged)
            {
                let mut widened = states[*previous];
                work.merges = work.merges.saturating_add(1);
                work.attachments = work.attachments.saturating_add(widened.merge(
                    states[*next],
                    body.source.def_id(),
                    Join::Widen,
                    &mut graph,
                    &mut context,
                )?);
                *next = states.intern(widened)?;
            }
            if incoming.get(&block) == merged.as_ref() {
                continue;
            }
            match merged {
                Some(state) => {
                    if incoming.insert(block, state).is_some()
                        && let Some(&target) = transparent_exits.get(&block)
                    {
                        // The preceding reachable visit installed empty observations and one
                        // unchanged edge. Keep its scheduled position so widening sees every update.
                        edges[block].insert(target, state);
                        for &position in &positions[target][&block] {
                            prefixes[target].replace(&mut prefix_maps, position, Some(state))?;
                        }
                        pending.changed(target);
                        work.nested_exit_forwards = work.nested_exit_forwards.saturating_add(1);
                        continue;
                    }
                }
                None => {
                    incoming.remove(&block);
                }
            }
            let mut successors = Vec::new();
            if let Some(state) = incoming.get(&block).copied() {
                let mut state = states[state];
                work.block_transfers = work.block_transfers.saturating_add(1);
                let mut observations = Observations::default();
                let data = &body.basic_blocks[block];
                let statements = data.statements.iter().enumerate();
                for (statement_index, statement) in statements {
                    work.statement_dispatches = work.statement_dispatches.saturating_add(1);
                    if let None = demand.assignment(Location {
                        block,
                        statement_index,
                    }) {
                        continue;
                    }
                    work.statement_transfers = work.statement_transfers.saturating_add(1);
                    match &statement.kind {
                        StatementKind::Assign(assignment) => {
                            let escaped = match &assignment.1 {
                                Rvalue::Ref(
                                    _,
                                    rustc_middle::mir::BorrowKind::Mut { .. },
                                    place,
                                )
                                | Rvalue::RawPtr(_, place) => {
                                    if let ty::Adt(adt, _) =
                                        place.ty(&body.local_decls, tcx).ty.kind()
                                    {
                                        observations.contracts.mutations.insert(adt.did());
                                    }
                                    Some(*place)
                                }
                                _ => None,
                            };
                            let writes = std::iter::once(assignment.0).chain(escaped);
                            for place in writes {
                                let projections = place.projection.iter().enumerate();
                                for (index, projection) in projections {
                                    if let ProjectionElem::Field(..) = projection {
                                        let base = Place {
                                            local: place.local,
                                            projection: tcx
                                                .mk_place_elems(&place.projection[..index]),
                                        };
                                        if let ty::Adt(adt, _) =
                                            base.ty(&body.local_decls, tcx).ty.kind()
                                        {
                                            observations.contracts.mutations.insert(adt.did());
                                        }
                                    }
                                }
                            }
                            let mut moves = Moves::default();
                            moves.visit_rvalue(
                                &assignment.1,
                                Location {
                                    block,
                                    statement_index,
                                },
                            );
                            let moved: Vec<_> = moves
                                .0
                                .into_iter()
                                .map(|place| context.paths.resolve(&state.values, tcx, place))
                                .collect();
                            let destination =
                                context.paths.resolve(&state.values, tcx, assignment.0);
                            if destination.local.index() > 0
                                && destination.local.index() <= body.arg_count
                            {
                                graph.record_argument_write(
                                    &mut observations.writes,
                                    destination.local.index() - 1,
                                )?;
                            }
                            if let Some(_) = destination
                                .projection
                                .iter()
                                .find(|projection| *projection == ProjectionElem::Deref)
                            {
                                let value = state.rvalue(
                                    tcx,
                                    body,
                                    &assignment.1,
                                    &mut graph,
                                    &mut context,
                                )?;
                                graph.functions(value, &mut observations.contracts.escapes)?;
                                if let Some(inputs) =
                                    graph.inputs(contracts::graph::NodeId::Expr(value))?
                                {
                                    observations.contracts.escaped_arguments.extend(inputs);
                                }
                                observations.contracts.behavior = contracts::Behavior::Unknown;
                                if destination.local.index() > body.arg_count {
                                    observations.writes = contracts::Writes::Unknown;
                                }
                            }
                            if let Rvalue::Discriminant(place) = &assignment.1 {
                                observations.contracts.inspections.push(state.expression(
                                    tcx,
                                    body,
                                    *place,
                                    &mut graph,
                                    &mut context,
                                )?);
                            }
                            state.assign(
                                tcx,
                                body,
                                assignment.0,
                                &assignment.1,
                                &mut graph,
                                &mut context,
                            )?;
                            for place in moved {
                                state.moved.insert(place, (), &mut context.paths)?;
                            }
                            if let Rvalue::Aggregate(kind, _) = &assignment.1
                                && let AggregateKind::Adt(owner, ..) = **kind
                                && tcx.adt_def(owner).is_struct()
                            {
                                observations.contracts.constructions.push(
                                    contracts::Construction {
                                        owner,
                                        value: state.expression(
                                            tcx,
                                            body,
                                            assignment.0,
                                            &mut graph,
                                            &mut context,
                                        )?,
                                        guards: state.facts.conditions.clone(),
                                    },
                                );
                            }
                        }
                        StatementKind::SetDiscriminant {
                            place,
                            variant_index,
                        } => {
                            let place = context.paths.resolve(&state.values, tcx, **place);
                            state.forget(place, &mut graph, &mut context)?;
                            state.values.insert(
                                place,
                                Value::Direct(ValueKind::Known(Fact::Variant(*variant_index))),
                                &mut context.paths,
                            )?;
                        }
                        StatementKind::Intrinsic(_) => {
                            observations.contracts.behavior = contracts::Behavior::Unknown;
                            observations.writes = contracts::Writes::Unknown;
                            state = State {
                                basis: state.basis,
                                ..State::default()
                            };
                        }
                        _ => {}
                    }
                }
                let terminator = data.terminator();
                match &terminator.kind {
                    TerminatorKind::SwitchInt { discr, targets } => {
                        let symbol = state.argument(tcx, body, discr, &mut graph, &mut context)?;
                        let symbol = match &graph[symbol] {
                            ExprNode::Test(_) => symbol,
                            _ if discr.ty(&body.local_decls, tcx).is_bool() => {
                                let condition = graph.from_expr(symbol, 1)?;
                                graph.intern_expr(ExprNode::Test(condition))?
                            }
                            _ => symbol,
                        };
                        observations.contracts.inspections.push(symbol);
                        if discr.ty(&body.local_decls, tcx).is_bool()
                            && let Some(check) = source.checks.get(&terminator.source_info.span)
                            && let Some(span) = crate::diagnostics::source_span(
                                tcx,
                                body.source.def_id(),
                                check.span,
                            )
                        {
                            observations.contracts.checks.push(contracts::Check {
                                basis: match state.basis {
                                    contracts::CheckBasis::Expression => {
                                        contracts::CheckBasis::Expression
                                    }
                                    contracts::CheckBasis::ControlFlow(evidence) => {
                                        contracts::CheckBasis::ControlFlow(
                                            graph.evidence_sequence(evidence)?,
                                        )
                                    }
                                },
                                loop_writes: None,
                                condition: graph.from_expr(
                                    symbol,
                                    match check.polarity {
                                        crate::diagnostics::CheckPolarity::Direct => 1,
                                        crate::diagnostics::CheckPolarity::Negated => 0,
                                    },
                                )?,
                                guards: state.facts.conditions.clone(),
                                span,
                            });
                        }
                        let value = state.operand(tcx, discr, &context.paths);
                        if let Some(value) = &value
                            && let Some(chosen) = scalar(tcx, body, &state, value, &context.paths)
                        {
                            let target = targets.target_for_value(chosen);
                            if let Some(()) = switch(
                                tcx,
                                body,
                                &mut state,
                                value,
                                chosen,
                                &mut discriminants,
                                &mut context.paths,
                            )? {
                                let condition = state.branch_condition(
                                    tcx,
                                    body,
                                    discr,
                                    symbol,
                                    chosen,
                                    &mut discriminants,
                                    &mut graph,
                                    &mut context,
                                )?;
                                let proof = graph.prove(condition, &state.facts.conditions)?;
                                if Truth::from(proof) != Truth::Refuted {
                                    if let crate::contracts::graph::evidence::Proof::Proven(
                                        evidence,
                                    ) = proof
                                        && evidence.0 != crate::contracts::graph::sets::SetId::EMPTY
                                    {
                                        state.basis = contracts::CheckBasis::ControlFlow(match state.basis {
                                        contracts::CheckBasis::Expression => evidence,
                                        contracts::CheckBasis::ControlFlow(previous) => graph.combine_evidence(crate::contracts::graph::sets::Combination::Union, previous, evidence)?,
                                    });
                                    }
                                    state.facts.condition(condition, &mut graph, &mut context)?;
                                    successors.push((target, state.clone()));
                                }
                            }
                        } else {
                            let mut choices = targets.iter().collect::<Vec<_>>();
                            let mut choice_values = FxHashSet::default();
                            for (key, _) in &choices {
                                choice_values.insert(*key);
                            }
                            let otherwise = match &value {
                                Some(
                                    Value::Direct(ValueKind::Predicate { .. }) | Value::Negated(_),
                                ) => (0..=1).find(|value| !choice_values.contains(value)),
                                Some(Value::Direct(ValueKind::Discriminant(place))) => {
                                    match *place.ty(&body.local_decls, tcx).ty.kind() {
                                        ty::Adt(adt, _) => {
                                            let remaining = adt
                                                .discriminants(tcx)
                                                .filter(|(_, discr)| {
                                                    !choice_values.contains(&discr.val)
                                                })
                                                .collect::<Vec<_>>();
                                            match remaining.as_slice() {
                                                [(_, discriminant)] => Some(discriminant.val),
                                                _ => None,
                                            }
                                        }
                                        _ => None,
                                    }
                                }
                                Some(Value::Direct(ValueKind::Origin(place)))
                                    if place.ty(&body.local_decls, tcx).ty.is_bool() =>
                                {
                                    (0..=1).find(|value| !choice_values.contains(value))
                                }
                                Some(Value::Direct(ValueKind::Known(Fact::Scalar(value))))
                                    if !choice_values.contains(value) =>
                                {
                                    Some(*value)
                                }
                                _ => None,
                            };
                            match otherwise {
                                Some(value) => {
                                    choices.push((value, targets.otherwise()));
                                    choice_values.insert(value);
                                }
                                None => {
                                    let mut other = state.clone();
                                    if let ty::Uint(_) = discr.ty(&body.local_decls, tcx).kind() {
                                        for (chosen, _) in &choices {
                                            let number =
                                                graph.intern_expr(ExprNode::Number(*chosen))?;
                                            other.facts.condition(
                                                graph.intern_condition(ConditionNode::Compare(
                                                    Order::NotEqual,
                                                    symbol,
                                                    number,
                                                ))?,
                                                &mut graph,
                                                &mut context,
                                            )?;
                                        }
                                    } else {
                                        other.facts.condition(
                                            graph.intern_condition(ConditionNode::Unknown)?,
                                            &mut graph,
                                            &mut context,
                                        )?;
                                    }
                                    successors.push((targets.otherwise(), other));
                                }
                            }
                            for (chosen, target) in choices {
                                let mut branch = state.clone();
                                if let Some(value) = &value {
                                    match switch(
                                        tcx,
                                        body,
                                        &mut branch,
                                        value,
                                        chosen,
                                        &mut discriminants,
                                        &mut context.paths,
                                    )? {
                                        Some(()) => {}
                                        None => continue,
                                    }
                                }
                                let condition = branch.branch_condition(
                                    tcx,
                                    body,
                                    discr,
                                    symbol,
                                    chosen,
                                    &mut discriminants,
                                    &mut graph,
                                    &mut context,
                                )?;
                                if graph.truth(condition, &branch.facts.conditions)?
                                    != Truth::Refuted
                                {
                                    branch
                                        .facts
                                        .condition(condition, &mut graph, &mut context)?;
                                    successors.push((target, branch));
                                }
                            }
                        }
                    }
                    TerminatorKind::Assert {
                        cond,
                        expected,
                        msg,
                        target,
                        ..
                    } => {
                        observations.contracts.behavior = contracts::Behavior::Unknown;
                        let (condition, operation) = match msg.as_ref() {
                            AssertKind::Overflow(BinOp::Sub, left, right)
                                if left.ty(&body.local_decls, tcx).is_integral()
                                    && !left.ty(&body.local_decls, tcx).is_signed() =>
                            {
                                (
                                    {
                                        let size = left
                                            .ty(&body.local_decls, tcx)
                                            .int_size_and_signed(tcx)
                                            .0;
                                        let right = state.argument(
                                            tcx,
                                            body,
                                            right,
                                            &mut graph,
                                            &mut context,
                                        )?;
                                        let left = state.argument(
                                            tcx,
                                            body,
                                            left,
                                            &mut graph,
                                            &mut context,
                                        )?;
                                        let condition = match (&graph[left], &graph[right]) {
                                            (ExprNode::Number(limit), _)
                                                if *limit == size.unsigned_int_max() =>
                                            {
                                                ConditionNode::Compare(Order::Equal, left, left)
                                            }
                                            (_, ExprNode::Number(0)) => {
                                                ConditionNode::Compare(Order::Equal, right, right)
                                            }
                                            _ => ConditionNode::Compare(
                                                Order::LessEqual,
                                                right,
                                                left,
                                            ),
                                        };
                                        graph.intern_condition(condition)?
                                    },
                                    contracts::Operation::Subtraction {
                                        left: crate::diagnostics::operand(tcx, body, left),
                                        right: crate::diagnostics::operand(tcx, body, right),
                                    },
                                )
                            }
                            AssertKind::Overflow(BinOp::Add, left, right) => {
                                let ty = left.ty(&body.local_decls, tcx);
                                let left =
                                    state.argument(tcx, body, left, &mut graph, &mut context)?;
                                let right =
                                    state.argument(tcx, body, right, &mut graph, &mut context)?;
                                (
                                    addition_condition(tcx, ty, &mut graph, left, right)?,
                                    contracts::Operation::Condition,
                                )
                            }
                            AssertKind::Overflow(BinOp::Shl | BinOp::Shr, value, count) => {
                                let value_ty = value.ty(&body.local_decls, tcx);
                                let count_ty = count.ty(&body.local_decls, tcx);
                                let count =
                                    state.argument(tcx, body, count, &mut graph, &mut context)?;
                                (
                                    shift_condition(tcx, value_ty, count_ty, &mut graph, count)?,
                                    contracts::Operation::Condition,
                                )
                            }
                            AssertKind::BoundsCheck { len, index } => (
                                {
                                    let index = state.argument(
                                        tcx,
                                        body,
                                        index,
                                        &mut graph,
                                        &mut context,
                                    )?;
                                    let len =
                                        state.argument(tcx, body, len, &mut graph, &mut context)?;
                                    graph.intern_condition(ConditionNode::Compare(
                                        Order::Less,
                                        index,
                                        len,
                                    ))?
                                },
                                contracts::Operation::Condition,
                            ),
                            AssertKind::DivisionByZero(_) | AssertKind::RemainderByZero(_) => (
                                {
                                    let value = state.argument(
                                        tcx,
                                        body,
                                        cond,
                                        &mut graph,
                                        &mut context,
                                    )?;
                                    graph.from_expr(value, u128::from(*expected))?
                                },
                                contracts::Operation::Condition,
                            ),
                            unsupported => {
                                let reason = match unsupported {
                                    AssertKind::Overflow(BinOp::Sub, ..) => {
                                        "signed subtraction overflow checking is not supported"
                                    }
                                    AssertKind::Overflow(BinOp::Mul, ..) => {
                                        "multiplication overflow checking is not supported"
                                    }
                                    AssertKind::Overflow(BinOp::Div | BinOp::Rem, ..) => {
                                        "signed division overflow checking is not supported"
                                    }
                                    AssertKind::Overflow(..) => {
                                        "this arithmetic overflow check is not supported"
                                    }
                                    AssertKind::OverflowNeg(_) => {
                                        "negation overflow checking is not supported"
                                    }
                                    AssertKind::ResumedAfterReturn(_)
                                    | AssertKind::ResumedAfterPanic(_)
                                    | AssertKind::ResumedAfterDrop(_) => {
                                        "coroutine resume checking is not supported"
                                    }
                                    AssertKind::MisalignedPointerDereference { .. } => {
                                        "pointer alignment checking is not supported"
                                    }
                                    AssertKind::NullPointerDereference
                                    | AssertKind::NullReferenceConstructed => {
                                        "null pointer checking is not supported"
                                    }
                                    AssertKind::InvalidEnumConstruction(_) => {
                                        "enum discriminant construction checking is not supported"
                                    }
                                    AssertKind::BoundsCheck { .. }
                                    | AssertKind::DivisionByZero(_)
                                    | AssertKind::RemainderByZero(_) => {
                                        unreachable!("handled checks above")
                                    }
                                };
                                (
                                    {
                                        let value = state.argument(
                                            tcx,
                                            body,
                                            cond,
                                            &mut graph,
                                            &mut context,
                                        )?;
                                        graph.from_expr(value, u128::from(*expected))?
                                    },
                                    contracts::Operation::Unsupported(reason.into()),
                                )
                            }
                        };
                        let truth = graph.truth(condition, &state.facts.conditions)?;
                        let proved_arithmetic = match msg.as_ref() {
                            AssertKind::Overflow(BinOp::Add | BinOp::Shl | BinOp::Shr, ..) => {
                                truth == Truth::Proven
                            }
                            _ => false,
                        };
                        if !proved_arithmetic {
                            observations
                                .contracts
                                .requirements
                                .push(contracts::Requirement {
                                    invalidated: state.facts.lost.clone(),
                                    consumer: contracts::Consumer {
                                        def: body.source.def_id(),
                                        span: terminator.source_info.span,
                                        operation,
                                    },
                                    condition,
                                    guards: state.facts.conditions.clone(),
                                    span: terminator.source_info.span,
                                });
                        }
                        if truth != Truth::Refuted {
                            state.facts.condition(condition, &mut graph, &mut context)?;
                            successors.push((*target, state));
                        }
                        for successor in terminator.successors() {
                            if successor != *target {
                                successors.push((successor, State::default()));
                            }
                        }
                    }
                    TerminatorKind::Call {
                        func,
                        args,
                        destination,
                        target,
                        ..
                    } => {
                        let mut normal_target = *target;
                        let mut protocols = std::mem::take(&mut state.protocols);
                        let mut escaped_serializations =
                            std::mem::replace(&mut state.escaped_serializations, Set::EMPTY);
                        let arguments: Vec<_> = args
                            .iter()
                            .map(|argument| {
                                state.argument(tcx, body, &argument.node, &mut graph, &mut context)
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        let resources: Vec<_> = args
                            .iter()
                            .enumerate()
                            .filter_map(|(index, argument)| {
                                if !argument.node.ty(&body.local_decls, tcx).is_ref() {
                                    return None;
                                }
                                let place = argument.node.place()?;
                                Some((
                                    index,
                                    context.paths.resolve(
                                        &state.values,
                                        tcx,
                                        place.project_deeper(&[ProjectionElem::Deref], tcx),
                                    ),
                                ))
                            })
                            .collect();
                        let callee = match func.ty(&body.local_decls, tcx).kind() {
                            ty::FnDef(def, _) => Some(*def),
                            _ => None,
                        };
                        let invocation_target = match func.ty(&body.local_decls, tcx).kind() {
                            ty::FnDef(def, args) => {
                                TargetNode::Direct(context.captures.capture_instance(
                                    body.typing_env(tcx),
                                    *def,
                                    args.skip_binder(),
                                )?)
                            }
                            _ => TargetNode::Indirect(state.argument(
                                tcx,
                                body,
                                func,
                                &mut graph,
                                &mut context,
                            )?),
                        };
                        if let Some(check) = protocols.call(
                            &mut context.protocols,
                            &mut graph,
                            tcx,
                            body.source.def_id(),
                            callee,
                            &resources,
                            names,
                            terminator.source_info.span,
                            &state.facts.conditions,
                        )? {
                            observations.contracts.protocol_checks.push(check);
                        }
                        let codec = callee.and_then(|def| crate::transfers::codec(tcx, def));
                        let mut symbol = graph.intern_expr(ExprNode::Unknown)?;
                        let mut contract = None;
                        if let ty::FnDef(def, generic_args) =
                            *func.ty(&body.local_decls, tcx).kind()
                        {
                            if let Some((receiver, &first)) = args.first().zip(arguments.first()) {
                                let receiver = receiver.node.ty(&body.local_decls, tcx);
                                let output = destination.ty(&body.local_decls, tcx).ty;
                                contract = if let (ty::Uint(_), ty::Uint(_)) =
                                    (receiver.kind(), output.kind())
                                    && tcx.lang_items().from_fn() == Some(def)
                                {
                                    let size = receiver.int_size_and_signed(tcx).0;
                                    let value =
                                        state.widen(first, size, &mut graph, &mut context)?;
                                    Some((value, Vec::new()))
                                } else {
                                    let types: Vec<_> = args
                                        .iter()
                                        .map(|arg| arg.node.ty(&body.local_decls, tcx))
                                        .collect();
                                    library::call(
                                        tcx, def, &arguments, receiver, &types, &mut graph,
                                    )?
                                };
                            }
                            match codec {
                                Some(crate::transfers::Codec::Encode(encoding)) => {
                                    if let (Some(value), Some(ty)) = (
                                        arguments.first(),
                                        generic_args.skip_binder().types().next(),
                                    ) {
                                        let encoded = graph.intern_expr(ExprNode::Serialized {
                                            value: *value,
                                            def: body.source.def_id(),
                                            span: terminator.source_info.span,
                                            encoding,
                                            ty: crate::transfers::fingerprint(tcx, ty.peel_refs()),
                                        })?;
                                        let fields = crate::sequence::Sequences::from_iter(
                                            graph.as_mut(),
                                            [encoded],
                                        )?;
                                        symbol = graph.intern_expr(ExprNode::Aggregate(fields))?;
                                    }
                                }
                                Some(crate::transfers::Codec::Decode(encoding)) => {
                                    if let (Some(encoded), Some(ty)) = (
                                        arguments
                                            .first()
                                            .and_then(|value| graph.serialization(*value)),
                                        generic_args.skip_binder().types().next(),
                                    ) && let ExprNode::Serialized {
                                        def,
                                        span,
                                        encoding: actual,
                                        ty: fingerprint,
                                        ..
                                    } = graph[encoded].clone()
                                        && actual == encoding
                                        && fingerprint == crate::transfers::fingerprint(tcx, ty)
                                        && let None =
                                            context.escaped.get(escaped_serializations, &span)
                                        && let Some(_) =
                                            crate::diagnostics::source_span(tcx, def, span)
                                    {
                                        let mut origin = contracts::Consumer {
                                            def,
                                            span,
                                            operation: contracts::Operation::Condition,
                                        }
                                        .source(tcx, sources);
                                        origin.label.message =
                                            "serializes the original typed value".into();
                                        observations.findings.push(Finding {
                                            span: terminator.source_info.span,
                                            evidence: CompilerEvidence::SerializationDetour {
                                                origin,
                                            },
                                        });
                                    }
                                }
                                None => {}
                            }
                            match &contract {
                                Some((value, requirements)) => {
                                    symbol = *value;
                                    for condition in requirements {
                                        observations.contracts.requirements.push(
                                            contracts::Requirement {
                                                invalidated: state.facts.lost.clone(),
                                                consumer: contracts::Consumer {
                                                    def: body.source.def_id(),
                                                    span: terminator.source_info.span,
                                                    operation: contracts::Operation::Condition,
                                                },
                                                condition: *condition,
                                                guards: state.facts.conditions.clone(),
                                                span: terminator.source_info.span,
                                            },
                                        );
                                    }
                                }
                                None => {
                                    if !def.is_local()
                                        && tcx
                                            .def_path_str(def)
                                            .starts_with("core::panicking::panic")
                                    {
                                        if let Some(last) =
                                            graph.items(state.facts.conditions).next_back().copied()
                                        {
                                            let len = crate::sequence::Sequences::len(
                                                graph.as_ref(),
                                                state.facts.conditions,
                                            );
                                            let guards = crate::sequence::Sequences::slice(
                                                graph.as_mut(),
                                                state.facts.conditions,
                                                0..len - 1,
                                            )?
                                            .expect("the last condition exists");
                                            let condition = graph.negate(last)?;
                                            observations.contracts.requirements.push(
                                                contracts::Requirement {
                                                    invalidated: state.facts.lost.clone(),
                                                    consumer: contracts::Consumer {
                                                        def: body.source.def_id(),
                                                        span: terminator.source_info.span,
                                                        operation: contracts::Operation::Condition,
                                                    },
                                                    condition,
                                                    guards,
                                                    span: terminator.source_info.span,
                                                },
                                            );
                                        }
                                    }
                                }
                            }
                        }
                        if let None = contract {
                            let arguments_id = crate::sequence::Sequences::from_iter(
                                graph.as_mut(),
                                arguments.iter().copied(),
                            )?;
                            observations.contracts.calls.push(contracts::Call {
                                basis: match state.basis {
                                    contracts::CheckBasis::Expression => {
                                        contracts::CheckBasis::Expression
                                    }
                                    contracts::CheckBasis::ControlFlow(evidence) => {
                                        contracts::CheckBasis::ControlFlow(
                                            graph.evidence_sequence(evidence)?,
                                        )
                                    }
                                },
                                target: invocation_target.clone(),
                                arguments: arguments_id,
                                guards: state.facts.conditions.clone(),
                                span: terminator.source_info.span,
                            });
                            if let ExprNode::Unknown = graph[symbol] {
                                symbol = graph.intern_expr(ExprNode::Call(
                                    invocation_target.clone(),
                                    arguments_id,
                                    None,
                                ))?;
                            }
                        }
                        if let (None, None) = (codec, callee.and_then(|def| method(tcx, def))) {
                            for argument in &arguments {
                                if let Some(encoded) = graph.serialization(*argument)
                                    && let ExprNode::Serialized { span, .. } = &graph[encoded]
                                {
                                    context.escaped.insert(
                                        &mut escaped_serializations,
                                        *span,
                                        (),
                                    )?;
                                }
                            }
                        }
                        let behavior = match (&contract, &graph[symbol]) {
                            (Some(_), _) => contracts::Behavior::Pure,
                            (None, ExprNode::Call(TargetNode::Direct(instance), ..)) => {
                                contracts::Behavior::Calls(FxHashSet::from_iter([
                                    graph[*instance].def
                                ]))
                            }
                            _ => contracts::Behavior::Unknown,
                        };
                        observations.contracts.behavior.merge(&behavior);
                        let external = match callee {
                            Some(def) if def.is_local() => None,
                            _ => match callee.and_then(|def| tcx.trait_of_assoc(def)) {
                                Some(owner)
                                    if Some(owner) == tcx.lang_items().fn_trait()
                                        || Some(owner) == tcx.lang_items().fn_mut_trait()
                                        || Some(owner) == tcx.lang_items().fn_once_trait() =>
                                {
                                    None
                                }
                                _ => Some(()),
                            },
                        };
                        if let Some(()) = external {
                            for argument in &arguments {
                                graph.functions(*argument, &mut observations.contracts.escapes)?;
                                if let Some(inputs) =
                                    graph.inputs(contracts::graph::NodeId::Expr(*argument))?
                                {
                                    observations.contracts.escaped_arguments.extend(inputs);
                                }
                            }
                        }
                        for argument in args {
                            let ty = argument.node.ty(&body.local_decls, tcx);
                            if let ty::Ref(_, inner, rustc_hir::Mutability::Mut)
                            | ty::RawPtr(inner, _) = ty.kind()
                                && let ty::Adt(adt, _) = inner.kind()
                            {
                                observations.contracts.mutations.insert(adt.did());
                            }
                        }
                        let mut effects = Some(Vec::new());
                        for argument in args {
                            let effect = 'effect: {
                                let ty = argument.node.ty(&body.local_decls, tcx);
                                match ty.kind() {
                                    ty::Ref(_, inner, rustc_hir::Mutability::Mut) => {
                                        let Some(()) =
                                            frozen(tcx, body, *inner, &mut context.frozen)
                                        else {
                                            break 'effect None;
                                        };
                                        let Some(place) = argument.node.place() else {
                                            break 'effect None;
                                        };
                                        let place = context.paths.resolve(
                                            &state.values,
                                            tcx,
                                            place.project_deeper(&[ProjectionElem::Deref], tcx),
                                        );
                                        let union = place.projection.iter().enumerate().find_map(
                                            |(depth, projection)| {
                                                let ProjectionElem::Field(..) = projection else {
                                                    return None;
                                                };
                                                let parent = Place {
                                                    local: place.local,
                                                    projection: tcx
                                                        .mk_place_elems(&place.projection[..depth]),
                                                };
                                                match parent.ty(&body.local_decls, tcx).ty.kind() {
                                                    ty::Adt(adt, _) if adt.is_union() => {
                                                        Some(parent)
                                                    }
                                                    _ => None,
                                                }
                                            },
                                        );
                                        let (place, name) = match union {
                                            Some(place) => {
                                                let (origin, consumed) = context.names.origin(
                                                    tcx,
                                                    place,
                                                    &context.paths,
                                                    &mut graph,
                                                )?;
                                                let name = match &place.projection[consumed..] {
                                                    [] | [ProjectionElem::Deref] => graph[origin]
                                                        .name
                                                        .map(|name| graph[name].to_owned()),
                                                    _ => None,
                                                };
                                                (place, name)
                                            }
                                            None => {
                                                let name = crate::diagnostics::operand(
                                                    tcx,
                                                    body,
                                                    &argument.node,
                                                )
                                                .map(|name| match inner.kind() {
                                                    ty::Bool
                                                    | ty::Int(_)
                                                    | ty::Uint(_)
                                                    | ty::Char => {
                                                        format!("*({name})")
                                                    }
                                                    _ => format!("({name})"),
                                                });
                                                (place, name)
                                            }
                                        };
                                        let expression = state.expression(
                                            tcx,
                                            body,
                                            place,
                                            &mut graph,
                                            &mut context,
                                        )?;
                                        if let None = graph.location(expression)
                                            && let Some(_) =
                                                place.projection.iter().find(|projection| {
                                                    *projection == ProjectionElem::Deref
                                                })
                                        {
                                            break 'effect None;
                                        }
                                        Some(Some((place, expression, name)))
                                    }
                                    ty::Ref(_, inner, rustc_hir::Mutability::Not) => {
                                        let Some(()) =
                                            frozen(tcx, body, *inner, &mut context.frozen)
                                        else {
                                            break 'effect None;
                                        };
                                        Some(None)
                                    }
                                    _ => {
                                        let Some(()) = frozen(tcx, body, ty, &mut context.frozen)
                                        else {
                                            break 'effect None;
                                        };
                                        for argument in ty.walk() {
                                            if let Some(ty) = argument.as_type()
                                                && let ty::RawPtr(..)
                                                | ty::Ref(_, _, rustc_hir::Mutability::Mut) =
                                                    ty.kind()
                                            {
                                                break 'effect None;
                                            }
                                        }
                                        Some(None)
                                    }
                                }
                            };
                            match (effects.as_mut(), effect) {
                                (Some(effects), Some(effect)) => effects.push(effect),
                                (_, None) => {
                                    effects = None;
                                    break;
                                }
                                (None, Some(_)) => {
                                    unreachable!("unknown effects stop argument traversal")
                                }
                            }
                        }
                        match &effects {
                            Some(effects) => {
                                let writes = effects.iter().flatten();
                                for (place, expression, _) in writes {
                                    observations.contracts.behavior = contracts::Behavior::Unknown;
                                    match graph.location(*expression).map(|(base, _)| &graph[base])
                                    {
                                        Some(ExprNode::Argument(argument)) => {
                                            graph.record_argument_write(
                                                &mut observations.writes,
                                                *argument,
                                            )?;
                                        }
                                        _ if place.local.index() > 0
                                            && place.local.index() <= body.arg_count =>
                                        {
                                            graph.record_argument_write(
                                                &mut observations.writes,
                                                place.local.index() - 1,
                                            )?;
                                        }
                                        _ => {
                                            if let Some(_) =
                                                place.projection.iter().find(|projection| {
                                                    *projection == ProjectionElem::Deref
                                                })
                                            {
                                                observations.writes = contracts::Writes::Unknown;
                                            }
                                        }
                                    }
                                }
                            }
                            None => {
                                observations.writes = contracts::Writes::Unknown;
                                observations.contracts.behavior = contracts::Behavior::Unknown;
                            }
                        }
                        let facts = std::mem::take(&mut state.facts);
                        let references =
                            state.values.references(*destination, &mut context.paths)?;
                        let invalidated = std::mem::take(&mut state.invalidated);
                        let moved = std::mem::take(&mut state.moved);
                        let method = match *func.ty(&body.local_decls, tcx).kind() {
                            ty::FnDef(def, _) => method(tcx, def),
                            _ => None,
                        };
                        let receiver = args.first().and_then(|arg| {
                            match state.operand(tcx, &arg.node, &context.paths) {
                                Some(
                                    Value::Direct(ValueKind::Reference(place))
                                    | Value::Direct(ValueKind::Origin(place)),
                                ) => Some(place),
                                _ => arg
                                    .node
                                    .place()
                                    .map(|place| context.paths.resolve(&state.values, tcx, place)),
                            }
                        });
                        match (method, receiver) {
                            (Some(method), Some(place)) => {
                                let value = match method {
                                    Method::Predicate(variant) => {
                                        Some(Value::Direct(ValueKind::Predicate { place, variant }))
                                    }
                                    Method::Extract(required) => {
                                        extract(
                                            tcx,
                                            body,
                                            &state,
                                            place,
                                            required,
                                            terminator.source_info.span,
                                            &mut observations,
                                            &context.paths,
                                        );
                                        if let Value::Direct(ValueKind::Known(Fact::Variant(
                                            actual,
                                        ))) = context.paths.value(&state.values, place)
                                            && actual != required
                                        {
                                            normal_target = None;
                                        }
                                        None
                                    }
                                    Method::Borrow => {
                                        Some(context.paths.value(&state.values, place))
                                    }
                                    Method::Take | Method::Replace => {
                                        let value = match context.paths.value(&state.values, place)
                                        {
                                            value @ Value::Direct(ValueKind::Known(_)) => {
                                                Some(value)
                                            }
                                            _ => None,
                                        };
                                        state.forget(place, &mut graph, &mut context)?;
                                        let variant = match method {
                                            Method::Take => 0,
                                            Method::Replace => 1,
                                            _ => unreachable!(),
                                        };
                                        state.values.insert(
                                            place,
                                            Value::Direct(ValueKind::Known(Fact::Variant(
                                                VariantIdx::from_usize(variant),
                                            ))),
                                            &mut context.paths,
                                        )?;
                                        value
                                    }
                                    Method::VecPush => None,
                                };
                                state.forget(*destination, &mut graph, &mut context)?;
                                if let Some(value) = value {
                                    state
                                        .values
                                        .insert(*destination, value, &mut context.paths)?;
                                }
                            }
                            _ => {
                                state = State {
                                    basis: state.basis,
                                    ..State::default()
                                }
                            }
                        }
                        state
                            .values
                            .restore_references(&references, &mut context.paths)?;
                        state.invalidated = invalidated;
                        state.moved = moved;
                        state.facts = facts;
                        let advancing = match &graph[symbol] {
                            ExprNode::MatchEntry(_) | ExprNode::NextToken(_) => {
                                receiver.zip(arguments.first().cloned())
                            }
                            _ => None,
                        };
                        let preserving = match &graph[symbol] {
                            ExprNode::Tokens { .. }
                            | ExprNode::Matches { .. }
                            | ExprNode::MatchEntry(_)
                            | ExprNode::NextToken(_) => Some(()),
                            _ => None,
                        };
                        let mut written = Vec::new();
                        let mut invalidated = Vec::new();
                        if let None = preserving {
                            match effects {
                                Some(effects) => {
                                    let effects = effects.into_iter().flatten();
                                    for (place, expression, name) in effects {
                                        let adt = match place
                                            .ty(&body.local_decls, tcx)
                                            .ty
                                            .peel_refs()
                                            .kind()
                                        {
                                            ty::Adt(adt, _) => Some(adt.did()),
                                            _ => None,
                                        };
                                        let origin = contracts::Origin {
                                            def: body.source.def_id(),
                                            name,
                                            adt,
                                            identity: Some(contracts::Identity {
                                                origin: (body.source.def_id(), place.local),
                                                fields: place
                                                    .projection
                                                    .iter()
                                                    .filter_map(|projection| match projection {
                                                        ProjectionElem::Field(index, _) => {
                                                            Some(index.index())
                                                        }
                                                        _ => None,
                                                    })
                                                    .collect(),
                                                calls: vec![(
                                                    body.source.def_id(),
                                                    destination.local,
                                                )],
                                            }),
                                        };
                                        let origin = graph.intern_value(&origin)?;
                                        let value = graph.intern_expr(ExprNode::Opaque(origin))?;
                                        state.facts.invalidate(
                                            GraphInvalidation::Replace {
                                                target: expression,
                                                value,
                                            },
                                            &mut graph,
                                            &mut context,
                                            facts::Scope::Lost,
                                            |_| None,
                                        )?;
                                        for condition in state.facts.lost_conditions(
                                            expression,
                                            value,
                                            &mut graph,
                                            &mut context,
                                        )? {
                                            invalidated.push(Invalidated {
                                                condition,
                                                def: body.source.def_id(),
                                                span: terminator.source_info.span,
                                            });
                                        }
                                        written.push((place, value));
                                        state.invalidated.insert(place, (), &mut context.paths)?;
                                        state.facts.invalidate(
                                            GraphInvalidation::Memory(expression),
                                            &mut graph,
                                            &mut context,
                                            facts::Scope::Live,
                                            |key| {
                                                // Keep parent origins so untouched fields retain their identity.
                                                if key.local == place.local
                                                    && place.projection.starts_with(key.projection)
                                                    && key.projection.len() < place.projection.len()
                                                {
                                                    Some(())
                                                } else {
                                                    None
                                                }
                                            },
                                        )?;
                                        symbol = state.facts.invalidate_expression(
                                            symbol,
                                            GraphInvalidation::Memory(expression),
                                            &mut graph,
                                            &mut context,
                                        )?;
                                        state.values.conflicts(
                                            place,
                                            tcx,
                                            body,
                                            &mut context.paths,
                                        )?;
                                        state.guards.conflicts(
                                            place,
                                            tcx,
                                            body,
                                            &mut context.paths,
                                        )?;
                                    }
                                }
                                None => {
                                    state = State {
                                        basis: state.basis,
                                        ..State::default()
                                    };
                                }
                            }
                        }
                        let unknown_producer = match &graph[symbol] {
                            ExprNode::Unknown => Some(()),
                            ExprNode::Call(TargetNode::Direct(instance), ..)
                                if graph[*instance].def.is_local() =>
                            {
                                None
                            }
                            ExprNode::Call(..) => Some(()),
                            _ => None,
                        };
                        if let Some(()) = unknown_producer {
                            let mut components = destination.ty(&body.local_decls, tcx).ty.walk();
                            while let Some(argument) = components.next() {
                                let Some(ty) = argument.as_type() else {
                                    continue;
                                };
                                match ty.kind() {
                                    ty::Ref(..) | ty::RawPtr(..) => {
                                        components.skip_current_subtree()
                                    }
                                    ty::Adt(adt, _)
                                        if tcx.crate_name(adt.did().krate).as_str() == "core"
                                            && tcx.item_name(tcx.parent(adt.did())).as_str()
                                                == "iter"
                                            && tcx
                                                .item_name(tcx.parent(tcx.parent(adt.did())))
                                                .as_str()
                                                == "slice" =>
                                    {
                                        match tcx.item_name(adt.did()).as_str() {
                                            "Iter" | "Chunks" => components.skip_current_subtree(),
                                            _ => {}
                                        }
                                    }
                                    ty::Adt(adt, _) if adt.did().is_local() => {
                                        observations.contracts.constructions.push(
                                            contracts::Construction {
                                                owner: adt.did(),
                                                value: graph.intern_expr(ExprNode::Unknown)?,
                                                guards: state.facts.conditions.clone(),
                                            },
                                        );
                                    }
                                    _ => {}
                                }
                            }
                        }
                        state.facts.invalidate(
                            GraphInvalidation::Local(destination.local),
                            &mut graph,
                            &mut context,
                            facts::Scope::All,
                            |_| None,
                        )?;
                        symbol = state.facts.invalidate_expression(
                            symbol,
                            GraphInvalidation::Local(destination.local),
                            &mut graph,
                            &mut context,
                        )?;
                        if let ExprNode::Call(target, arguments, _) = graph[symbol].clone() {
                            let origin = context
                                .names
                                .origin(tcx, *destination, &context.paths, &mut graph)?
                                .0;
                            symbol = graph.intern_expr(ExprNode::Call(
                                target,
                                arguments,
                                Some(origin),
                            ))?;
                        }
                        state.moved.remove_prefix(
                            *destination,
                            places::Overlap::Prefixes,
                            &mut context.paths,
                        )?;
                        state.invalidated.remove_prefix(
                            *destination,
                            places::Overlap::Descendants,
                            &mut context.paths,
                        )?;
                        state.facts.remove(destination, &graph, &mut context)?;
                        let iteration_origin = contracts::Origin {
                            def: body.source.def_id(),
                            name: None,
                            adt: None,
                            identity: Some(contracts::Identity {
                                origin: (body.source.def_id(), destination.local),
                                fields: Vec::new(),
                                calls: Vec::new(),
                            }),
                        };
                        let iteration_origin = graph.intern_value(&iteration_origin)?;
                        if let ExprNode::MatchEntry(mut matched) = graph[symbol].clone() {
                            matched.occurrence =
                                graph.intern_expr(ExprNode::Opaque(iteration_origin))?;
                            symbol = graph.intern_expr(ExprNode::MatchEntry(matched))?;
                        }
                        if let Some((place, mut iterator)) = advancing {
                            if let ExprNode::NextToken(mut token) = graph[symbol].clone() {
                                token.length =
                                    graph.intern_expr(ExprNode::Opaque(iteration_origin))?;
                                let end = graph.intern_expr(ExprNode::Arithmetic(
                                    contracts::Arithmetic::Add(ty::UintTy::U32),
                                    token.start,
                                    token.length,
                                ))?;
                                let length = graph.intern_expr(ExprNode::Length(token.text))?;
                                let maximum =
                                    graph.intern_expr(ExprNode::Number(u128::from(u32::MAX)))?;
                                let fits = graph.intern_condition(ConditionNode::Compare(
                                    Order::LessEqual,
                                    length,
                                    maximum,
                                ))?;
                                if tcx.data_layout.pointer_size().bits() <= 32
                                    || graph.truth(fits, &state.facts.conditions)? == Truth::Proven
                                {
                                    let no_overflow = addition_condition(
                                        tcx,
                                        tcx.types.u32,
                                        &mut graph,
                                        token.start,
                                        token.length,
                                    )?;
                                    state
                                        .facts
                                        .condition(no_overflow, &mut graph, &mut context)?;
                                }
                                let conditions = [
                                    ConditionNode::Compare(Order::LessEqual, token.start, end),
                                    ConditionNode::Compare(Order::LessEqual, end, length),
                                    ConditionNode::Boundary(token.text, token.start),
                                    ConditionNode::Boundary(token.text, end),
                                ];
                                for condition in conditions {
                                    state.facts.condition(
                                        graph.intern_condition(condition)?,
                                        &mut graph,
                                        &mut context,
                                    )?;
                                }
                                iterator = graph.intern_expr(ExprNode::Tokens {
                                    text: token.text,
                                    consumed: end,
                                })?;
                                symbol = graph.intern_expr(ExprNode::NextToken(token))?;
                            }
                            state.facts.insert(place, iterator, &graph, &mut context)?;
                        }
                        for fact in invalidated {
                            state.facts.lose(fact, &mut graph, &mut context)?;
                        }
                        for (place, value) in written {
                            state.facts.insert(place, value, &graph, &mut context)?;
                        }
                        if let (Some(Method::VecPush), Some(receiver)) = (method, receiver) {
                            let receiver =
                                state.expression(tcx, body, receiver, &mut graph, &mut context)?;
                            let length = graph.intern_expr(ExprNode::Length(receiver))?;
                            let one = graph.intern_expr(ExprNode::Number(1))?;
                            let condition = graph.intern_condition(ConditionNode::Compare(
                                Order::LessEqual,
                                one,
                                length,
                            ))?;
                            state.facts.condition(condition, &mut graph, &mut context)?;
                        }
                        state
                            .facts
                            .insert(*destination, symbol, &graph, &mut context)?;
                        if let Some((_, requirements)) = contract {
                            for condition in requirements {
                                if graph.truth(condition, &state.facts.conditions)?
                                    == Truth::Refuted
                                {
                                    normal_target = None;
                                }
                            }
                        }
                        state.protocols = protocols;
                        state.escaped_serializations = escaped_serializations;
                        if let Some(target) = normal_target {
                            if let Some(symbol) =
                                context.symbols.get(state.facts.symbols, destination)
                                && let ExprNode::Call(target, arguments, _) = graph[*symbol].clone()
                            {
                                state.facts.condition(
                                    graph.intern_condition(ConditionNode::Returned(
                                        target, arguments,
                                    ))?,
                                    &mut graph,
                                    &mut context,
                                )?;
                            }
                            successors.push((target, state));
                        }
                        for successor in terminator.successors() {
                            if Some(successor) != *target {
                                successors.push((successor, State::default()));
                            }
                        }
                    }
                    TerminatorKind::Return => {
                        observations
                            .contracts
                            .protocol_returns
                            .extend(state.protocols.returns(&context.protocols, body.arg_count));
                        let place = Place::from(RETURN_PLACE);
                        observations.contracts.returns.push(contracts::Return {
                            value: state.expression(tcx, body, place, &mut graph, &mut context)?,
                            guards: state.facts.conditions.clone(),
                        });
                        if let ty::Adt(adt, args) = *body.return_ty().kind()
                            && adt.is_struct()
                        {
                            let fields = adt
                                .non_enum_variant()
                                .fields
                                .iter_enumerated()
                                .filter_map(|(index, field)| {
                                    let place = place.project_deeper(
                                        &[ProjectionElem::Field(
                                            index,
                                            field.ty(tcx, args).skip_normalization(),
                                        )],
                                        tcx,
                                    );
                                    match context.paths.value(&state.values, place) {
                                        Value::Direct(ValueKind::Known(fact)) => {
                                            Some((index, fact))
                                        }
                                        _ => None,
                                    }
                                })
                                .collect();
                            if let Some(owner) = StateType::from_ty(tcx, body, body.return_ty()) {
                                observations.constructions.push(Construction {
                                    owner,
                                    fields,
                                    span: body.span,
                                });
                            }
                        }
                    }
                    TerminatorKind::TailCall { .. } => {
                        observations.contracts.behavior = contracts::Behavior::Unknown;
                        observations.contracts.returns.push(contracts::Return {
                            value: graph.intern_expr(ExprNode::Unknown)?,
                            guards: state.facts.conditions.clone(),
                        });
                    }
                    TerminatorKind::Drop { place, target, .. } => {
                        let preserved = state.moved.empty_drop(
                            tcx,
                            body,
                            *place,
                            &context.paths,
                            &mut context.droppable,
                        );
                        if let None = preserved {
                            observations.contracts.behavior = contracts::Behavior::Unknown;
                            observations.writes = contracts::Writes::Unknown;
                        }
                        for successor in terminator.successors() {
                            let next = match preserved {
                                Some(()) if successor == *target => state.clone(),
                                _ => State::default(),
                            };
                            successors.push((successor, next));
                        }
                    }
                    TerminatorKind::Yield { .. } | TerminatorKind::InlineAsm { .. } => {
                        observations.contracts.behavior = contracts::Behavior::Unknown;
                        observations.writes = contracts::Writes::Unknown;
                        successors.extend(
                            terminator
                                .successors()
                                .map(|target| (target, State::default())),
                        );
                    }
                    _ => successors.extend(
                        terminator
                            .successors()
                            .map(|target| (target, state.clone())),
                    ),
                }
                events.insert(block, observations);
            } else {
                events.remove(&block);
            }
            let mut outgoing: FxHashMap<BasicBlock, State<'tcx, '_, '_>> = FxHashMap::default();
            for (target, state) in successors {
                match outgoing.entry(target) {
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        entry.insert(state);
                    }
                    std::collections::hash_map::Entry::Occupied(mut entry) => {
                        work.merges = work.merges.saturating_add(1);
                        work.attachments = work.attachments.saturating_add(entry.get_mut().merge(
                            state,
                            body.source.def_id(),
                            Join::Hull,
                            &mut graph,
                            &mut context,
                        )?);
                    }
                }
            }
            let outgoing = outgoing
                .into_iter()
                .map(|(target, state)| Ok((target, states.intern(state)?)))
                .collect::<Result<FxHashMap<_, _>, CapacityError>>()?;
            let previous = std::mem::replace(&mut edges[block], outgoing);
            let affected: FxHashSet<_> = previous
                .keys()
                .copied()
                .chain(edges[block].keys().copied())
                .collect();
            for target in affected {
                let state = edges[block].get(&target);
                if previous.get(&target) != state {
                    for &position in &positions[target][&block] {
                        prefixes[target].replace(&mut prefix_maps, position, state.copied())?;
                    }
                    pending.changed(target);
                }
            }
        }
        let loop_writes = loops.writes(
            events.iter().map(|(block, event)| (*block, &event.writes)),
            graph,
        )?;
        for (block, event) in &mut events {
            if let Some(header) = loops[*block].innermost {
                for check in &mut event.contracts.checks {
                    check.loop_writes = Some(loop_writes[&header].clone());
                }
            }
        }
        let mut result = Observations::default();
        result.findings.extend(crate::transfers::borrowed_clones(
            tcx, body, sources, &mut work,
        ));
        for header in loops.headers() {
            if events.contains_key(&header) {
                result
                    .contracts
                    .loops
                    .push(body.basic_blocks[header].terminator().source_info.span);
            }
        }
        for declaration in &body.local_decls {
            if let ty::RawPtr(..) = declaration.ty.kind() {
                result.contracts.behavior = contracts::Behavior::Unknown;
            }
        }
        if let ty::Adt(adt, _) = body.return_ty().kind() {
            result.contracts.output = Some(adt.did());
        }
        for (block, _) in body.basic_blocks.iter_enumerated() {
            if let Some(events) = events.remove(&block) {
                result
                    .contracts
                    .protocol_checks
                    .extend(events.contracts.protocol_checks);
                result
                    .contracts
                    .protocol_returns
                    .extend(events.contracts.protocol_returns);
                result.contracts.behavior.merge(&events.contracts.behavior);
                result
                    .contracts
                    .inspections
                    .extend(events.contracts.inspections);
                result.contracts.escapes.extend(events.contracts.escapes);
                result
                    .contracts
                    .escaped_arguments
                    .extend(events.contracts.escaped_arguments);
                result
                    .contracts
                    .mutations
                    .extend(events.contracts.mutations);
                result
                    .contracts
                    .requirements
                    .extend(events.contracts.requirements);
                result.contracts.checks.extend(events.contracts.checks);
                result.contracts.calls.extend(events.contracts.calls);
                result.contracts.returns.extend(events.contracts.returns);
                result
                    .contracts
                    .constructions
                    .extend(events.contracts.constructions);
                result.findings.extend(events.findings);
                result.invariants.extend(events.invariants);
                result.constructions.extend(events.constructions);
            }
        }
        work.place_prefix_type_steps = context.paths.prefix_type_steps;
        work.discriminant_index_visits = discriminants.visits;
        work.discriminant_index_lookups = discriminants.lookups;
        let capture = Capture {
            observations: result,
            work,
        };
        Ok(capture)
    })?
}

fn frozen<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    ty: ty::Ty<'tcx>,
    memo: &mut FxHashMap<ty::Ty<'tcx>, Option<()>>,
) -> Option<()> {
    if let Some(result) = memo.get(&ty) {
        return *result;
    }
    let result = frozen_uncached(tcx, body, ty, memo);
    memo.insert(ty, result);
    result
}

fn frozen_uncached<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    ty: ty::Ty<'tcx>,
    memo: &mut FxHashMap<ty::Ty<'tcx>, Option<()>>,
) -> Option<()> {
    match ty.kind() {
        ty::Bool
        | ty::Char
        | ty::Int(_)
        | ty::Uint(_)
        | ty::Float(_)
        | ty::Str
        | ty::Never
        | ty::Ref(..)
        | ty::RawPtr(..)
        | ty::FnDef(..)
        | ty::FnPtr(..) => return Some(()),
        ty::Array(inner, _) | ty::Slice(inner) => return frozen(tcx, body, *inner, memo),
        ty::Tuple(fields) => {
            return fields
                .iter()
                .map(|field| frozen(tcx, body, field, memo))
                .collect();
        }
        _ => {}
    }
    // Freeze for a coroutine needs its witness, which depends on the MIR provider being wrapped.
    if let Some(_) = body.coroutine {
        return None;
    }
    for argument in ty.walk() {
        if let Some(ty) = argument.as_type() {
            match ty.kind() {
                ty::Coroutine(..)
                | ty::CoroutineClosure(..)
                | ty::CoroutineWitness(..)
                | ty::Alias(..)
                | ty::Param(..)
                | ty::Dynamic(..) => return None,
                _ => {}
            }
        }
    }
    match ty.is_freeze(tcx, body.typing_env(tcx)) {
        true => Some(()),
        false => None,
    }
}
