use crate::contracts::operations::{ArgumentProjection, InputUse, Inputs};
use crate::sequence::Sequence;
use crate::values::StoreValue;
use std::rc::Rc;
mod applicability;
mod callers;

use crate::contracts::schedule;
use crate::pipeline::report::evaluator::applicability::{
    Applicabilities, Applicability, ApplicabilityId, Traversal,
};

use crate::contracts::graph::evidence::{Evidence, Proof};
use crate::contracts::graph::sets::{Combination, SetId, Sets};
use crate::contracts::recursion::{Recursion, Revision};
use schedule::{Dependencies, Dependency, Engine, Finished, Lookup, QueryId, Session};

use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap, FxIndexSet};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;

use crate::contracts::graph::summaries::CallNode;
use crate::contracts::graph::{
    ArgumentContextId, CapacityError, ChoiceId, ChoiceNode, ConditionId, ConditionNode, ExprId,
    ExprNode, Graph, GuardContextId, NodeId, TargetNode, TextMatchNode, TokenNode,
};
use crate::contracts::{Arithmetic, CheckBasis, Invocation, Join, Order, Relocation, Truth};
use crate::values::{Dispatch, GenericsId, InstanceId, InstanceNode, OriginId};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ChoiceTarget<'g> {
    Indirect,
    Receiver(InstanceId<'g>),
}

pub(crate) type Requirement<'g> = crate::contracts::summaries::RequirementNode<'g>;

#[derive(Clone, PartialEq, Eq, Hash)]
struct RequirementCore<'g> {
    invalidated: Sequence<'g, crate::contracts::InvalidatedFact<ConditionId<'g>>>,
    consumer: crate::contracts::summaries::ConsumerId<'g>,
    condition: ConditionId<'g>,
    applicability: ApplicabilityId<'g>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct RequirementId<'g>(u32, std::marker::PhantomData<fn(&'g ()) -> &'g ()>);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct RequirementPlanId<'g>(u32, std::marker::PhantomData<fn(&'g ()) -> &'g ()>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum RequirementPlan<'g> {
    Leaf(RequirementId<'g>),
    Transform(
        Sequence<'g, RequirementPlanId<'g>>,
        ArgumentContextId<'g>,
        GuardContextId<'g>,
    ),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ReportDemand {
    LocalFindings,
    ExportedContract,
}

#[derive(Clone, Copy)]
enum ReportDisposition {
    Discard,
    Retain,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum RequirementOperation<'g> {
    Resolve,
    LocalFindings,
    Transform(ArgumentContextId<'g>, GuardContextId<'g>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum RequirementPlanOperation<'g> {
    Resolve,
    LocalFindings,
    Transform(ArgumentProjection<'g>, GuardContextId<'g>),
}

#[derive(Clone, Copy)]
enum CacheSlot<'g> {
    Expression(ExprId<'g>, GuardContextId<'g>),
    Condition(ConditionId<'g>, GuardContextId<'g>),
    Guards(GuardContextId<'g>),
    Transform(
        RequirementId<'g>,
        ArgumentProjection<'g>,
        GuardContextId<'g>,
    ),
    Plans(
        Sequence<'g, RequirementPlanId<'g>>,
        RequirementPlanOperation<'g>,
    ),
    Other,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) struct ResolvedRequirements<'g>(RequirementGroup<'g>);

pub(crate) struct RequirementCursor<'g> {
    pending: Vec<Sequence<'g, RequirementPlanId<'g>>>,
    visited: FxHashSet<Sequence<'g, RequirementPlanId<'g>>>,
    state: std::rc::Rc<std::cell::RefCell<RequirementCursorState<'g>>>,
}

#[derive(Clone, Copy)]
pub(crate) struct ResolvedRequirement<'g> {
    pub(crate) requirement: Requirement<'g>,
    pub(crate) condition: ConditionId<'g>,
    pub(crate) outcome: Truth,
}

pub(crate) enum RequirementReport<'g> {
    Pending(RequirementId<'g>),
    Resolved(ResolvedRequirement<'g>),
}

struct RequirementCursorState<'g> {
    applied: FxHashSet<RequirementId<'g>>,
    reports: Vec<RequirementReport<'g>>,
}

impl<'g> RequirementCursor<'g> {
    fn new(
        requirements: ResolvedRequirements<'g>,
        state: std::rc::Rc<std::cell::RefCell<RequirementCursorState<'g>>>,
    ) -> Self {
        Self {
            pending: vec![requirements.0.ordered],
            visited: FxHashSet::default(),
            state,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Obligation<'g> {
    invalidated: Sequence<'g, crate::contracts::InvalidatedFact<ConditionId<'g>>>,
    consumer: crate::contracts::summaries::ConsumerId<'g>,
    condition: ConditionId<'g>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Sharing {
    Independent,
    Stable,
    Contextual,
}

/// Carries one obligation together with its shared, ordered applicability.
struct SharedRequirement<'g> {
    applicability: ApplicabilityId<'g>,
    prefix: Sequence<'g, ConditionId<'g>>,
    sharing: Sharing,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct RequirementGroup<'g> {
    ordered: Sequence<'g, RequirementPlanId<'g>>,
    members: SetId<'g, RequirementPlanId<'g>>,
    obligations: SetId<'g, Obligation<'g>>,
}

impl RequirementGroup<'_> {
    const EMPTY: Self = Self {
        ordered: Sequence::EMPTY,
        members: SetId::EMPTY,
        obligations: SetId::EMPTY,
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct ReportGroup<'g> {
    span: Span,
    requirements: RequirementGroup<'g>,
}

#[derive(Clone, Default, PartialEq, Eq)]
pub(crate) struct Requirements<'g> {
    groups: Vec<ReportGroup<'g>>,
    members: FxHashMap<Span, SetId<'g, RequirementPlanId<'g>>>,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct RequirementsId<'g>(Sequence<'g, ReportGroup<'g>>);
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ReturnGuardsId<'g>(Sequence<'g, Sequence<'g, ConditionId<'g>>>);

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Body<'g> {
    returns: Sequence<'g, crate::contracts::Return<'g, ExprId<'g>, ConditionId<'g>>>,
    requirements: Sequence<'g, (RequirementId<'g>, Span)>,
    calls: Sequence<'g, CallNode<'g>>,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct BodyId<'g>(u32, std::marker::PhantomData<fn(&'g ()) -> &'g ()>);

#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) enum Query<'g> {
    Reduced(ArgumentContextId<'g>, GuardContextId<'g>),
    ChoiceTargets(
        ChoiceId<'g>,
        ChoiceTarget<'g>,
        ArgumentContextId<'g>,
        GuardContextId<'g>,
    ),
    ChoiceCompletes(ChoiceId<'g>, GuardContextId<'g>),
    Expression(ExprId<'g>, GuardContextId<'g>),
    Condition(ConditionId<'g>, GuardContextId<'g>),
    Guards(GuardContextId<'g>),
    Targets(TargetNode<'g>, ArgumentContextId<'g>, GuardContextId<'g>),
    Returned(
        InstanceId<'g>,
        ArgumentContextId<'g>,
        Option<OriginId<'g>>,
        GuardContextId<'g>,
    ),
    ReturnGuards(InstanceId<'g>, ArgumentContextId<'g>),
    Completes(ExprId<'g>, GuardContextId<'g>),
    Requirements(InstanceId<'g>, ArgumentContextId<'g>),
    TransformRequirements(RequirementId<'g>, ArgumentContextId<'g>, GuardContextId<'g>),
    RequirementPlans(
        Sequence<'g, RequirementPlanId<'g>>,
        RequirementOperation<'g>,
    ),
    Materialized(
        TargetNode<'g>,
        ArgumentContextId<'g>,
        GuardContextId<'g>,
        CheckBasis<GuardContextId<'g>>,
        Span,
    ),
    Contextual(InstanceId<'g>, ArgumentContextId<'g>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum Completion {
    Possible,
    Never,
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) enum Answer<'g> {
    Reduced(Option<ExprId<'g>>),
    Expression(ExprId<'g>),
    Condition(ConditionId<'g>),
    Guards(GuardPrefixId<'g>),
    Targets(Option<Sequence<'g, (InstanceId<'g>, Sequence<'g, ExprId<'g>>)>>),
    ReturnGuards(ReturnGuardsId<'g>),
    Completes(Completion),
    Requirements(RequirementsId<'g>),

    ResolvedRequirements(ResolvedRequirements<'g>),
    Calls(Sequence<'g, CallNode<'g>>),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum Derivation {
    #[default]
    Direct,
    Recursive,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Support<'g> {
    pub facts: Evidence<'g>,
    pub derivation: Derivation,
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Derived<'g, T = Answer<'g>> {
    value: T,
    support: Support<'g>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct GuardPrefix<'g> {
    raw: GuardContextId<'g>,
    unique: GuardContextId<'g>,
    members: SetId<'g, ConditionId<'g>>,
}

impl Default for GuardPrefix<'_> {
    fn default() -> Self {
        let empty = GuardContextId(crate::sequence::Sequence::EMPTY);
        let prefix = Self {
            raw: empty,
            unique: empty,
            members: SetId::EMPTY,
        };
        prefix
    }
}
impl<'g> GuardPrefix<'g> {
    fn append(&mut self, graph: &mut Graph<'g>, condition: ConditionId<'g>) -> Step<()> {
        self.raw = GuardContextId(graph.push(self.raw.0, condition)?);
        if let Some(()) = graph.include_guard(&mut self.members, condition)? {
            self.unique = GuardContextId(graph.push(self.unique.0, condition)?);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct GuardPrefixId<'g>(u32, std::marker::PhantomData<fn(&'g ()) -> &'g ()>);

type Step<T> = Result<T, CapacityError>;

#[derive(Clone)]
enum Memo<T> {
    Active(QueryId),
    Ready(T),
    Deferred { value: T, dependency: Dependency },
}

impl<T> Memo<T> {
    fn map<U>(self, f: impl FnOnce(T) -> U) -> Memo<U> {
        match self {
            Self::Active(id) => Memo::Active(id),
            Self::Ready(value) => Memo::Ready(f(value)),
            Self::Deferred { value, dependency } => Memo::Deferred {
                value: f(value),
                dependency,
            },
        }
    }
}

impl<'g, T> Derived<'g, T> {
    fn map<U>(self, f: impl FnOnce(T) -> U) -> Derived<'g, U> {
        let Self { value, support } = self;
        let derived = Derived {
            value: f(value),
            support,
        };
        derived
    }
}

type CacheEntry<'g, T = Answer<'g>> = (Revision, Memo<Derived<'g, T>>);

#[derive(Default)]
/// Keeps evaluator results scoped to the revision that produced them.
struct Cache<'g> {
    expressions: FxHashMap<(ExprId<'g>, GuardContextId<'g>), CacheEntry<'g, ExprId<'g>>>,
    conditions: FxHashMap<(ConditionId<'g>, GuardContextId<'g>), CacheEntry<'g, ConditionId<'g>>>,
    guards: FxHashMap<GuardContextId<'g>, CacheEntry<'g, GuardPrefixId<'g>>>,
    requirement_transforms: FxHashMap<
        (
            RequirementId<'g>,
            ArgumentProjection<'g>,
            GuardContextId<'g>,
        ),
        CacheEntry<'g, ResolvedRequirements<'g>>,
    >,
    requirement_plans: FxHashMap<
        (
            Sequence<'g, RequirementPlanId<'g>>,
            RequirementPlanOperation<'g>,
        ),
        CacheEntry<'g, ResolvedRequirements<'g>>,
    >,
    other: FxHashMap<Query<'g>, CacheEntry<'g>>,
}

impl<'g> Cache<'g> {
    fn get(
        &self,
        query: &Query<'g>,
        revision: Revision,
        slot: CacheSlot<'g>,
    ) -> Option<Memo<Derived<'g>>> {
        fn current<'g, T: Clone>(
            entry: Option<&CacheEntry<'g, T>>,
            revision: Revision,
            f: impl FnOnce(T) -> Answer<'g>,
        ) -> Option<Memo<Derived<'g>>> {
            match entry {
                Some((entry_revision, entry)) if *entry_revision == revision => {
                    Some(entry.clone().map(|derived| derived.map(f)))
                }
                Some(_) | None => None,
            }
        }

        match &slot {
            CacheSlot::Expression(value, guards) => current(
                self.expressions.get(&(*value, *guards)),
                revision,
                Answer::Expression,
            ),
            CacheSlot::Condition(value, guards) => current(
                self.conditions.get(&(*value, *guards)),
                revision,
                Answer::Condition,
            ),
            CacheSlot::Guards(guards) => current(self.guards.get(guards), revision, Answer::Guards),
            CacheSlot::Transform(requirements, projection, guards) => current(
                self.requirement_transforms
                    .get(&(*requirements, *projection, *guards)),
                revision,
                Answer::ResolvedRequirements,
            ),
            CacheSlot::Plans(sequence, operation) => current(
                self.requirement_plans.get(&(*sequence, *operation)),
                revision,
                Answer::ResolvedRequirements,
            ),
            CacheSlot::Other => current(self.other.get(query), revision, |answer| answer),
        }
    }

    fn insert(
        &mut self,
        query: &Query<'g>,
        (revision, entry): CacheEntry<'g>,
        slot: CacheSlot<'g>,
        work: &mut crate::contracts::Work,
    ) {
        match &slot {
            CacheSlot::Expression(value, guards) => {
                let entry = entry.map(|derived| {
                    derived.map(|answer| match answer {
                        Answer::Expression(value) => value,
                        _ => unreachable!("expression query returned a different answer"),
                    })
                });
                self.expressions
                    .insert((*value, *guards), (revision, entry));
            }
            CacheSlot::Condition(value, guards) => {
                let entry = entry.map(|derived| {
                    derived.map(|answer| match answer {
                        Answer::Condition(value) => value,
                        _ => unreachable!("condition query returned a different answer"),
                    })
                });
                self.conditions.insert((*value, *guards), (revision, entry));
            }
            CacheSlot::Guards(guards) => {
                let entry = entry.map(|derived| {
                    derived.map(|answer| match answer {
                        Answer::Guards(value) => value,
                        _ => unreachable!("guards query returned a different answer"),
                    })
                });
                self.guards.insert(*guards, (revision, entry));
            }
            CacheSlot::Transform(requirements, projection, guards) => {
                let entry = entry.map(|derived| {
                    derived.map(|answer| match answer {
                        Answer::ResolvedRequirements(value) => value,
                        _ => unreachable!("requirement transformation returned a different answer"),
                    })
                });
                self.requirement_transforms
                    .insert((*requirements, *projection, *guards), (revision, entry));
            }
            CacheSlot::Plans(sequence, operation) => {
                let entry = entry.map(|derived| {
                    derived.map(|answer| match answer {
                        Answer::ResolvedRequirements(value) => value,
                        _ => unreachable!("requirement plan query returned a different answer"),
                    })
                });
                self.requirement_plans
                    .insert((*sequence, *operation), (revision, entry));
                work.requirement_plan_cache_entries = self.requirement_plans.len();
            }
            CacheSlot::Other => {
                self.other.insert(query.clone(), (revision, entry));
            }
        }
    }
}

enum Progress {
    Settled,
    Blocked,
    Retry,
}

struct Activation<'g> {
    query: Query<'g>,
    support: Support<'g>,
}

pub(crate) struct Frame<'g> {
    first_return: Option<DefId>,
    query: Query<'g>,
    previous: Option<Memo<Derived<'g>>>,
    revision: Revision,
    slot: CacheSlot<'g>,
}

#[derive(Clone, Copy)]
enum GuardDependence {
    Independent,
    Element,
    Dependent,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ReportPathStatus {
    Proven,
    Refuted,
    Unknown(crate::contracts::ProofGap),
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ReportPathKey<'g> {
    applicability: ApplicabilityId<'g>,
    prefix: Sequence<'g, ConditionId<'g>>,
    status: ReportPathStatus,
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct ReportLocation<'g> {
    base: ExprId<'g>,
    fields: Vec<usize>,
}

#[derive(Clone)]
enum ReportSupportTree<'g> {
    Empty,
    Location(ReportLocation<'g>),
    Union(Rc<ReportSupportTree<'g>>, Rc<ReportSupportTree<'g>>),
}

#[derive(Clone)]
enum ReportSupport<'g> {
    Known(Rc<ReportSupportTree<'g>>),
    Unknown,
}

#[derive(Default)]
struct ConditionFacts<'g> {
    support: Option<ReportSupport<'g>>,
    certificate: Option<Option<ConditionId<'g>>>,
    context: Option<Option<()>>,
}

#[derive(Default)]
struct ApplicabilityFacts<'g> {
    support: Option<ReportSupport<'g>>,
    no_proven_guard_path: Option<Option<()>>,
    impossible: Option<Option<()>>,
}

#[derive(Default)]
struct PlanFacts<'g> {
    obligation: Option<Option<(Obligation<'g>, RequirementId<'g>)>>,
    inputs: Option<Inputs<'g>>,
}

#[derive(Default)]
struct PlanSequenceFacts<'g> {
    factors: Option<RequirementGroup<'g>>,
    inputs: Option<Inputs<'g>>,
}

#[derive(Default)]
struct DefinitionActivity<'g> {
    active: Option<QueryId>,
    generics: Option<FxIndexMap<GenericsId<'g>, usize>>,
}

pub(crate) struct Evaluator<'a, 'tcx, 'g> {
    pub work: crate::contracts::Work,
    tcx: TyCtxt<'tcx>,
    captures: crate::values::Captures<'tcx, 'g>,
    guard_prefixes: FxIndexSet<GuardPrefix<'g>>,
    guard_dependence: FxHashMap<NodeId<'g>, GuardDependence>,
    selected: FxHashMap<(ExprId<'g>, GuardContextId<'g>), Derived<'g, ExprId<'g>>>,
    pub graph: &'a mut Graph<'g>,
    definitions: &'a [(DefId, crate::contracts::summaries::SummaryId<'g>)],
    bodies: FxHashMap<DefId, BodyId<'g>>,
    body_values: FxIndexSet<Body<'g>>,
    body_requirements: crate::sequence::Sequences<'g, (RequirementId<'g>, Span)>,
    cache: Cache<'g>,
    queries: Vec<Activation<'g>>,
    dependencies: Dependencies,
    definition_activity: FxHashMap<DefId, DefinitionActivity<'g>>,
    returning: Vec<usize>,
    pub(crate) recursion: Recursion,
    applicability: Applicabilities<'g>,
    applicability_facts: FxHashMap<ApplicabilityId<'g>, ApplicabilityFacts<'g>>,
    report_guard_sequence_blockers: FxHashMap<Sequence<'g, ConditionId<'g>>, Option<()>>,
    requirement_values: FxIndexSet<RequirementCore<'g>>,
    requirement_inputs: FxHashMap<RequirementId<'g>, Inputs<'g>>,
    plan_facts: FxHashMap<RequirementPlanId<'g>, PlanFacts<'g>>,
    plan_sequence_facts: FxHashMap<Sequence<'g, RequirementPlanId<'g>>, PlanSequenceFacts<'g>>,
    requirement_plans: FxIndexSet<RequirementPlan<'g>>,
    requirement_consumers: FxHashMap<crate::contracts::summaries::ConsumerId<'g>, Option<Span>>,
    requirement_sequences: crate::sequence::Sequences<'g, RequirementPlanId<'g>>,
    requirement_groups: crate::sequence::Sequences<'g, ReportGroup<'g>>,
    return_guards: crate::sequence::Sequences<'g, Sequence<'g, ConditionId<'g>>>,
    target_lists: crate::sequence::Sequences<'g, (InstanceId<'g>, Sequence<'g, ExprId<'g>>)>,
    requirement_sets: Sets<'g, RequirementPlanId<'g>>,
    obligation_sets: Sets<'g, Obligation<'g>>,
    requirement_filters: FxHashMap<
        (
            Sequence<'g, RequirementPlanId<'g>>,
            SetId<'g, RequirementPlanId<'g>>,
        ),
        RequirementGroup<'g>,
    >,
    requirement_candidates: FxHashSet<DefId>,
    arena_steps: FxHashMap<DefId, Option<()>>,
    sharing_modes: FxHashMap<(RequirementCore<'g>, Sequence<'g, ConditionId<'g>>), Sharing>,
    report_condition_facts: FxHashMap<ConditionId<'g>, ConditionFacts<'g>>,
    report_expression_supports: FxHashMap<ExprId<'g>, ReportSupport<'g>>,
    report_support_location_cache: FxHashMap<ReportLocation<'g>, Rc<ReportSupportTree<'g>>>,
    report_support_empty_node: Rc<ReportSupportTree<'g>>,
    report_support_union_cache: FxHashMap<(usize, usize), Rc<ReportSupportTree<'g>>>,
    report_support_overlap_cache: FxHashMap<(usize, ReportLocation<'g>), Option<()>>,
    report_support_contains_location_cache: FxHashMap<(usize, ReportLocation<'g>), Option<()>>,
    report_support_tree_overlap_cache: FxHashMap<(usize, usize), Option<()>>,
    report_support_containment_cache: FxHashMap<(usize, usize), Option<()>>,
    report_guard_projection_cache:
        FxHashMap<(usize, Sequence<'g, ConditionId<'g>>), Option<Sequence<'g, ConditionId<'g>>>>,
    report_uniform_contexts:
        FxHashMap<(ConditionId<'g>, ApplicabilityId<'g>), Option<Sequence<'g, ConditionId<'g>>>>,
    report_outcome_certificates:
        FxHashMap<(ConditionId<'g>, ApplicabilityId<'g>), Option<ConditionId<'g>>>,
}

impl<'a, 'tcx, 'g> Evaluator<'a, 'tcx, 'g> {
    fn intern_guard_prefix(&mut self, value: GuardPrefix<'g>) -> Step<GuardPrefixId<'g>> {
        let index = match self.guard_prefixes.get_index_of(&value) {
            Some(index) => index,
            None => {
                u32::try_from(self.guard_prefixes.len()).map_err(|_| CapacityError::Values)?;
                self.guard_prefixes.insert_full(value).0
            }
        };
        Ok(GuardPrefixId(index as u32, std::marker::PhantomData))
    }
    pub fn try_new(
        tcx: TyCtxt<'tcx>,
        definitions: &'a [(DefId, crate::contracts::summaries::SummaryId<'g>)],
        graph: &'a mut Graph<'g>,
        calls: &crate::callers::CallIndex<'_, 'g>,
    ) -> Result<Self, CapacityError> {
        let mut evaluator = Self {
            work: crate::contracts::Work::default(),
            tcx,
            captures: crate::values::Captures::new(
                tcx,
                crate::values::Values::share(graph.as_ref()),
            ),
            guard_prefixes: FxIndexSet::default(),
            guard_dependence: FxHashMap::default(),
            selected: FxHashMap::default(),
            graph,
            definitions,
            bodies: FxHashMap::default(),
            body_values: FxIndexSet::default(),
            body_requirements: crate::sequence::Sequences::new(),
            cache: Cache::default(),
            queries: Vec::new(),
            dependencies: Dependencies::default(),
            definition_activity: FxHashMap::default(),
            returning: Vec::new(),
            recursion: Recursion::default(),
            applicability: Applicabilities::default(),
            applicability_facts: FxHashMap::default(),
            report_guard_sequence_blockers: FxHashMap::default(),
            requirement_values: FxIndexSet::default(),
            requirement_inputs: FxHashMap::default(),
            plan_facts: FxHashMap::default(),
            plan_sequence_facts: FxHashMap::default(),
            requirement_plans: FxIndexSet::default(),
            requirement_consumers: FxHashMap::default(),
            requirement_sequences: crate::sequence::Sequences::new(),
            requirement_groups: crate::sequence::Sequences::new(),
            return_guards: crate::sequence::Sequences::new(),
            target_lists: crate::sequence::Sequences::new(),
            requirement_sets: Sets::new(),
            obligation_sets: Sets::new(),
            requirement_filters: FxHashMap::default(),
            requirement_candidates: FxHashSet::default(),
            arena_steps: FxHashMap::default(),
            sharing_modes: FxHashMap::default(),
            report_condition_facts: FxHashMap::default(),
            report_expression_supports: FxHashMap::default(),
            report_support_location_cache: FxHashMap::default(),
            report_support_empty_node: Rc::new(ReportSupportTree::Empty),
            report_support_union_cache: FxHashMap::default(),
            report_support_overlap_cache: FxHashMap::default(),
            report_support_contains_location_cache: FxHashMap::default(),
            report_support_tree_overlap_cache: FxHashMap::default(),
            report_support_containment_cache: FxHashMap::default(),
            report_guard_projection_cache: FxHashMap::default(),
            report_uniform_contexts: FxHashMap::default(),
            report_outcome_certificates: FxHashMap::default(),
        };
        let mut edges = Vec::new();
        for &(def, id) in definitions {
            let summary = evaluator.graph[id];
            let mut requirements = Vec::new();
            let body_requirements = evaluator
                .graph
                .items(summary.requirements)
                .copied()
                .collect::<Vec<_>>();
            for requirement in body_requirements {
                let core = evaluator.requirement_core(requirement)?;
                let id = evaluator.intern_requirement_core(core)?;
                requirements.push((id, requirement.span));
            }
            for call in evaluator.graph.items(summary.calls) {
                if let TargetNode::Direct(instance) = call.target {
                    edges.push((def, evaluator.graph[instance].def));
                }
            }
            let body = Body {
                returns: summary.returns,
                requirements: evaluator.body_requirements.from_iter(requirements)?,
                calls: summary.calls,
            };
            let body_index = match evaluator.body_values.get_index_of(&body) {
                Some(index) => index,
                None => {
                    u32::try_from(evaluator.body_values.len())
                        .map_err(|_| CapacityError::Values)?;
                    evaluator.body_values.insert_full(body).0
                }
            };
            evaluator
                .bodies
                .insert(def, BodyId(body_index as u32, std::marker::PhantomData));
        }
        evaluator.recursion = Recursion::try_from(edges)?;
        let mut candidates: FxHashSet<_> = evaluator
            .bodies
            .iter()
            .filter_map(|(def, body)| {
                match evaluator
                    .body_requirements
                    .len(evaluator.body_values[body.0 as usize].requirements)
                    == 0
                {
                    true => None,
                    false => Some(*def),
                }
            })
            .collect();
        candidates.extend(evaluator.recursion.recursive_definitions());
        evaluator.requirement_candidates = calls.relevant(&candidates);
        Ok(evaluator)
    }

    fn context(
        &mut self,
        root: NodeId<'g>,
        guards: GuardContextId<'g>,
    ) -> Result<GuardContextId<'g>, CapacityError> {
        if crate::sequence::Sequences::len(self.graph.as_ref(), guards.0) == 0 {
            return Ok(guards);
        }
        enum Work<'g> {
            Visit(NodeId<'g>),
            Build(NodeId<'g>, GuardDependence, Vec<NodeId<'g>>),
        }
        let mut pending = Vec::new();
        if let None = self.guard_dependence.get(&root) {
            pending.push(Work::Visit(root));
        }
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(node) => {
                    if self.guard_dependence.contains_key(&node) {
                        continue;
                    }
                    let mut children = Vec::new();
                    let mut expression = |id| children.push(NodeId::Expr(id));
                    let dependence = match node {
                        NodeId::Expr(id) => match &self.graph[id] {
                            ExprNode::Select(..)
                            | ExprNode::Test(_)
                            | ExprNode::Global(_)
                            | ExprNode::Alternatives(_) => GuardDependence::Dependent,
                            ExprNode::Call(target, arguments, _) => {
                                for value in self.graph.items(*arguments) {
                                    expression(*value);
                                }
                                match target {
                                    TargetNode::Direct(instance)
                                        if !self
                                            .bodies
                                            .contains_key(&self.graph[*instance].def) =>
                                    {
                                        GuardDependence::Independent
                                    }
                                    TargetNode::Direct(_) | TargetNode::Indirect(_) => {
                                        GuardDependence::Dependent
                                    }
                                }
                            }
                            ExprNode::Unknown
                            | ExprNode::Serialized { .. }
                            | ExprNode::Cursor { .. }
                            | ExprNode::Opaque(_)
                            | ExprNode::Argument(_)
                            | ExprNode::Range(_)
                            | ExprNode::Number(_)
                            | ExprNode::Text(_)
                            | ExprNode::Function(_) => GuardDependence::Independent,
                            ExprNode::Typed(_, value)
                            | ExprNode::Field(value, _)
                            | ExprNode::Length(value)
                            | ExprNode::Trimmed(value) => {
                                expression(*value);
                                GuardDependence::Independent
                            }
                            ExprNode::Element(base, index) => {
                                expression(*base);
                                expression(*index);
                                GuardDependence::Element
                            }
                            ExprNode::Closure(_, values)
                            | ExprNode::Aggregate(values)
                            | ExprNode::Variant(_, _, values) => {
                                for value in self.graph.items(*values) {
                                    expression(*value);
                                }
                                GuardDependence::Independent
                            }
                            ExprNode::Found { text, pattern }
                            | ExprNode::Matches { text, pattern } => {
                                expression(*text);
                                expression(*pattern);
                                GuardDependence::Independent
                            }
                            ExprNode::MatchIndex {
                                text,
                                pattern,
                                occurrence,
                            }
                            | ExprNode::MatchEntry(TextMatchNode {
                                text,
                                pattern,
                                occurrence,
                            }) => {
                                expression(*text);
                                expression(*pattern);
                                expression(*occurrence);
                                GuardDependence::Independent
                            }
                            ExprNode::Tokens { text, consumed } => {
                                expression(*text);
                                expression(*consumed);
                                GuardDependence::Independent
                            }
                            ExprNode::Token(TokenNode {
                                text,
                                start,
                                length,
                            })
                            | ExprNode::NextToken(TokenNode {
                                text,
                                start,
                                length,
                            }) => {
                                expression(*text);
                                expression(*start);
                                expression(*length);
                                GuardDependence::Independent
                            }
                            ExprNode::Partition {
                                sequence,
                                predicate,
                            } => {
                                expression(*sequence);
                                expression(*predicate);
                                GuardDependence::Independent
                            }
                            ExprNode::Slice { text, start, end } => {
                                expression(*text);
                                expression(*start);
                                expression(*end);
                                GuardDependence::Independent
                            }
                            ExprNode::Arithmetic(_, left, right) => {
                                expression(*left);
                                expression(*right);
                                GuardDependence::Independent
                            }
                        },
                        NodeId::Condition(id) => match &self.graph[id] {
                            ConditionNode::Unknown => GuardDependence::Independent,
                            ConditionNode::Returned(..) => GuardDependence::Dependent,
                            ConditionNode::Compare(_, left, right)
                            | ConditionNode::Boundary(left, right)
                            | ConditionNode::NotBoundary(left, right) => {
                                expression(*left);
                                expression(*right);
                                GuardDependence::Independent
                            }
                            ConditionNode::Variant(value, _)
                            | ConditionNode::NotVariant(value, _) => {
                                expression(*value);
                                GuardDependence::Independent
                            }
                        },
                        NodeId::Choice(_) => {
                            unreachable!("evaluator dependence visits expressions and conditions")
                        }
                    };
                    pending.push(Work::Build(node, dependence, children.clone()));
                    pending.extend(children.into_iter().map(Work::Visit));
                }
                Work::Build(node, mut dependence, children) => {
                    for child in children {
                        dependence = match (dependence, self.guard_dependence[&child]) {
                            (GuardDependence::Dependent, _) | (_, GuardDependence::Dependent) => {
                                GuardDependence::Dependent
                            }
                            (GuardDependence::Element, _) | (_, GuardDependence::Element) => {
                                GuardDependence::Element
                            }
                            (GuardDependence::Independent, GuardDependence::Independent) => {
                                GuardDependence::Independent
                            }
                        };
                    }
                    if let NodeId::Condition(id) = node
                        && let ConditionNode::Compare(..) = self.graph[id]
                        && let GuardDependence::Element = dependence
                    {
                        dependence = GuardDependence::Dependent;
                    }
                    self.guard_dependence.insert(node, dependence);
                }
            }
        }
        match self.guard_dependence[&root] {
            GuardDependence::Independent | GuardDependence::Element => {
                Ok(GuardContextId(crate::sequence::Sequence::EMPTY))
            }
            GuardDependence::Dependent => Ok(guards),
        }
    }

    fn fallback(&mut self, query: &Query<'g>) -> Result<Answer<'g>, CapacityError> {
        let predicate = match query {
            Query::Condition(condition, guards) => {
                let expression = match self.graph[*condition] {
                    ConditionNode::Compare(Order::Equal, left, right) => {
                        match (&self.graph[left], &self.graph[right]) {
                            (_, ExprNode::Number(1)) => Some(left),
                            (ExprNode::Number(1), _) => Some(right),
                            _ => None,
                        }
                    }
                    _ => None,
                };
                let mut predicate = Some((*condition, None));
                if let Some(value) = expression {
                    let value = self.selected(value, *guards)?;
                    if let ExprNode::Select(condition, _, no) = self.graph[value] {
                        let context = self.context(NodeId::Condition(condition), *guards)?;
                        let query = Query::Condition(condition, context);
                        if let (ExprNode::Number(0), Some(Memo::Active(id))) = (
                            &self.graph[no],
                            self.cache.get(
                                &query,
                                self.revision(&query),
                                CacheSlot::Condition(condition, context),
                            ),
                        ) {
                            predicate = Some((condition, Some(id)));
                        }
                    }
                }
                predicate
            }
            Query::Expression(value, guards) => match &self.graph[*value] {
                ExprNode::Test(condition) => Some((*condition, None)),
                ExprNode::Select(condition, _, no) => {
                    let query = Query::Condition(*condition, *guards);
                    match (
                        &self.graph[*no],
                        self.cache.get(
                            &query,
                            self.revision(&query),
                            CacheSlot::Condition(*condition, *guards),
                        ),
                    ) {
                        (ExprNode::Number(0), Some(Memo::Active(id))) => {
                            Some((*condition, Some(id)))
                        }
                        _ => None,
                    }
                }
                _ => None,
            },
            _ => None,
        };
        if let Some((predicate, blocker)) = predicate
            && let ConditionNode::Returned(TargetNode::Direct(callable), arguments) =
                self.graph[predicate].clone()
        {
            if let Some(()) = self.finite_arguments(callable, &arguments.into()) {
                if let Some(blocker) = blocker {
                    self.dependencies.observe(Dependency::Blocked(blocker));
                }
                let zero = self.graph.intern_expr(ExprNode::Number(0))?;
                return Ok(match query {
                    Query::Condition(..) => {
                        let one = self.graph.intern_expr(ExprNode::Number(1))?;
                        Answer::Condition(self.graph.intern_condition(ConditionNode::Compare(
                            Order::Equal,
                            zero,
                            one,
                        ))?)
                    }
                    Query::Expression(..) => Answer::Expression(zero),
                    _ => unreachable!(
                        "only condition and boolean-expression queries select a return predicate"
                    ),
                });
            }
        }
        Ok(match query {
            Query::Reduced(..) => Answer::Reduced(Some(self.graph.intern_expr(ExprNode::Unknown)?)),
            Query::ChoiceTargets(..) => Answer::Targets(None),
            Query::ChoiceCompletes(..) => Answer::Completes(Completion::Never),
            Query::Expression(..) => Answer::Expression(self.graph.intern_expr(ExprNode::Unknown)?),
            Query::Condition(condition, _) => Answer::Condition(*condition),
            Query::Guards(_) => {
                let returning = self.returning.last().map(|index| {
                    let Query::ReturnGuards(callable, arguments) = &self.queries[*index].query
                    else {
                        unreachable!("return-guard index names a return-guard query")
                    };
                    (*callable, &arguments.0)
                });
                match returning
                    .and_then(|(callable, arguments)| self.finite_arguments(callable, arguments))
                {
                    Some(()) => {
                        let zero = self.graph.intern_expr(ExprNode::Number(0))?;
                        let one = self.graph.intern_expr(ExprNode::Number(1))?;
                        let mut prefix = GuardPrefix::default();
                        let condition = self.graph.intern_condition(ConditionNode::Compare(
                            Order::Equal,
                            zero,
                            one,
                        ))?;
                        prefix.append(self.graph, condition)?;
                        Answer::Guards(self.intern_guard_prefix(prefix)?)
                    }
                    None => {
                        let prefix = GuardPrefix::default();
                        Answer::Guards(self.intern_guard_prefix(prefix)?)
                    }
                }
            }
            Query::Targets(..) => Answer::Targets(None),
            Query::Completes(..) => Answer::Completes(Completion::Never),
            Query::Returned(_, _, origin, _) => {
                Answer::Expression(self.graph.intern_expr(match origin {
                    Some(origin) => ExprNode::Opaque(*origin),
                    None => ExprNode::Unknown,
                })?)
            }
            Query::ReturnGuards(callable, arguments) => {
                let guards = match self.finite_arguments(*callable, &arguments.0) {
                    Some(()) => crate::sequence::Sequence::EMPTY,
                    None => self
                        .return_guards
                        .from_iter([crate::sequence::Sequence::EMPTY])?,
                };
                Answer::ReturnGuards(ReturnGuardsId(guards))
            }
            Query::Requirements(callable, arguments) => {
                let mut requirements = Requirements::default();
                if let None = self.finite_arguments(*callable, &arguments.0) {
                    let def = self.graph[*callable].def;
                    let span = self.tcx.def_span(def);
                    self.recursive_requirement(&mut requirements, def, span, Sequence::EMPTY)?;
                }
                Answer::Requirements(RequirementsId(
                    self.requirement_groups.from_iter(requirements.groups)?,
                ))
            }
            Query::TransformRequirements(..) => {
                Answer::ResolvedRequirements(ResolvedRequirements(RequirementGroup::EMPTY))
            }
            Query::RequirementPlans(..) => {
                Answer::ResolvedRequirements(ResolvedRequirements(RequirementGroup::EMPTY))
            }
            Query::Materialized(target, arguments, guards, basis, span) => {
                Answer::Calls(crate::sequence::Sequences::from_iter(
                    self.graph.as_mut(),
                    [CallNode {
                        basis: match basis {
                            CheckBasis::Expression => CheckBasis::Expression,
                            CheckBasis::ControlFlow(basis) => CheckBasis::ControlFlow(basis.0),
                        },
                        target: *target,
                        arguments: arguments.0,
                        guards: guards.0,
                        span: *span,
                    }],
                )?)
            }
            Query::Contextual(..) => Answer::Calls(Sequence::EMPTY),
        })
    }

    fn revision(&self, query: &Query<'g>) -> Revision {
        match query {
            Query::Requirements(callable, _) => self.recursion.revision(self.graph[*callable].def),
            _ => Revision::default(),
        }
    }

    fn recursive_edge_requirements(
        &mut self,
        result: &mut Requirements<'g>,
        induction_edges: &mut Vec<(Span, Sequence<'g, ConditionId<'g>>)>,
        caller: InstanceId<'g>,
        callee: InstanceId<'g>,
        call: &CallNode<'g>,
        guards: Sequence<'g, ConditionId<'g>>,
    ) -> Step<()> {
        let caller = self.graph[caller];
        let callee = self.graph[callee];
        let def = caller.def;
        if let TargetNode::Direct(_) = call.target
            && def == callee.def
            && let Some(()) = *self.arena_steps.entry(def).or_insert_with(|| {
                crate::arena_induction::proves_step(self.tcx, def, |leaf| {
                    let body = self.bodies.get(&leaf)?;
                    (self.body_values[body.0 as usize].requirements == Sequence::EMPTY)
                        .then_some(())
                })
            })
        {
            // Reporting a generic method itself starts with an empty substitution.
            // Compare its identity substitution with the actual recursive instance.
            let caller = if caller.args == GenericsId::EMPTY && caller != callee {
                let identity = ty::GenericArgs::identity_for_item(self.tcx, def);
                let instance = self.captures.capture_instance(
                    ty::TypingEnv::post_analysis(self.tcx, def),
                    def,
                    identity,
                )?;
                self.graph[instance]
            } else {
                caller
            };
            if caller == callee {
                induction_edges.push((call.span, guards));
                return Ok(());
            }
        }
        self.recursive_requirement(result, def, call.span, guards)
    }

    fn recursive_requirement(
        &mut self,
        result: &mut Requirements<'g>,
        def: DefId,
        span: Span,
        guards: Sequence<'g, ConditionId<'g>>,
    ) -> Step<()> {
        let consumer = self
            .graph
            .unsupported_consumer(def, span, "recursive call requirements")?;
        let condition = self.graph.intern_condition(ConditionNode::Unknown)?;
        self.insert_requirement(
            result,
            Requirement {
                invalidated: Sequence::EMPTY,
                consumer,
                condition,
                guards,
                span,
            },
        )
    }

    fn symbolic_arguments(&mut self, def: DefId) -> Step<Sequence<'g, ExprId<'g>>> {
        match self.tcx.def_kind(def) {
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn => {}
            _ => return Ok(Sequence::EMPTY),
        }
        let count = self
            .tcx
            .fn_sig(def)
            .instantiate_identity()
            .skip_binder()
            .inputs()
            .len();
        let values = (0..count)
            .map(|index| self.graph.intern_expr(ExprNode::Argument(index)))
            .collect::<Result<Vec<_>, _>>()?;
        crate::sequence::Sequences::from_iter(self.graph.as_mut(), values)
    }

    fn finite_arguments(
        &self,
        callable: InstanceId<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
    ) -> Option<()> {
        let instance = self.graph[callable];
        match self.tcx.def_kind(instance.def) {
            rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn => {}
            _ => return None,
        }
        if let Some(DefinitionActivity {
            generics: Some(contexts),
            ..
        }) = self.definition_activity.get(&instance.def)
        {
            match (contexts.len(), contexts.keys().next()) {
                (1, Some(arguments)) if *arguments == instance.args => {}
                _ => return None,
            }
        }
        let signature = self
            .tcx
            .fn_sig(instance.def)
            .instantiate_identity()
            .skip_binder();
        if signature.inputs().len()
            != crate::sequence::Sequences::len(self.graph.as_ref(), *arguments)
        {
            return None;
        }
        let inputs = signature.inputs().iter().zip(self.graph.items(*arguments));
        for (ty, value) in inputs {
            match (ty.kind(), &self.graph[*value]) {
                (ty::Bool, ExprNode::Number(0 | 1)) => {}
                (ty::Adt(adt, _), ExprNode::Variant(def, variant, fields))
                    if adt.did() == *def
                        && crate::sequence::Sequences::len(self.graph.as_ref(), *fields) == 0
                        && adt
                            .variants()
                            .iter()
                            .all(|variant| variant.fields.is_empty())
                        && *variant < adt.variants().len() => {}
                _ => return None,
            }
        }
        Some(())
    }

    fn observe(&mut self, support: Support<'g>) -> Step<()> {
        if let Some(Activation {
            support: current, ..
        }) = self.queries.last_mut()
        {
            current.facts =
                self.graph
                    .combine_evidence(Combination::Union, current.facts, support.facts)?;
            current.derivation = match (current.derivation, support.derivation) {
                (Derivation::Recursive, _) | (_, Derivation::Recursive) => Derivation::Recursive,
                (Derivation::Direct, Derivation::Direct) => Derivation::Direct,
            };
        }
        Ok(())
    }

    fn selected(&mut self, value: ExprId<'g>, guards: GuardContextId<'g>) -> Step<ExprId<'g>> {
        let mut path = Vec::new();
        let mut current = value;
        let mut result = loop {
            if let Some(result) = self.selected.get(&(current, guards)) {
                break result.clone();
            }
            let ExprNode::Select(condition, yes, no) = self.graph[current] else {
                let result = Derived {
                    value: current,
                    support: Support::default(),
                };
                self.selected.insert((current, guards), result.clone());
                break result;
            };
            let (next, facts) = match self.graph.prove_in_context(condition, guards)? {
                Proof::Proven(facts) => (yes, facts),
                Proof::Refuted(facts) => (no, facts),
                Proof::Unknown(_) => {
                    let result = Derived {
                        value: current,
                        support: Support::default(),
                    };
                    self.selected.insert((current, guards), result.clone());
                    break result;
                }
            };
            path.push((current, facts));
            current = next;
        };
        while let Some((current, facts)) = path.pop() {
            result.support.facts =
                self.graph
                    .combine_evidence(Combination::Union, result.support.facts, facts)?;
            self.selected.insert((current, guards), result.clone());
        }
        self.observe(result.support)?;
        Ok(result.value)
    }

    fn truth(&mut self, condition: ConditionId<'g>, guards: GuardContextId<'g>) -> Step<Truth> {
        let proof = self.graph.prove_in_context(condition, guards)?;
        match proof {
            Proof::Proven(facts) | Proof::Refuted(facts) => self.observe(Support {
                facts,
                derivation: Derivation::Direct,
            })?,
            Proof::Unknown(_) => {}
        }
        Ok(proof.into())
    }

    fn test(
        &mut self,
        condition: ConditionId<'g>,
        guards: GuardContextId<'g>,
    ) -> Step<(ExprId<'g>, Support<'g>)> {
        let proof = self.graph.prove_in_context(condition, guards)?;
        let (node, support) = match proof {
            Proof::Proven(facts) => (
                ExprNode::Number(1),
                Support {
                    facts,
                    derivation: Derivation::Direct,
                },
            ),
            Proof::Refuted(facts) => (
                ExprNode::Number(0),
                Support {
                    facts,
                    derivation: Derivation::Direct,
                },
            ),
            Proof::Unknown(_) => (ExprNode::Test(condition), Support::default()),
        };
        let value = self.graph.intern_expr(node)?;
        Ok((value, support))
    }

    pub(crate) fn established(
        &mut self,
        condition: ConditionId<'g>,
        guards: &Sequence<'g, ConditionId<'g>>,
        basis: &crate::contracts::CheckBasis<Sequence<'g, ConditionId<'g>>>,
    ) -> Step<Option<crate::pipeline::report::EstablishedCheck<'g>>> {
        if self
            .graph
            .conjunction(guards, &crate::sequence::Sequence::EMPTY)?
            == Truth::Refuted
        {
            return Ok(None);
        }
        let guards = GuardContextId::from(*guards);
        let context = self.context(NodeId::Condition(condition), guards)?;
        let Derived {
            value: Answer::Condition(condition),
            mut support,
        } = schedule::evaluate(self, Query::Condition(condition, context))?
        else {
            unreachable!("condition query result");
        };
        let proof = self.graph.prove_in_context(condition, guards)?;
        let (outcome, facts) = match proof {
            Proof::Proven(facts) => (shapelint::CheckOutcome::AlwaysTrue, facts),
            Proof::Refuted(facts) => (shapelint::CheckOutcome::AlwaysFalse, facts),
            Proof::Unknown(_) => return Ok(None),
        };
        support.facts = self
            .graph
            .combine_evidence(Combination::Union, support.facts, facts)?;
        let check = crate::pipeline::report::EstablishedCheck {
            basis: basis.clone(),
            condition,
            outcome,
            support,
        };
        Ok(Some(check))
    }

    fn refuted(
        &mut self,
        conditions: &Sequence<'g, ConditionId<'g>>,
        guards: GuardContextId<'g>,
    ) -> Step<Option<()>> {
        let mut conditions = self.graph.scan(*conditions);
        while let Some(condition) = conditions.next() {
            if self.truth(condition, guards)? == Truth::Refuted {
                return Ok(Some(()));
            }
        }
        Ok(None)
    }

    fn requirement_core(&mut self, requirement: Requirement<'g>) -> Step<RequirementCore<'g>> {
        let Requirement {
            invalidated,
            consumer,
            condition,
            guards,
            span: _,
        } = requirement;
        let applicability = self.applicability.intern(Applicability::Context(guards))?;
        let requirement = RequirementCore {
            invalidated,
            consumer,
            condition,
            applicability,
        };
        Ok(requirement)
    }

    fn intern_requirement_core(
        &mut self,
        requirement: RequirementCore<'g>,
    ) -> Step<RequirementId<'g>> {
        let index = match self.requirement_values.get_index_of(&requirement) {
            Some(index) => index,
            None => {
                u32::try_from(self.requirement_values.len()).map_err(|_| CapacityError::Sets)?;
                {
                    self.work.requirement_nodes = self.work.requirement_nodes.saturating_add(1);
                    self.requirement_values.insert_full(requirement).0
                }
            }
        };
        Ok(RequirementId(index as u32, std::marker::PhantomData))
    }

    fn applicability_contains(
        &mut self,
        root: ApplicabilityId<'g>,
        target: ConditionId<'g>,
    ) -> Step<Option<()>> {
        Ok(self.applicability.contains(self.graph, root, target)?)
    }

    fn shared_requirement(
        &mut self,
        requirement: &RequirementCore<'g>,
        prefix: Sequence<'g, ConditionId<'g>>,
    ) -> Step<Option<SharedRequirement<'g>>> {
        self.work.sharing_probes = self.work.sharing_probes.saturating_add(1);
        if requirement.invalidated != Sequence::EMPTY {
            return Ok(None);
        }
        let key = (requirement.clone(), prefix);
        if let Some(sharing) = self.sharing_modes.get(&key).copied() {
            return Ok(Some(SharedRequirement {
                applicability: requirement.applicability,
                prefix,
                sharing,
            }));
        }
        // Unknown value inputs do not prevent storing one obligation with a
        // shared applicability expression. They only prevent the stronger
        // empty-context classification shortcut below.
        let empty = GuardContextId(Sequence::EMPTY);
        let first = self
            .applicability
            .first(self.graph, requirement.applicability)?;
        let first = self.graph.append(prefix, first)?;
        let mut sharing = Sharing::Contextual;
        let mut condition_independent = None;
        if let Truth::Unknown(_) = self.graph.truth(requirement.condition, &Sequence::EMPTY)? {
            // A first path is not a sharing certificate. Inspect the
            // applicability DAG's structural support once, without expanding
            // its path product. Guards that are already known require the
            // stronger value-disjoint proof below; unknown, structurally
            // independent guards are safe to share with opaque values.
            let probe = self.graph.push(Sequence::EMPTY, requirement.condition)?;
            let condition_support = self
                .graph
                .input_summary(NodeId::Condition(requirement.condition), InputUse::Value)?;
            condition_independent = (self.context(
                NodeId::Condition(requirement.condition),
                GuardContextId(probe),
            )? == empty)
                .then_some(());
            let mut stable = condition_independent;
            let mut pending = vec![Traversal::Visit(requirement.applicability)];
            let mut visited = FxHashSet::default();
            let prefix_guards = self.graph.items(prefix).copied().collect::<Vec<_>>();
            for guard in prefix_guards {
                if let Some(()) = self.graph.known(NodeId::Condition(guard)) {
                    stable = None;
                    break;
                }
                if self.context(NodeId::Condition(guard), GuardContextId(probe))? != empty {
                    stable = None;
                    break;
                }
                let guard_support = self
                    .graph
                    .input_summary(NodeId::Condition(guard), InputUse::Value)?;
                if let (Inputs::Known(condition), Inputs::Known(guard)) =
                    (condition_support, guard_support)
                    && let None = self.graph.independent_arguments(condition, guard)?
                {
                    stable = None;
                    break;
                }
            }
            while let Some(()) = stable {
                let Some(frame) = pending.pop() else {
                    break;
                };
                let id = match frame {
                    Traversal::Visit(id) | Traversal::Finish(id) => id,
                };
                if !visited.insert(id) {
                    continue;
                }
                let (guards, child) = match self.applicability[id] {
                    Applicability::Context(guards) => (guards, None),
                    Applicability::Prefix(guards, child) => (guards, Some(child)),
                    Applicability::Either(left, right) => {
                        pending.extend([Traversal::Visit(right), Traversal::Visit(left)]);
                        continue;
                    }
                };
                if let Some(child) = child {
                    pending.push(Traversal::Visit(child));
                }
                let guards = self.graph.items(guards).copied().collect::<Vec<_>>();
                for guard in guards {
                    if let Some(()) = self.graph.known(NodeId::Condition(guard)) {
                        stable = None;
                        break;
                    }
                    if self.context(NodeId::Condition(guard), GuardContextId(probe))? != empty {
                        stable = None;
                        break;
                    }
                    let guard_support = self
                        .graph
                        .input_summary(NodeId::Condition(guard), InputUse::Value)?;
                    if let (Inputs::Known(condition), Inputs::Known(guard)) =
                        (condition_support, guard_support)
                        && let None = self.graph.independent_arguments(condition, guard)?
                    {
                        stable = None;
                        break;
                    }
                }
            }
            if let Some(()) = stable {
                sharing = Sharing::Stable;
            }
        }
        let exact_guard = self
            .applicability_contains(requirement.applicability, requirement.condition)?
            .or_else(|| {
                self.graph
                    .items(prefix)
                    .copied()
                    .find(|condition| *condition == requirement.condition)
                    .map(|_| ())
            });
        if let Some(()) = exact_guard {
            sharing = Sharing::Contextual;
            condition_independent = None;
        }
        if first == Sequence::EMPTY {
            self.work.sharing_unknown_rejections =
                self.work.sharing_unknown_rejections.saturating_add(1);
        } else {
            let condition = self
                .graph
                .input_summary(NodeId::Condition(requirement.condition), InputUse::Value)?;
            let guards = self.applicability.inputs(
                self.graph,
                requirement.applicability,
                InputUse::Value,
            )?;
            let outer = self.graph.sequence_input_summary(
                crate::contracts::operations::InputSequence::Conditions(prefix),
                InputUse::Value,
            )?;
            if let Inputs::Known(condition) = condition
                && let Inputs::Known(guards) = self.graph.combine_inputs(guards, outer)?
            {
                let mut independent = condition_independent;
                if let None = self.graph.independent_arguments(condition, guards)? {
                    independent = None;
                }
                if let Some(()) = independent
                    && self.context(
                        NodeId::Condition(requirement.condition),
                        GuardContextId(first),
                    )? != empty
                {
                    independent = None;
                }
                if let Some(()) = independent {
                    self.work.sharing_proof_queries =
                        self.work.sharing_proof_queries.saturating_add(1);
                    if let Truth::Proven | Truth::Refuted =
                        self.graph.truth(requirement.condition, &Sequence::EMPTY)?
                    {
                        independent = None;
                    }
                }
                if let Some(()) = independent {
                    let outer_guards = self.graph.items(prefix).copied().collect::<Vec<_>>();
                    for guard in outer_guards {
                        if self.context(NodeId::Condition(guard), GuardContextId(first))? != empty {
                            independent = None;
                            break;
                        }
                    }
                }
                if let Some(()) = independent {
                    sharing = Sharing::Independent;
                }
                let mut pending = vec![Traversal::Visit(requirement.applicability)];
                let mut visited = FxHashSet::default();
                while let Some(frame) = pending.pop() {
                    let id = match frame {
                        Traversal::Visit(id) | Traversal::Finish(id) => id,
                    };
                    if let Traversal::Visit(_) = frame
                        && !visited.insert(id)
                    {
                        continue;
                    }
                    let node = self.applicability[id];
                    if let Traversal::Visit(_) = frame {
                        pending.push(Traversal::Finish(id));
                        match node {
                            Applicability::Context(_) => {}
                            Applicability::Prefix(_, child) => {
                                pending.push(Traversal::Visit(child))
                            }
                            Applicability::Either(left, right) => {
                                pending.extend([Traversal::Visit(right), Traversal::Visit(left)])
                            }
                        }
                        continue;
                    }
                    let guards = match node {
                        Applicability::Context(guards) | Applicability::Prefix(guards, _) => guards,
                        Applicability::Either(..) => Sequence::EMPTY,
                    };
                    let guards = self.graph.items(guards).copied().collect::<Vec<_>>();
                    for guard in guards {
                        if let Sharing::Independent = sharing {
                            if self.context(NodeId::Condition(guard), GuardContextId(first))?
                                != empty
                            {
                                sharing = Sharing::Contextual;
                            }
                        }
                    }
                }
            } else {
                self.work.sharing_unknown_rejections =
                    self.work.sharing_unknown_rejections.saturating_add(1);
            }
        }
        self.sharing_modes.insert(key, sharing);
        Ok(Some(SharedRequirement {
            applicability: requirement.applicability,
            prefix,
            sharing,
        }))
    }

    fn prune_applicability(&mut self, root: ApplicabilityId<'g>) -> Step<()> {
        let mut pending = vec![Traversal::Visit(root)];
        while let Some(frame) = pending.pop() {
            self.work.applicability_visits = self.work.applicability_visits.saturating_add(1);
            let id = match frame {
                Traversal::Visit(id) | Traversal::Finish(id) => id,
            };
            if let Some(ApplicabilityFacts {
                impossible: Some(_),
                ..
            }) = self.applicability_facts.get(&id)
            {
                continue;
            }
            let node = self.applicability[id];
            if let Traversal::Visit(_) = frame {
                pending.push(Traversal::Finish(id));
                match node {
                    Applicability::Context(_) => {}
                    Applicability::Prefix(_, child) => pending.push(Traversal::Visit(child)),
                    Applicability::Either(left, right) => {
                        pending.extend([Traversal::Visit(right), Traversal::Visit(left)])
                    }
                }
                continue;
            }
            let impossible = match node {
                Applicability::Context(guards) => {
                    let guards = self.resolve_guards(&guards)?;
                    match self.graph.conjunction(&guards, &Sequence::EMPTY)? {
                        Truth::Refuted => Some(()),
                        Truth::Proven | Truth::Unknown(_) => None,
                    }
                }
                Applicability::Prefix(guards, child) => match self.applicability_facts[&child]
                    .impossible
                    .expect("pruned child applicability")
                {
                    Some(()) => Some(()),
                    None => {
                        let guards = self.resolve_guards(&guards)?;
                        match self.graph.conjunction(&guards, &Sequence::EMPTY)? {
                            Truth::Refuted => Some(()),
                            Truth::Proven | Truth::Unknown(_) => None,
                        }
                    }
                },
                Applicability::Either(left, right) => match (
                    self.applicability_facts[&left]
                        .impossible
                        .expect("pruned left applicability"),
                    self.applicability_facts[&right]
                        .impossible
                        .expect("pruned right applicability"),
                ) {
                    (Some(()), Some(())) => Some(()),
                    (None, _) | (_, None) => None,
                },
            };
            self.applicability_facts.entry(id).or_default().impossible = Some(impossible);
        }
        Ok(())
    }

    pub fn finish_work(&mut self) -> crate::contracts::Work {
        self.applicability.record_work(&mut self.work);
        self.work.requirement_input_entries = self.requirement_inputs.len();
        self.work.plan_input_entries = self
            .plan_facts
            .values()
            .filter(|facts| facts.inputs.is_some())
            .count();
        self.work.plan_sequence_input_entries = self
            .plan_sequence_facts
            .values()
            .filter(|facts| facts.inputs.is_some())
            .count();

        self.work.input_visits = self.graph.substitution_work.input_visits;
        self.work.argument_projections = self.graph.substitution_work.argument_projections;
        self.work.argument_projection_positions =
            self.graph.substitution_work.argument_projection_positions;
        self.work.rewritten_nodes = self.graph.substitution_work.rewritten_nodes;
        self.work
    }

    fn report_expression_guard_dependence(&self, root: ExprId<'g>) -> GuardDependence {
        let mut pending = vec![root];
        let mut visited = FxHashSet::default();
        while let Some(expression) = pending.pop() {
            if !visited.insert(expression) {
                continue;
            }
            match self.graph[expression] {
                ExprNode::Select(..)
                | ExprNode::Range(..)
                | ExprNode::Test(_)
                | ExprNode::Alternatives(_) => return GuardDependence::Dependent,
                ExprNode::Element(..) => {
                    return GuardDependence::Element;
                }
                ExprNode::Arithmetic(
                    Arithmetic::Subtract(_) | Arithmetic::WrappingSubtract(_),
                    ..,
                ) => return GuardDependence::Dependent,
                ExprNode::Typed(_, value)
                | ExprNode::Field(value, _)
                | ExprNode::Length(value)
                | ExprNode::Trimmed(value) => pending.push(value),
                ExprNode::Arithmetic(Arithmetic::Add(_), left, right) => {
                    pending.extend([left, right]);
                }
                ExprNode::Found { text, pattern }
                | ExprNode::Matches { text, pattern }
                | ExprNode::Tokens {
                    text,
                    consumed: pattern,
                } => pending.extend([text, pattern]),
                ExprNode::MatchIndex {
                    text,
                    pattern,
                    occurrence,
                } => pending.extend([text, pattern, occurrence]),
                ExprNode::MatchEntry(TextMatchNode {
                    text,
                    pattern,
                    occurrence,
                }) => pending.extend([text, pattern, occurrence]),
                ExprNode::Token(TokenNode {
                    text,
                    start,
                    length,
                })
                | ExprNode::NextToken(TokenNode {
                    text,
                    start,
                    length,
                }) => pending.extend([text, start, length]),
                ExprNode::Slice { text, start, end } => pending.extend([text, start, end]),
                ExprNode::Partition {
                    sequence,
                    predicate,
                } => pending.extend([sequence, predicate]),
                ExprNode::Closure(_, values)
                | ExprNode::Aggregate(values)
                | ExprNode::Variant(_, _, values) => {
                    pending.extend(self.graph.items(values).copied())
                }
                ExprNode::Call(_, arguments, _) => {
                    pending.extend(self.graph.items(arguments).copied())
                }
                ExprNode::Serialized { value, .. } => pending.push(value),
                ExprNode::Unknown
                | ExprNode::Function(_)
                | ExprNode::Opaque(_)
                | ExprNode::Global(_)
                | ExprNode::Argument(_)
                | ExprNode::Number(_)
                | ExprNode::Text(_)
                | ExprNode::Cursor { .. } => {}
            }
        }
        GuardDependence::Independent
    }

    fn report_support_union(
        &mut self,
        left: ReportSupport<'g>,
        right: ReportSupport<'g>,
    ) -> ReportSupport<'g> {
        match (left, right) {
            (ReportSupport::Unknown, _) | (_, ReportSupport::Unknown) => ReportSupport::Unknown,
            (ReportSupport::Known(left), ReportSupport::Known(right)) => {
                if let ReportSupportTree::Empty = left.as_ref() {
                    return ReportSupport::Known(right);
                }
                if let ReportSupportTree::Empty = right.as_ref() {
                    return ReportSupport::Known(left);
                }
                if Rc::ptr_eq(&left, &right) {
                    return ReportSupport::Known(left);
                }
                let (left, right) = match Rc::as_ptr(&left).cmp(&Rc::as_ptr(&right)) {
                    std::cmp::Ordering::Greater => (right, left),
                    std::cmp::Ordering::Equal | std::cmp::Ordering::Less => (left, right),
                };
                let key = (Rc::as_ptr(&left) as usize, Rc::as_ptr(&right) as usize);
                if let Some(union) = self.report_support_union_cache.get(&key) {
                    return ReportSupport::Known(Rc::clone(union));
                }
                self.work.report_support_nodes = self.work.report_support_nodes.saturating_add(1);
                let union = Rc::new(ReportSupportTree::Union(left, right));
                self.report_support_union_cache
                    .insert(key, Rc::clone(&union));
                ReportSupport::Known(union)
            }
        }
    }

    fn report_support_location(
        &mut self,
        base: ExprId<'g>,
        fields: Vec<usize>,
    ) -> ReportSupport<'g> {
        let location = ReportLocation { base, fields };
        if let Some(support) = self.report_support_location_cache.get(&location) {
            return ReportSupport::Known(Rc::clone(support));
        }
        self.work.report_support_nodes = self.work.report_support_nodes.saturating_add(1);
        self.work.report_support_elements = self.work.report_support_elements.saturating_add(1);
        let support = Rc::new(ReportSupportTree::Location(location.clone()));
        self.report_support_location_cache
            .insert(location, Rc::clone(&support));
        ReportSupport::Known(support)
    }

    fn report_expression_support(&mut self, root: ExprId<'g>) -> ReportSupport<'g> {
        if let Some(support) = self.report_expression_supports.get(&root) {
            return support.clone();
        }
        enum Work<'g> {
            Visit(ExprId<'g>),
            Build(ExprId<'g>),
        }
        let mut pending = vec![Work::Visit(root)];
        let mut scheduled = FxHashSet::default();
        while let Some(work) = pending.pop() {
            let expression = match work {
                Work::Visit(expression) | Work::Build(expression) => expression,
            };
            match work {
                Work::Visit(_) => {
                    self.work.report_support_visits =
                        self.work.report_support_visits.saturating_add(1);
                    if self.report_expression_supports.contains_key(&expression)
                        || !scheduled.insert(expression)
                    {
                        continue;
                    }
                    if let Some((base, fields)) = self.graph.location(expression) {
                        let location = self.report_support_location(base, fields);
                        self.report_expression_supports.insert(expression, location);
                        continue;
                    }
                    pending.push(Work::Build(expression));
                    match self.graph[expression] {
                        ExprNode::Typed(_, value)
                        | ExprNode::Field(value, _)
                        | ExprNode::Length(value)
                        | ExprNode::Trimmed(value)
                        | ExprNode::Serialized { value, .. } => pending.push(Work::Visit(value)),
                        ExprNode::Element(base, index) | ExprNode::Arithmetic(_, base, index) => {
                            pending.extend([Work::Visit(index), Work::Visit(base)])
                        }
                        ExprNode::Found { text, pattern }
                        | ExprNode::Matches { text, pattern }
                        | ExprNode::Tokens {
                            text,
                            consumed: pattern,
                        } => pending.extend([Work::Visit(pattern), Work::Visit(text)]),
                        ExprNode::MatchIndex {
                            text,
                            pattern,
                            occurrence,
                        } => pending.extend([
                            Work::Visit(occurrence),
                            Work::Visit(pattern),
                            Work::Visit(text),
                        ]),
                        ExprNode::MatchEntry(TextMatchNode {
                            text,
                            pattern,
                            occurrence,
                        }) => pending.extend([
                            Work::Visit(occurrence),
                            Work::Visit(pattern),
                            Work::Visit(text),
                        ]),
                        ExprNode::Token(TokenNode {
                            text,
                            start,
                            length,
                        })
                        | ExprNode::NextToken(TokenNode {
                            text,
                            start,
                            length,
                        }) => pending.extend([
                            Work::Visit(length),
                            Work::Visit(start),
                            Work::Visit(text),
                        ]),
                        ExprNode::Slice { text, start, end } => pending.extend([
                            Work::Visit(end),
                            Work::Visit(start),
                            Work::Visit(text),
                        ]),
                        ExprNode::Partition {
                            sequence,
                            predicate,
                        } => pending.extend([Work::Visit(predicate), Work::Visit(sequence)]),
                        ExprNode::Closure(_, values)
                        | ExprNode::Aggregate(values)
                        | ExprNode::Variant(_, _, values) => {
                            pending.extend(self.graph.items(values).copied().rev().map(Work::Visit))
                        }
                        ExprNode::Select(_, yes, no) => {
                            pending.extend([Work::Visit(no), Work::Visit(yes)])
                        }
                        ExprNode::Call(..)
                        | ExprNode::Alternatives(_)
                        | ExprNode::Global(_)
                        | ExprNode::Range(_)
                        | ExprNode::Cursor { .. }
                        | ExprNode::Unknown
                        | ExprNode::Test(_)
                        | ExprNode::Opaque(_)
                        | ExprNode::Function(_)
                        | ExprNode::Argument(_)
                        | ExprNode::Number(_)
                        | ExprNode::Text(_) => {}
                    }
                }
                Work::Build(_) => {
                    let support = match self.graph[expression] {
                        ExprNode::Call(..)
                        | ExprNode::Alternatives(_)
                        | ExprNode::Global(_)
                        | ExprNode::Range(_)
                        | ExprNode::Cursor { .. }
                        | ExprNode::Unknown => ReportSupport::Unknown,
                        ExprNode::Opaque(_) => {
                            let location = self.report_support_location(expression, Vec::new());
                            location
                        }
                        ExprNode::Select(test, yes, no) => {
                            let test = self.report_condition_support(test);
                            let yes = self.report_expression_supports[&yes].clone();
                            let no = self.report_expression_supports[&no].clone();
                            let branches = self.report_support_union(yes, no);
                            let branches = self.report_support_union(test, branches);
                            branches
                        }
                        ExprNode::Test(test) => self.report_condition_support(test),
                        ExprNode::Typed(_, value)
                        | ExprNode::Field(value, _)
                        | ExprNode::Length(value)
                        | ExprNode::Trimmed(value)
                        | ExprNode::Serialized { value, .. } => {
                            self.report_expression_supports[&value].clone()
                        }
                        ExprNode::Element(base, index) | ExprNode::Arithmetic(_, base, index) => {
                            let base = self.report_expression_supports[&base].clone();
                            let index = self.report_expression_supports[&index].clone();
                            self.report_support_union(base, index)
                        }
                        ExprNode::Found { text, pattern }
                        | ExprNode::Matches { text, pattern }
                        | ExprNode::Tokens {
                            text,
                            consumed: pattern,
                        } => {
                            let text = self.report_expression_supports[&text].clone();
                            let pattern = self.report_expression_supports[&pattern].clone();
                            self.report_support_union(text, pattern)
                        }
                        ExprNode::MatchIndex {
                            text,
                            pattern,
                            occurrence,
                        } => {
                            let text = self.report_expression_supports[&text].clone();
                            let pattern = self.report_expression_supports[&pattern].clone();
                            let occurrence = self.report_expression_supports[&occurrence].clone();
                            let support = self.report_support_union(text, pattern);
                            self.report_support_union(support, occurrence)
                        }
                        ExprNode::MatchEntry(TextMatchNode {
                            text,
                            pattern,
                            occurrence,
                        }) => {
                            let text = self.report_expression_supports[&text].clone();
                            let pattern = self.report_expression_supports[&pattern].clone();
                            let occurrence = self.report_expression_supports[&occurrence].clone();
                            let support = self.report_support_union(text, pattern);
                            self.report_support_union(support, occurrence)
                        }
                        ExprNode::Token(TokenNode {
                            text,
                            start,
                            length,
                        })
                        | ExprNode::NextToken(TokenNode {
                            text,
                            start,
                            length,
                        }) => {
                            let text = self.report_expression_supports[&text].clone();
                            let start = self.report_expression_supports[&start].clone();
                            let length = self.report_expression_supports[&length].clone();
                            let support = self.report_support_union(text, start);
                            let support = self.report_support_union(support, length);
                            support
                        }
                        ExprNode::Slice { text, start, end } => {
                            let text = self.report_expression_supports[&text].clone();
                            let start = self.report_expression_supports[&start].clone();
                            let end = self.report_expression_supports[&end].clone();
                            let support = self.report_support_union(text, start);
                            self.report_support_union(support, end)
                        }
                        ExprNode::Partition {
                            sequence,
                            predicate,
                        } => {
                            let sequence = self.report_expression_supports[&sequence].clone();
                            let predicate = self.report_expression_supports[&predicate].clone();
                            self.report_support_union(sequence, predicate)
                        }
                        ExprNode::Closure(_, values)
                        | ExprNode::Aggregate(values)
                        | ExprNode::Variant(_, _, values) => {
                            let values = self.graph.items(values).copied().collect::<Vec<_>>();
                            let mut support =
                                ReportSupport::Known(Rc::clone(&self.report_support_empty_node));
                            for value in values {
                                let value = self.report_expression_supports[&value].clone();
                                support = self.report_support_union(support, value);
                            }
                            support
                        }
                        ExprNode::Function(_)
                        | ExprNode::Argument(_)
                        | ExprNode::Number(_)
                        | ExprNode::Text(_) => {
                            ReportSupport::Known(Rc::clone(&self.report_support_empty_node))
                        }
                    };
                    self.report_expression_supports.insert(expression, support);
                }
            }
        }
        self.report_expression_supports[&root].clone()
    }

    fn report_condition_support(&mut self, condition: ConditionId<'g>) -> ReportSupport<'g> {
        if let Some(ConditionFacts {
            support: Some(support),
            ..
        }) = self.report_condition_facts.get(&condition)
        {
            return support.clone();
        }
        self.work.report_support_visits = self.work.report_support_visits.saturating_add(1);
        let support = match self.graph[condition] {
            ConditionNode::Compare(_, left, right)
            | ConditionNode::Boundary(left, right)
            | ConditionNode::NotBoundary(left, right) => {
                let left = self.report_expression_support(left);
                let right = self.report_expression_support(right);
                self.report_support_union(left, right)
            }
            ConditionNode::Variant(value, _) | ConditionNode::NotVariant(value, _) => {
                self.report_expression_support(value)
            }
            ConditionNode::Unknown | ConditionNode::Returned(..) => ReportSupport::Unknown,
        };
        self.report_condition_facts
            .entry(condition)
            .or_default()
            .support = Some(support.clone());
        self.work.report_support_entries = self.work.report_support_entries.saturating_add(1);
        support
    }

    fn report_condition_sequence_support(
        &mut self,
        guards: Sequence<'g, ConditionId<'g>>,
    ) -> ReportSupport<'g> {
        let conditions = self.graph.items(guards).copied().collect::<Vec<_>>();
        let mut support = ReportSupport::Known(Rc::clone(&self.report_support_empty_node));
        for condition in conditions {
            let condition = self.report_condition_support(condition);
            support = self.report_support_union(support, condition);
        }
        support
    }

    fn report_locations_overlap(
        left: &ReportLocation<'g>,
        right: &ReportLocation<'g>,
    ) -> Option<()> {
        if left.base == right.base
            && (left.fields.starts_with(&right.fields) || right.fields.starts_with(&left.fields))
        {
            Some(())
        } else {
            None
        }
    }

    fn report_support_overlaps(
        &mut self,
        support: &Rc<ReportSupportTree<'g>>,
        location: &ReportLocation<'g>,
    ) -> Option<()> {
        enum Work<'g> {
            Visit(Rc<ReportSupportTree<'g>>),
            Finish(Rc<ReportSupportTree<'g>>),
        }
        let mut pending = vec![Work::Visit(Rc::clone(support))];
        while let Some(work) = pending.pop() {
            self.work.report_support_overlap_visits =
                self.work.report_support_overlap_visits.saturating_add(1);
            let node = match &work {
                Work::Visit(node) | Work::Finish(node) => Rc::clone(node),
            };
            let key = (Rc::as_ptr(&node) as usize, location.clone());
            match work {
                Work::Visit(_) => {
                    if let Some(_) = self.report_support_overlap_cache.get(&key) {
                        continue;
                    }
                    pending.push(Work::Finish(Rc::clone(&node)));
                    if let ReportSupportTree::Union(left, right) = node.as_ref() {
                        pending.push(Work::Visit(Rc::clone(right)));
                        pending.push(Work::Visit(Rc::clone(left)));
                    }
                }
                Work::Finish(_) => {
                    let result = match node.as_ref() {
                        ReportSupportTree::Empty => None,
                        ReportSupportTree::Location(other) => {
                            Self::report_locations_overlap(location, other)
                        }
                        ReportSupportTree::Union(left, right) => {
                            let left_key = (Rc::as_ptr(left) as usize, location.clone());
                            let right_key = (Rc::as_ptr(right) as usize, location.clone());
                            match self.report_support_overlap_cache.get(&left_key) {
                                Some(Some(())) => Some(()),
                                Some(None) => self
                                    .report_support_overlap_cache
                                    .get(&right_key)
                                    .copied()
                                    .flatten(),
                                None => unreachable!("support child overlap was visited"),
                            }
                        }
                    };
                    self.report_support_overlap_cache.insert(key, result);
                }
            }
        }
        self.report_support_overlap_cache
            .get(&(Rc::as_ptr(support) as usize, location.clone()))
            .copied()
            .flatten()
    }

    fn report_support_trees_overlap(
        &mut self,
        left: &Rc<ReportSupportTree<'g>>,
        target: &Rc<ReportSupportTree<'g>>,
    ) -> Option<()> {
        let left_key = Rc::as_ptr(left) as usize;
        let target_key = Rc::as_ptr(target) as usize;
        let key = match left_key.cmp(&target_key) {
            std::cmp::Ordering::Greater => (target_key, left_key),
            std::cmp::Ordering::Equal | std::cmp::Ordering::Less => (left_key, target_key),
        };
        if let Some(overlap) = self.report_support_tree_overlap_cache.get(&key) {
            return *overlap;
        }
        let mut pending = vec![Rc::clone(left)];
        let mut visited = FxHashSet::default();
        let overlap = loop {
            let Some(node) = pending.pop() else {
                break None;
            };
            self.work.report_support_overlap_visits =
                self.work.report_support_overlap_visits.saturating_add(1);
            let node_key = Rc::as_ptr(&node) as usize;
            if !visited.insert(node_key) {
                continue;
            }
            match node.as_ref() {
                ReportSupportTree::Empty => {}
                ReportSupportTree::Location(location) => {
                    if let Some(()) = self.report_support_overlaps(target, location) {
                        break Some(());
                    }
                }
                ReportSupportTree::Union(left, right) => {
                    pending.extend([Rc::clone(right), Rc::clone(left)]);
                }
            }
        };
        self.report_support_tree_overlap_cache.insert(key, overlap);
        overlap
    }

    fn report_support_contains_location(
        &mut self,
        target: &Rc<ReportSupportTree<'g>>,
        location: &ReportLocation<'g>,
    ) -> Option<()> {
        enum Work<'g> {
            Visit(Rc<ReportSupportTree<'g>>),
            Build(Rc<ReportSupportTree<'g>>),
        }
        let key = (Rc::as_ptr(target) as usize, location.clone());
        if let Some(contained) = self.report_support_contains_location_cache.get(&key) {
            return *contained;
        }
        let mut pending = vec![Work::Visit(Rc::clone(target))];
        while let Some(work) = pending.pop() {
            self.work.report_support_overlap_visits =
                self.work.report_support_overlap_visits.saturating_add(1);
            match work {
                Work::Visit(node) => {
                    let key = (Rc::as_ptr(&node) as usize, location.clone());
                    if self
                        .report_support_contains_location_cache
                        .contains_key(&key)
                    {
                        continue;
                    }
                    pending.push(Work::Build(Rc::clone(&node)));
                    if let ReportSupportTree::Union(left, right) = node.as_ref() {
                        pending
                            .extend([Work::Visit(Rc::clone(right)), Work::Visit(Rc::clone(left))]);
                    }
                }
                Work::Build(node) => {
                    let contained = match node.as_ref() {
                        ReportSupportTree::Empty => None,
                        ReportSupportTree::Location(target) => {
                            if target.base == location.base
                                && location.fields.starts_with(&target.fields)
                            {
                                Some(())
                            } else {
                                None
                            }
                        }
                        ReportSupportTree::Union(left, right) => {
                            let left = self.report_support_contains_location_cache
                                [&(Rc::as_ptr(left) as usize, location.clone())];
                            let right = self.report_support_contains_location_cache
                                [&(Rc::as_ptr(right) as usize, location.clone())];
                            match (left, right) {
                                (Some(()), _) | (_, Some(())) => Some(()),
                                (None, None) => None,
                            }
                        }
                    };
                    self.report_support_contains_location_cache
                        .insert((Rc::as_ptr(&node) as usize, location.clone()), contained);
                }
            }
        }
        self.report_support_contains_location_cache
            .get(&key)
            .copied()
            .flatten()
    }

    fn report_support_tree_within(
        &mut self,
        support: &Rc<ReportSupportTree<'g>>,
        target: &Rc<ReportSupportTree<'g>>,
    ) -> Option<()> {
        enum Work<'g> {
            Visit(Rc<ReportSupportTree<'g>>),
            Build(Rc<ReportSupportTree<'g>>),
        }
        let key = (Rc::as_ptr(support) as usize, Rc::as_ptr(target) as usize);
        if let Some(contained) = self.report_support_containment_cache.get(&key) {
            return *contained;
        }
        let target_key = Rc::as_ptr(target) as usize;
        let mut pending = vec![Work::Visit(Rc::clone(support))];
        while let Some(work) = pending.pop() {
            self.work.report_support_overlap_visits =
                self.work.report_support_overlap_visits.saturating_add(1);
            match work {
                Work::Visit(node) => {
                    let key = (Rc::as_ptr(&node) as usize, target_key);
                    if self.report_support_containment_cache.contains_key(&key) {
                        continue;
                    }
                    pending.push(Work::Build(Rc::clone(&node)));
                    if let ReportSupportTree::Union(left, right) = node.as_ref() {
                        pending
                            .extend([Work::Visit(Rc::clone(right)), Work::Visit(Rc::clone(left))]);
                    }
                }
                Work::Build(node) => {
                    let contained = match node.as_ref() {
                        ReportSupportTree::Empty => Some(()),
                        ReportSupportTree::Location(location) => {
                            self.report_support_contains_location(target, location)
                        }
                        ReportSupportTree::Union(left, right) => {
                            let left = self.report_support_containment_cache
                                [&(Rc::as_ptr(left) as usize, target_key)];
                            let right = self.report_support_containment_cache
                                [&(Rc::as_ptr(right) as usize, target_key)];
                            match (left, right) {
                                (Some(()), Some(())) => Some(()),
                                (None, _) | (_, None) => None,
                            }
                        }
                    };
                    self.report_support_containment_cache
                        .insert((Rc::as_ptr(&node) as usize, target_key), contained);
                }
            }
        }
        self.report_support_containment_cache
            .get(&key)
            .copied()
            .flatten()
    }

    fn report_applicability_support(&mut self, root: ApplicabilityId<'g>) -> ReportSupport<'g> {
        enum Work<'g> {
            Visit(ApplicabilityId<'g>),
            Build(ApplicabilityId<'g>),
        }
        if let Some(ApplicabilityFacts {
            support: Some(support),
            ..
        }) = self.applicability_facts.get(&root)
        {
            return support.clone();
        }
        let mut pending = vec![Work::Visit(root)];
        while let Some(work) = pending.pop() {
            self.work.report_support_visits = self.work.report_support_visits.saturating_add(1);
            match work {
                Work::Visit(id) => {
                    if let Some(ApplicabilityFacts {
                        support: Some(_),
                        ..
                    }) = self.applicability_facts.get(&id)
                    {
                        continue;
                    }
                    pending.push(Work::Build(id));
                    match self.applicability[id] {
                        Applicability::Context(_) => {}
                        Applicability::Prefix(_, child) => pending.push(Work::Visit(child)),
                        Applicability::Either(left, right) => {
                            pending.extend([Work::Visit(right), Work::Visit(left)])
                        }
                    }
                }
                Work::Build(id) => {
                    let own = match self.applicability[id] {
                        Applicability::Context(guards) | Applicability::Prefix(guards, _) => {
                            self.report_condition_sequence_support(guards)
                        }
                        Applicability::Either(..) => {
                            ReportSupport::Known(Rc::clone(&self.report_support_empty_node))
                        }
                    };
                    let support = match self.applicability[id] {
                        Applicability::Context(_) => own,
                        Applicability::Prefix(_, child) => {
                            let child = self.applicability_facts[&child]
                                .support
                                .clone()
                                .expect("child applicability support is built");
                            self.report_support_union(own, child)
                        }
                        Applicability::Either(left, right) => {
                            let left = self.applicability_facts[&left]
                                .support
                                .clone()
                                .expect("left applicability support is built");
                            let right = self.applicability_facts[&right]
                                .support
                                .clone()
                                .expect("right applicability support is built");
                            self.report_support_union(left, right)
                        }
                    };
                    self.applicability_facts.entry(id).or_default().support = Some(support);
                    self.work.report_support_retained =
                        self.work.report_support_retained.saturating_add(1);
                    self.work.report_support_entries =
                        self.work.report_support_entries.saturating_add(1);
                }
            }
        }
        self.applicability_facts[&root]
            .support
            .clone()
            .expect("root applicability support is built")
    }

    fn report_project_prefix(
        &mut self,
        condition: ConditionId<'g>,
        prefix: Sequence<'g, ConditionId<'g>>,
        target: &ReportSupport<'g>,
        remaining: &ReportSupport<'g>,
    ) -> Step<Sequence<'g, ConditionId<'g>>> {
        self.work.report_projection_visits = self.work.report_projection_visits.saturating_add(1);
        let allocated_before =
            crate::sequence::Sequences::<ConditionId>::allocated_nodes(self.graph.as_ref());
        let (ReportSupport::Known(target), ReportSupport::Known(remaining)) = (target, remaining)
        else {
            return Ok(prefix);
        };
        let combined = self.report_support_union(
            ReportSupport::Known(Rc::clone(target)),
            ReportSupport::Known(Rc::clone(remaining)),
        );
        let ReportSupport::Known(combined) = combined else {
            unreachable!("known support unions remain known")
        };
        let mut projected = Sequence::EMPTY;
        let guards = self.graph.items(prefix).copied().collect::<Vec<_>>();
        self.work.report_projection_guards = self
            .work
            .report_projection_guards
            .saturating_add(guards.len());
        enum ProjectedGuard<'g> {
            Keep,
            Check(ReportLocation<'g>),
        }
        let mut projected_guards = Vec::with_capacity(guards.len());
        for &guard in &guards {
            let ReportSupport::Known(support) = self.report_condition_support(guard) else {
                return Ok(prefix);
            };
            let projected = match support.as_ref() {
                ReportSupportTree::Empty => ProjectedGuard::Keep,
                ReportSupportTree::Location(location) => ProjectedGuard::Check(location.clone()),
                ReportSupportTree::Union(..) => {
                    if let Some(()) = self.report_support_tree_within(&support, &combined) {
                        ProjectedGuard::Keep
                    } else {
                        return Ok(prefix);
                    }
                }
            };
            projected_guards.push((guard, projected));
        }
        for (guard, projected_guard) in projected_guards {
            match projected_guard {
                ProjectedGuard::Keep => {
                    projected = self.graph.push(projected, guard)?;
                }
                ProjectedGuard::Check(location) => {
                    let mut overlap = None;
                    if let Some(()) = self.report_support_overlaps(target, &location) {
                        overlap = Some(());
                    } else if let Some(()) = self.report_support_overlaps(remaining, &location) {
                        overlap = Some(());
                    }
                    if let Some(()) = overlap {
                        projected = self.graph.push(projected, guard)?;
                    }
                }
            }
        }
        let result = if crate::sequence::Sequences::len(self.graph.as_ref(), projected) > 0
            && self.context(NodeId::Condition(condition), GuardContextId(prefix))?
                != GuardContextId(Sequence::EMPTY)
        {
            prefix
        } else {
            projected
        };
        self.work.report_projection_storage = self.work.report_projection_storage.saturating_add(
            (allocated_before
                ..crate::sequence::Sequences::<ConditionId>::allocated_nodes(self.graph.as_ref()))
                .len(),
        );
        Ok(result)
    }

    fn report_project_guard_sequence(
        &mut self,
        guards: Sequence<'g, ConditionId<'g>>,
        target: &Rc<ReportSupportTree<'g>>,
    ) -> Step<Option<Sequence<'g, ConditionId<'g>>>> {
        self.work.report_projection_visits = self.work.report_projection_visits.saturating_add(1);
        let target_key = Rc::as_ptr(target) as usize;
        let key = (target_key, guards);
        if let Some(projected) = self.report_guard_projection_cache.get(&key) {
            return Ok(*projected);
        }
        enum Work<'g> {
            Visit(Sequence<'g, ConditionId<'g>>),
            Build(
                Sequence<'g, ConditionId<'g>>,
                Sequence<'g, ConditionId<'g>>,
                Sequence<'g, ConditionId<'g>>,
            ),
        }
        let mut local = FxHashMap::default();
        let mut pending = vec![Work::Visit(guards)];
        while let Some(work) = pending.pop() {
            self.work.report_projection_visits =
                self.work.report_projection_visits.saturating_add(1);
            match work {
                Work::Visit(sequence) => {
                    if local.contains_key(&sequence) {
                        continue;
                    }
                    if let Some(projected) = self
                        .report_guard_projection_cache
                        .get(&(target_key, sequence))
                    {
                        local.insert(sequence, *projected);
                        continue;
                    }
                    match crate::sequence::Sequences::parts(self.graph.as_mut(), sequence)? {
                        crate::sequence::Parts::Empty => {
                            self.report_guard_projection_cache
                                .insert((target_key, sequence), Some(Sequence::EMPTY));
                            local.insert(sequence, Some(Sequence::EMPTY));
                        }
                        crate::sequence::Parts::Leaf(guard) => {
                            self.work.report_projection_guards =
                                self.work.report_projection_guards.saturating_add(1);
                            let projected = match self.report_condition_support(guard) {
                                ReportSupport::Unknown => None,
                                ReportSupport::Known(support) => match support.as_ref() {
                                    ReportSupportTree::Empty => Some(Sequence::EMPTY),
                                    ReportSupportTree::Location(location) => {
                                        if let Some(()) =
                                            self.report_support_overlaps(target, location)
                                        {
                                            Some(self.graph.push(Sequence::EMPTY, guard)?)
                                        } else {
                                            Some(Sequence::EMPTY)
                                        }
                                    }
                                    ReportSupportTree::Union(..) => {
                                        if let Some(()) =
                                            self.report_support_tree_within(&support, target)
                                        {
                                            Some(self.graph.push(Sequence::EMPTY, guard)?)
                                        } else {
                                            None
                                        }
                                    }
                                },
                            };
                            self.report_guard_projection_cache
                                .insert((target_key, sequence), projected);
                            local.insert(sequence, projected);
                        }
                        crate::sequence::Parts::Branch(left, right) => {
                            pending.push(Work::Build(sequence, left, right));
                            pending.extend([Work::Visit(right), Work::Visit(left)]);
                        }
                    }
                }
                Work::Build(sequence, left, right) => {
                    let projected = match (local[&left], local[&right]) {
                        (Some(left), Some(right)) => Some(self.graph.append(left, right)?),
                        (None, _) | (_, None) => None,
                    };
                    self.report_guard_projection_cache
                        .insert((target_key, sequence), projected);
                    local.insert(sequence, projected);
                }
            }
        }
        Ok(local[&guards])
    }

    fn report_uniform_context(
        &mut self,
        condition: ConditionId<'g>,
        root: ApplicabilityId<'g>,
    ) -> Step<Option<Sequence<'g, ConditionId<'g>>>> {
        if let Some(context) = self.report_uniform_contexts.get(&(condition, root)) {
            return Ok(*context);
        }
        let ReportSupport::Known(target) = self.report_condition_support(condition) else {
            self.report_uniform_contexts.insert((condition, root), None);
            return Ok(None);
        };
        let allocated_before =
            crate::sequence::Sequences::<ConditionId>::allocated_nodes(self.graph.as_ref());
        enum Work<'g> {
            Visit(ApplicabilityId<'g>),
            Build(ApplicabilityId<'g>),
        }
        let mut local = FxHashMap::default();
        let mut pending = vec![Work::Visit(root)];
        while let Some(work) = pending.pop() {
            self.work.report_projection_visits =
                self.work.report_projection_visits.saturating_add(1);
            let id = match work {
                Work::Visit(id) | Work::Build(id) => id,
            };
            match work {
                Work::Visit(_)
                    if let Some(context) = self.report_uniform_contexts.get(&(condition, id)) =>
                {
                    local.insert(id, *context);
                }
                Work::Visit(_) if local.contains_key(&id) => {}
                Work::Visit(_) => {
                    pending.push(Work::Build(id));
                    match self.applicability[id] {
                        Applicability::Context(_) => {}
                        Applicability::Prefix(_, child) => pending.push(Work::Visit(child)),
                        Applicability::Either(left, right) => {
                            pending.extend([Work::Visit(right), Work::Visit(left)])
                        }
                    }
                }
                Work::Build(id) => {
                    let projected = match self.applicability[id] {
                        Applicability::Context(guards) => {
                            self.report_project_guard_sequence(guards, &target)?
                        }
                        Applicability::Prefix(guards, child) => {
                            let own = self.report_project_guard_sequence(guards, &target)?;
                            match (own, local[&child]) {
                                (Some(own), Some(child)) => Some(self.graph.append(own, child)?),
                                (None, _) | (_, None) => None,
                            }
                        }
                        Applicability::Either(left, right) => match (local[&left], local[&right]) {
                            (Some(left), Some(right)) if left == right => Some(left),
                            _ => None,
                        },
                    };
                    local.insert(id, projected);
                }
            }
        }
        let result = local[&root];
        for (id, context) in local {
            self.report_uniform_contexts
                .insert((condition, id), context);
        }
        self.work.report_projection_storage = self.work.report_projection_storage.saturating_add(
            (allocated_before
                ..crate::sequence::Sequences::<ConditionId>::allocated_nodes(self.graph.as_ref()))
                .len(),
        );
        Ok(result)
    }

    fn report_path_status(
        &mut self,
        prefix: Sequence<'g, ConditionId<'g>>,
    ) -> Step<ReportPathStatus> {
        Ok(match self.graph.conjunction(&prefix, &Sequence::EMPTY)? {
            Truth::Proven => ReportPathStatus::Proven,
            Truth::Refuted => ReportPathStatus::Refuted,
            Truth::Unknown(gap) => ReportPathStatus::Unknown(gap),
        })
    }

    fn report_expression_merge_shape(&self, root: ExprId<'g>) -> Option<()> {
        let mut pending = vec![root];
        let mut visited = FxHashSet::default();
        while let Some(expression) = pending.pop() {
            if !visited.insert(expression) {
                continue;
            }
            match self.graph[expression] {
                ExprNode::Select(..)
                | ExprNode::Range(..)
                | ExprNode::Test(_)
                | ExprNode::Alternatives(_)
                | ExprNode::Field(..)
                | ExprNode::Element(..)
                | ExprNode::Call(..)
                | ExprNode::MatchEntry(_)
                | ExprNode::Token(_)
                | ExprNode::NextToken(_) => return None,
                ExprNode::Typed(_, value) | ExprNode::Length(value) | ExprNode::Trimmed(value) => {
                    pending.push(value)
                }
                ExprNode::Arithmetic(_, left, right) => pending.extend([left, right]),
                ExprNode::Found { text, pattern }
                | ExprNode::Matches { text, pattern }
                | ExprNode::Tokens {
                    text,
                    consumed: pattern,
                } => pending.extend([text, pattern]),
                ExprNode::MatchIndex {
                    text,
                    pattern,
                    occurrence,
                } => pending.extend([text, pattern, occurrence]),
                ExprNode::Slice { text, start, end } => pending.extend([text, start, end]),
                ExprNode::Partition {
                    sequence,
                    predicate,
                } => pending.extend([sequence, predicate]),
                ExprNode::Closure(_, values)
                | ExprNode::Aggregate(values)
                | ExprNode::Variant(_, _, values) => {
                    pending.extend(self.graph.items(values).copied())
                }
                ExprNode::Serialized { value, .. } => pending.push(value),
                ExprNode::Unknown
                | ExprNode::Function(_)
                | ExprNode::Opaque(_)
                | ExprNode::Global(_)
                | ExprNode::Argument(_)
                | ExprNode::Number(_)
                | ExprNode::Text(_)
                | ExprNode::Cursor { .. } => {}
            }
        }
        Some(())
    }

    fn report_path_merge_context(
        &mut self,
        condition: ConditionId<'g>,
        guards: Sequence<'g, ConditionId<'g>>,
    ) -> Step<Option<GuardContextId<'g>>> {
        let guard_context = GuardContextId(guards);
        if self.context(NodeId::Condition(condition), guard_context)?
            != GuardContextId(Sequence::EMPTY)
        {
            return Ok(None);
        }
        let shape = match self.graph[condition] {
            ConditionNode::Compare(_, left, right) => match (
                self.report_expression_merge_shape(left),
                self.report_expression_merge_shape(right),
            ) {
                (Some(()), Some(())) => Some(()),
                _ => None,
            },
            ConditionNode::Variant(value, _) | ConditionNode::NotVariant(value, _) => {
                self.report_expression_merge_shape(value)
            }
            ConditionNode::Unknown
            | ConditionNode::Boundary(..)
            | ConditionNode::NotBoundary(..)
            | ConditionNode::Returned(..) => None,
        };
        let Some(()) = shape else {
            return Ok(None);
        };
        let condition_inputs = self
            .graph
            .input_summary(NodeId::Condition(condition), InputUse::Substitution)?;
        let guard_inputs = self.graph.sequence_input_summary(
            crate::contracts::operations::InputSequence::Conditions(guards),
            InputUse::Substitution,
        )?;
        let (Inputs::Known(condition_inputs), Inputs::Known(guard_inputs)) =
            (condition_inputs, guard_inputs)
        else {
            return Ok(None);
        };
        if let None = self
            .graph
            .independent_arguments(condition_inputs, guard_inputs)?
        {
            return Ok(None);
        }
        Ok(Some(GuardContextId(Sequence::EMPTY)))
    }

    fn report_condition_context_probe(&mut self, condition: ConditionId<'g>) -> Step<Option<()>> {
        if let Some(ConditionFacts {
            context: Some(context),
            ..
        }) = self.report_condition_facts.get(&condition)
        {
            return Ok(*context);
        }
        let probe = self.graph.push(Sequence::EMPTY, condition)?;
        if self.context(NodeId::Condition(condition), GuardContextId(probe))?
            != GuardContextId(Sequence::EMPTY)
        {
            self.report_condition_facts
                .entry(condition)
                .or_default()
                .context = Some(None);
            return Ok(None);
        }
        self.report_condition_facts
            .entry(condition)
            .or_default()
            .context = Some(Some(()));
        Ok(Some(()))
    }

    // A context-independent non-Proven guard remains a blocker after resolution.
    fn report_guard_sequence_blocks_proven_path(
        &mut self,
        guards: Sequence<'g, ConditionId<'g>>,
    ) -> Step<Option<()>> {
        if let Some(result) = self.report_guard_sequence_blockers.get(&guards) {
            return Ok(*result);
        }
        let sequence = guards;
        let mut guards = self.graph.scan(sequence);
        while let Some(guard) = guards.next() {
            self.work.report_path_certificate_guard_visits = self
                .work
                .report_path_certificate_guard_visits
                .saturating_add(1);
            if let Some(()) = self.report_condition_context_probe(guard)? {
                match self.graph.truth(guard, &Sequence::EMPTY)? {
                    Truth::Proven => {}
                    Truth::Refuted | Truth::Unknown(_) => {
                        self.report_guard_sequence_blockers
                            .insert(sequence, Some(()));
                        return Ok(Some(()));
                    }
                }
            }
        }
        let result = None;
        self.report_guard_sequence_blockers.insert(sequence, result);
        Ok(result)
    }

    fn report_applicability_has_no_proven_guard_path(
        &mut self,
        root: ApplicabilityId<'g>,
    ) -> Step<Option<()>> {
        #[derive(Clone, Copy)]
        enum Work<'g> {
            Visit(ApplicabilityId<'g>),
            Prefix(ApplicabilityId<'g>, ApplicabilityId<'g>),
            EitherLeft(
                ApplicabilityId<'g>,
                ApplicabilityId<'g>,
                ApplicabilityId<'g>,
            ),
            EitherRight(ApplicabilityId<'g>, ApplicabilityId<'g>),
        }
        if let Some(ApplicabilityFacts {
            no_proven_guard_path: Some(result),
            ..
        }) = self.applicability_facts.get(&root)
        {
            return Ok(*result);
        }
        let mut local = FxHashMap::default();
        let mut pending = vec![Work::Visit(root)];
        while let Some(work) = pending.pop() {
            if let Work::Visit(_) = work {
                self.work.applicability_visits = self.work.applicability_visits.saturating_add(1);
            }
            let id = match work {
                Work::Visit(id)
                | Work::Prefix(id, _)
                | Work::EitherLeft(id, _, _)
                | Work::EitherRight(id, _) => id,
            };
            match work {
                Work::Visit(_) => {
                    if let Some(ApplicabilityFacts {
                        no_proven_guard_path: Some(certificate),
                        ..
                    }) = self.applicability_facts.get(&id)
                    {
                        local.insert(id, *certificate);
                        continue;
                    }
                    if let Some(_) = local.get(&id) {
                        continue;
                    }
                    match self.applicability[id] {
                        Applicability::Context(guards) => {
                            let certificate =
                                self.report_guard_sequence_blocks_proven_path(guards)?;
                            self.applicability_facts
                                .entry(id)
                                .or_default()
                                .no_proven_guard_path = Some(certificate);
                            local.insert(id, certificate);
                        }
                        Applicability::Prefix(guards, child) => {
                            match self.report_guard_sequence_blocks_proven_path(guards)? {
                                Some(()) => {
                                    self.applicability_facts
                                        .entry(id)
                                        .or_default()
                                        .no_proven_guard_path = Some(Some(()));
                                    local.insert(id, Some(()));
                                }
                                None => {
                                    pending.push(Work::Prefix(id, child));
                                    pending.push(Work::Visit(child));
                                }
                            }
                        }
                        Applicability::Either(left, right) => {
                            pending.push(Work::EitherLeft(id, left, right));
                            pending.push(Work::Visit(left));
                        }
                    }
                }
                Work::Prefix(_, child) => {
                    let certificate = local[&child];
                    self.applicability_facts
                        .entry(id)
                        .or_default()
                        .no_proven_guard_path = Some(certificate);
                    local.insert(id, certificate);
                }
                Work::EitherLeft(_, left, right) => match local[&left] {
                    Some(()) => {
                        pending.push(Work::EitherRight(id, right));
                        pending.push(Work::Visit(right));
                    }
                    None => {
                        self.applicability_facts
                            .entry(id)
                            .or_default()
                            .no_proven_guard_path = Some(None);
                        local.insert(id, None);
                    }
                },
                Work::EitherRight(_, right) => {
                    let certificate = local[&right];
                    self.applicability_facts
                        .entry(id)
                        .or_default()
                        .no_proven_guard_path = Some(certificate);
                    local.insert(id, certificate);
                }
            }
        }
        Ok(local[&root])
    }

    fn report_requirement_has_one_unproven_witness(
        &mut self,
        condition: ConditionId<'g>,
        applicability: ApplicabilityId<'g>,
    ) -> Step<Option<()>> {
        // context() caches structural dependence, so an empty probe result is unchanged under
        // every path prefix used to resolve this condition.
        let Some(()) = self.report_condition_context_probe(condition)? else {
            return Ok(None);
        };
        let condition = self.resolve_condition(condition, &Sequence::EMPTY)?;
        // Field relations can produce separate unencoded-precondition findings. Other local
        // unknown preconditions are suppressed, while exported ones need only one witness.
        match self.graph[condition] {
            ConditionNode::Compare(Order::Less | Order::LessEqual, left, right) => {
                if let (ExprNode::Field(..), ExprNode::Field(..)) =
                    (&self.graph[left], &self.graph[right])
                {
                    return Ok(None);
                }
            }
            ConditionNode::Unknown
            | ConditionNode::Compare(..)
            | ConditionNode::Boundary(..)
            | ConditionNode::NotBoundary(..)
            | ConditionNode::Variant(..)
            | ConditionNode::NotVariant(..)
            | ConditionNode::Returned(..) => {}
        }
        self.report_applicability_has_no_proven_guard_path(applicability)
    }

    fn report_condition_context_independent(
        &mut self,
        condition: ConditionId<'g>,
        applicability: ApplicabilityId<'g>,
    ) -> Step<Option<()>> {
        if let Some(()) = self.applicability_contains(applicability, condition)? {
            return Ok(None);
        }
        self.report_condition_context_probe(condition)
    }

    fn report_condition_guard_independent(&self, resolved: ConditionId<'g>) -> Option<()> {
        match self.graph[resolved] {
            ConditionNode::Compare(_, left, right) => {
                match (
                    self.report_expression_guard_dependence(left),
                    self.report_expression_guard_dependence(right),
                ) {
                    (GuardDependence::Independent, GuardDependence::Independent) => Some(()),
                    _ => None,
                }
            }
            ConditionNode::Variant(value, _) | ConditionNode::NotVariant(value, _) => {
                match self.report_expression_guard_dependence(value) {
                    GuardDependence::Independent => Some(()),
                    GuardDependence::Element | GuardDependence::Dependent => None,
                }
            }
            ConditionNode::Boundary(..)
            | ConditionNode::NotBoundary(..)
            | ConditionNode::Returned(..)
            | ConditionNode::Unknown => Some(()),
        }
    }

    fn report_condition_shape_certificate(&self, resolved: ConditionId<'g>) -> Option<()> {
        match self.graph.known(NodeId::Condition(resolved)) {
            None => self.report_condition_guard_independent(resolved),
            Some(()) => None,
        }
    }

    fn report_condition_certificate(
        &mut self,
        condition: ConditionId<'g>,
    ) -> Step<Option<ConditionId<'g>>> {
        if let ConditionNode::Unknown = self.graph[condition] {
            return Ok(Some(condition));
        }
        if let Some(ConditionFacts {
            certificate: Some(certificate),
            ..
        }) = self.report_condition_facts.get(&condition)
        {
            return Ok(*certificate);
        }
        let Some(()) = self.report_condition_context_probe(condition)? else {
            self.report_condition_facts
                .entry(condition)
                .or_default()
                .certificate = Some(None);
            return Ok(None);
        };
        let resolved = self.resolve_condition(condition, &Sequence::EMPTY)?;
        let certificate = self
            .report_condition_shape_certificate(resolved)
            .map(|_| resolved);
        self.report_condition_facts
            .entry(condition)
            .or_default()
            .certificate = Some(certificate);
        Ok(certificate)
    }

    fn report_outcome_certificate(
        &mut self,
        condition: ConditionId<'g>,
        applicability: ApplicabilityId<'g>,
    ) -> Step<Option<ConditionId<'g>>> {
        if let Some(certificate) = self
            .report_outcome_certificates
            .get(&(condition, applicability))
        {
            return Ok(*certificate);
        }
        if let Some(()) = self.applicability_contains(applicability, condition)? {
            self.report_outcome_certificates
                .insert((condition, applicability), None);
            return Ok(None);
        }
        let condition_support = self.report_condition_support(condition);
        if let ReportSupport::Known(_) = &condition_support {
            if let Some(context) = self.report_uniform_context(condition, applicability)? {
                if self.graph.conjunction(&context, &Sequence::EMPTY)? == Truth::Refuted {
                    self.report_outcome_certificates
                        .insert((condition, applicability), None);
                    return Ok(None);
                }
                let resolved = self.resolve_condition(condition, &context)?;
                match self.graph.truth(resolved, &context)? {
                    Truth::Unknown(_) => {
                        self.report_outcome_certificates
                            .insert((condition, applicability), Some(resolved));
                        return Ok(Some(resolved));
                    }
                    Truth::Proven | Truth::Refuted => {
                        self.report_outcome_certificates
                            .insert((condition, applicability), None);
                        return Ok(None);
                    }
                }
            }
        }
        let Some(()) = self.report_condition_context_independent(condition, applicability)? else {
            self.report_outcome_certificates
                .insert((condition, applicability), None);
            return Ok(None);
        };
        let condition_inputs = self
            .graph
            .input_summary(NodeId::Condition(condition), InputUse::Substitution)?;
        let applicability_inputs =
            self.applicability
                .inputs(self.graph, applicability, InputUse::Substitution)?;
        let input_independent = match (condition_inputs, applicability_inputs) {
            (Inputs::Known(condition), Inputs::Known(applicability)) => {
                self.graph.independent_arguments(condition, applicability)?
            }
            (Inputs::Unknown, _) | (_, Inputs::Unknown) => None,
        };
        let support_independent = match input_independent {
            Some(()) => Some(()),
            None => {
                let applicability_support = self.report_applicability_support(applicability);
                match (&condition_support, &applicability_support) {
                    (ReportSupport::Known(condition), ReportSupport::Known(guards)) => {
                        match self.report_support_trees_overlap(condition, guards) {
                            Some(()) => None,
                            None => Some(()),
                        }
                    }
                    (ReportSupport::Unknown, _) | (_, ReportSupport::Unknown) => None,
                }
            }
        };
        if let None = support_independent {
            self.report_outcome_certificates
                .insert((condition, applicability), None);
            return Ok(None);
        }
        let resolved = self.resolve_condition(condition, &Sequence::EMPTY)?;
        match self.graph.truth(resolved, &Sequence::EMPTY)? {
            Truth::Unknown(_) => {}
            Truth::Proven | Truth::Refuted => {
                self.report_outcome_certificates
                    .insert((condition, applicability), None);
                return Ok(None);
            }
        }
        self.report_outcome_certificates
            .insert((condition, applicability), Some(resolved));
        Ok(Some(resolved))
    }

    pub fn report_requirement(
        &mut self,
        cursor: &mut RequirementCursor<'g>,
        id: RequirementId<'g>,
        span: Span,
    ) -> Step<Option<ResolvedRequirement<'g>>> {
        self.work.reporting_visits = self.work.reporting_visits.saturating_add(1);
        let requirement = self.requirement_values[id.0 as usize].clone();
        let RequirementCore {
            invalidated,
            consumer,
            condition,
            applicability,
        } = requirement;
        let one_unproven_witness = if invalidated == Sequence::EMPTY {
            self.report_requirement_has_one_unproven_witness(condition, applicability)?
        } else {
            None
        };
        let sharing = if let Some(()) = one_unproven_witness {
            self.prune_applicability(applicability)?;
            None
        } else {
            let sharing = self.shared_requirement(
                &RequirementCore {
                    invalidated,
                    consumer,
                    condition,
                    applicability,
                },
                Sequence::EMPTY,
            )?;
            if let Some(shared) = &sharing {
                self.prune_applicability(shared.applicability)?;
            }
            sharing
        };
        let report_certificate = if let Some(()) = one_unproven_witness {
            None
        } else {
            let shape_certificate = if invalidated == Sequence::EMPTY {
                self.report_condition_certificate(condition)?
            } else {
                None
            };
            let outcome_certificate = if invalidated == Sequence::EMPTY
                && let None = shape_certificate
            {
                self.report_outcome_certificate(condition, applicability)?
            } else {
                None
            };
            match shape_certificate {
                Some(condition) => Some(condition),
                None => outcome_certificate,
            }
        };
        let exact_guard = if invalidated == Sequence::EMPTY
            && let None = one_unproven_witness
            && let None = report_certificate
        {
            self.applicability_contains(applicability, condition)?
        } else {
            None
        };
        let mut pending = vec![(applicability, Sequence::EMPTY)];
        let mut first = None;
        let mut extras = Vec::new();
        let mut merged_contexts = FxHashSet::default();
        let target_support = if invalidated == Sequence::EMPTY
            && let None = one_unproven_witness
            && let None = report_certificate
        {
            Some(self.report_condition_support(condition))
        } else {
            None
        };
        let mut path_statuses = FxHashSet::default();
        let prefix_prune_condition = if invalidated == Sequence::EMPTY
            && let Some(()) = self.report_condition_context_probe(condition)?
        {
            let resolved = self.resolve_condition(condition, &Sequence::EMPTY)?;
            self.report_condition_guard_independent(resolved)
                .map(|()| resolved)
        } else {
            None
        };
        while let Some((id, prefix)) = pending.pop() {
            self.work.applicability_visits = self.work.applicability_visits.saturating_add(1);
            let projected = if let Some(target_support) = &target_support {
                let remaining = self.report_applicability_support(id);
                self.report_project_prefix(condition, prefix, target_support, &remaining)?
            } else {
                prefix
            };
            let status = self.report_path_status(prefix)?;
            let key = ReportPathKey {
                applicability: id,
                prefix: projected,
                status,
            };
            if let Some(_) = path_statuses.get(&key) {
                continue;
            }
            path_statuses.insert(key);
            if let ReportPathStatus::Refuted = status {
                continue;
            }
            if let Some(ApplicabilityFacts {
                impossible: Some(Some(())),
                ..
            }) = self.applicability_facts.get(&id)
            {
                continue;
            }
            match self.applicability[id] {
                Applicability::Context(guards) => {
                    let guards = self.graph.append(prefix, guards)?;
                    let guards = self.resolve_guards(&guards)?;
                    if self.graph.conjunction(&guards, &Sequence::EMPTY)? == Truth::Refuted {
                        continue;
                    }
                    if invalidated == Sequence::EMPTY
                        && let None = exact_guard
                        && let Some(context) = self.report_path_merge_context(condition, guards)?
                        && !merged_contexts.insert(context)
                    {
                        continue;
                    }
                    let resolved = match report_certificate {
                        Some(condition) => condition,
                        None => self.resolve_condition(condition, &guards)?,
                    };
                    let outcome = self.graph.truth(resolved, &guards)?;
                    if outcome == Truth::Proven {
                        continue;
                    }
                    self.work.reporting_materializations =
                        self.work.reporting_materializations.saturating_add(1);
                    let candidate = Requirement {
                        invalidated,
                        consumer,
                        condition,
                        guards,
                        span,
                    };
                    let resolved = ResolvedRequirement {
                        requirement: candidate,
                        condition: resolved,
                        outcome,
                    };
                    if let Some(_) = report_certificate {
                        return Ok(Some(resolved));
                    }
                    if let Some(()) = one_unproven_witness {
                        return Ok(Some(resolved));
                    }
                    if let Some(shared) = &sharing
                        && let Sharing::Independent | Sharing::Stable = shared.sharing
                        && let None = &first
                    {
                        return Ok(Some(resolved));
                    }
                    match &first {
                        None => first = Some(resolved),
                        Some(_) => extras.push(resolved),
                    }
                }
                Applicability::Prefix(guards, child) => {
                    let guards = self.graph.append(prefix, guards)?;
                    let guards = self.resolve_guards(&guards)?;
                    if self.graph.conjunction(&guards, &Sequence::EMPTY)? == Truth::Refuted {
                        continue;
                    }
                    if let Some(condition) = prefix_prune_condition
                        && self.graph.truth(condition, &guards)? == Truth::Proven
                    {
                        continue;
                    }
                    pending.push((child, guards));
                }
                Applicability::Either(left, right) => {
                    pending.extend([(right, prefix), (left, prefix)])
                }
            }
        }
        extras.reverse();
        cursor
            .state
            .borrow_mut()
            .reports
            .extend(extras.into_iter().map(RequirementReport::Resolved));
        Ok(first)
    }

    fn requirement_input_summary(&mut self, id: RequirementId<'g>) -> Step<Inputs<'g>> {
        if let Some(inputs) = self.requirement_inputs.get(&id) {
            return Ok(*inputs);
        }
        let requirement = self.requirement_values[id.0 as usize].clone();
        let condition = self.graph.input_summary(
            NodeId::Condition(requirement.condition),
            InputUse::Substitution,
        )?;
        let inputs = match condition {
            Inputs::Unknown => Inputs::Unknown,
            Inputs::Known(_) => {
                let applicability = self.applicability.inputs(
                    self.graph,
                    requirement.applicability,
                    InputUse::Substitution,
                )?;
                match self.graph.combine_inputs(condition, applicability)? {
                    Inputs::Unknown => Inputs::Unknown,
                    inputs @ Inputs::Known(_) => {
                        let invalidated = self.graph.sequence_input_summary(
                            crate::contracts::operations::InputSequence::Invalidated(
                                requirement.invalidated,
                            ),
                            InputUse::Substitution,
                        )?;
                        self.graph.combine_inputs(inputs, invalidated)?
                    }
                }
            }
        };
        self.requirement_inputs.insert(id, inputs);
        Ok(inputs)
    }

    fn plan_input_summary(
        &mut self,
        root: Sequence<'g, RequirementPlanId<'g>>,
    ) -> Step<Inputs<'g>> {
        enum Work<'g> {
            Sequence(Sequence<'g, RequirementPlanId<'g>>),
            Leaf(Sequence<'g, RequirementPlanId<'g>>, RequirementPlanId<'g>),
            Left(
                Sequence<'g, RequirementPlanId<'g>>,
                Sequence<'g, RequirementPlanId<'g>>,
                Sequence<'g, RequirementPlanId<'g>>,
            ),
            Right(
                Sequence<'g, RequirementPlanId<'g>>,
                Inputs<'g>,
                Sequence<'g, RequirementPlanId<'g>>,
            ),
            Plan(RequirementPlanId<'g>),
            Transform(
                RequirementPlanId<'g>,
                Sequence<'g, RequirementPlanId<'g>>,
                ArgumentContextId<'g>,
                Inputs<'g>,
            ),
        }
        if let Some(PlanSequenceFacts {
            inputs: Some(inputs),
            ..
        }) = self.plan_sequence_facts.get(&root)
        {
            return Ok(*inputs);
        }
        let mut pending = vec![Work::Sequence(root)];
        while let Some(work) = pending.pop() {
            self.work.plan_input_visits = self.work.plan_input_visits.saturating_add(1);
            match work {
                Work::Sequence(sequence) => {
                    if let Some(PlanSequenceFacts {
                        inputs: Some(_),
                        ..
                    }) = self.plan_sequence_facts.get(&sequence)
                    {
                        continue;
                    }
                    match self.requirement_sequences.parts(sequence)? {
                        crate::sequence::Parts::Empty => {
                            self.plan_sequence_facts
                                .entry(sequence)
                                .or_default()
                                .inputs = Some(Inputs::Known(SetId::EMPTY));
                        }
                        crate::sequence::Parts::Leaf(plan) => {
                            pending.push(Work::Leaf(sequence, plan));
                            pending.push(Work::Plan(plan));
                        }
                        crate::sequence::Parts::Branch(left, right) => {
                            pending.push(Work::Left(sequence, left, right));
                            pending.push(Work::Sequence(left));
                        }
                    }
                }
                Work::Leaf(sequence, plan) => {
                    let inputs = self.plan_facts[&plan].inputs;
                    self.plan_sequence_facts
                        .entry(sequence)
                        .or_default()
                        .inputs = Some(inputs.expect("leaf plan inputs are built"));
                }
                Work::Left(sequence, left, right) => match self.plan_sequence_facts[&left]
                    .inputs
                    .expect("left plan sequence inputs are built")
                {
                    Inputs::Unknown => {
                        self.plan_sequence_facts
                            .entry(sequence)
                            .or_default()
                            .inputs = Some(Inputs::Unknown);
                    }
                    inputs @ Inputs::Known(_) => {
                        pending.push(Work::Right(sequence, inputs, right));
                        pending.push(Work::Sequence(right));
                    }
                },
                Work::Right(sequence, left, right) => {
                    let right = self.plan_sequence_facts[&right]
                        .inputs
                        .expect("right plan sequence inputs are built");
                    let inputs = self.graph.combine_inputs(left, right)?;
                    self.plan_sequence_facts
                        .entry(sequence)
                        .or_default()
                        .inputs = Some(inputs);
                }
                Work::Plan(plan) => {
                    if let Some(PlanFacts {
                        inputs: Some(_),
                        ..
                    }) = self.plan_facts.get(&plan)
                    {
                        continue;
                    }
                    match self.requirement_plans[plan.0 as usize] {
                        RequirementPlan::Leaf(id) => {
                            let inputs = self.requirement_input_summary(id)?;
                            self.plan_facts.entry(plan).or_default().inputs = Some(inputs);
                        }
                        RequirementPlan::Transform(sequence, arguments, guards) => {
                            match self.graph.sequence_input_summary(
                                crate::contracts::operations::InputSequence::Conditions(guards.0),
                                InputUse::Substitution,
                            )? {
                                Inputs::Unknown => {
                                    self.plan_facts.entry(plan).or_default().inputs =
                                        Some(Inputs::Unknown);
                                }
                                inputs @ Inputs::Known(_) => {
                                    pending
                                        .push(Work::Transform(plan, sequence, arguments, inputs));
                                    pending.push(Work::Sequence(sequence));
                                }
                            }
                        }
                    }
                }
                Work::Transform(plan, sequence, arguments, guards) => {
                    let inputs = match self.plan_sequence_facts[&sequence]
                        .inputs
                        .expect("transformed plan sequence inputs are built")
                    {
                        Inputs::Unknown => Inputs::Unknown,
                        Inputs::Known(positions) => {
                            let positions = self.graph.members(positions).collect::<Vec<_>>();
                            let mut inputs = guards;
                            for index in positions {
                                self.work.plan_input_positions =
                                    self.work.plan_input_positions.saturating_add(1);
                                let input = match crate::sequence::Sequences::get(
                                    self.graph.as_ref(),
                                    arguments.0,
                                    index,
                                )
                                .copied()
                                {
                                    Some(value) => self.graph.input_summary(
                                        NodeId::Expr(value),
                                        InputUse::Substitution,
                                    )?,
                                    None => Inputs::Unknown,
                                };
                                inputs = self.graph.combine_inputs(inputs, input)?;
                                if let Inputs::Unknown = inputs {
                                    break;
                                }
                            }
                            inputs
                        }
                    };
                    self.plan_facts.entry(plan).or_default().inputs = Some(inputs);
                }
            }
        }
        Ok(self.plan_sequence_facts[&root]
            .inputs
            .expect("root plan sequence inputs are built"))
    }

    fn cache_slot(&mut self, query: &Query<'g>) -> Step<CacheSlot<'g>> {
        Ok(match query {
            Query::Expression(value, guards) => CacheSlot::Expression(*value, *guards),
            Query::Condition(value, guards) => CacheSlot::Condition(*value, *guards),
            Query::Guards(guards) => CacheSlot::Guards(*guards),
            Query::TransformRequirements(id, arguments, guards) => {
                let inputs = self.requirement_input_summary(*id)?;
                CacheSlot::Transform(
                    *id,
                    self.graph.project_arguments(inputs, *arguments)?,
                    *guards,
                )
            }
            Query::RequirementPlans(sequence, operation) => {
                let operation = match operation {
                    RequirementOperation::Resolve => RequirementPlanOperation::Resolve,
                    RequirementOperation::LocalFindings => RequirementPlanOperation::LocalFindings,
                    RequirementOperation::Transform(arguments, guards) => {
                        let inputs = self.plan_input_summary(*sequence)?;
                        RequirementPlanOperation::Transform(
                            self.graph.project_arguments(inputs, *arguments)?,
                            *guards,
                        )
                    }
                };
                CacheSlot::Plans(*sequence, operation)
            }
            Query::Reduced(..)
            | Query::ChoiceTargets(..)
            | Query::ChoiceCompletes(..)
            | Query::Targets(..)
            | Query::Returned(..)
            | Query::ReturnGuards(..)
            | Query::Completes(..)
            | Query::Requirements(..)
            | Query::Materialized(..)
            | Query::Contextual(..) => CacheSlot::Other,
        })
    }

    fn substitute_requirement(
        &mut self,
        requirement: &RequirementCore<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
        invocation: &Invocation<'g>,
    ) -> Result<RequirementCore<'g>, CapacityError> {
        let substituted = RequirementCore {
            invalidated: self.graph.substitute_invalidated(
                &requirement.invalidated,
                arguments,
                invocation,
            )?,
            consumer: requirement.consumer.clone(),
            condition: self.graph.substitute_condition(
                requirement.condition,
                arguments,
                invocation,
            )?,
            applicability: self.applicability.substitute(
                self.graph,
                requirement.applicability,
                *arguments,
                *invocation,
            )?,
        };
        Ok(substituted)
    }

    pub fn resolve_expression(
        &mut self,
        expression: ExprId<'g>,
        guards: &Sequence<'g, ConditionId<'g>>,
    ) -> Result<ExprId<'g>, CapacityError> {
        let guards = GuardContextId::from(*guards);
        let context = self.context(NodeId::Expr(expression), guards)?;
        let Answer::Expression(result) =
            schedule::evaluate(self, Query::Expression(expression, context))?.value
        else {
            unreachable!("expression query result")
        };
        Ok(result)
    }
    pub fn resolve_condition(
        &mut self,
        condition: ConditionId<'g>,
        guards: &Sequence<'g, ConditionId<'g>>,
    ) -> Result<ConditionId<'g>, CapacityError> {
        let guards = GuardContextId::from(*guards);
        let context = self.context(NodeId::Condition(condition), guards)?;
        let Answer::Condition(result) =
            schedule::evaluate(self, Query::Condition(condition, context))?.value
        else {
            unreachable!("condition query result")
        };
        Ok(result)
    }
    pub fn resolve_guards(
        &mut self,
        guards: &Sequence<'g, ConditionId<'g>>,
    ) -> Result<Sequence<'g, ConditionId<'g>>, CapacityError> {
        let context = GuardContextId::from(*guards);
        let Answer::Guards(result) = schedule::evaluate(self, Query::Guards(context))?.value else {
            unreachable!("guard query result")
        };
        Ok(self.guard_prefixes[result.0 as usize].unique.0)
    }
    fn requirement_consumer(
        &mut self,
        consumer: crate::contracts::summaries::ConsumerId<'g>,
    ) -> Option<Span> {
        match self.requirement_consumers.get(&consumer) {
            Some(span) => *span,
            None => {
                let consumer_node = self.graph[consumer];
                let span = crate::diagnostics::source_span(
                    self.tcx,
                    consumer_node.def,
                    consumer_node.span,
                );
                self.requirement_consumers.insert(consumer, span);
                span
            }
        }
    }

    fn intern_requirement_plan(
        &mut self,
        plan: RequirementPlan<'g>,
    ) -> Step<RequirementPlanId<'g>> {
        let index = match self.requirement_plans.get_index_of(&plan) {
            Some(index) => index,
            None => {
                u32::try_from(self.requirement_plans.len()).map_err(|_| CapacityError::Sets)?;
                self.requirement_plans.insert_full(plan).0
            }
        };
        Ok(RequirementPlanId(index as u32, std::marker::PhantomData))
    }

    fn requirement_plan_obligation(
        &mut self,
        id: RequirementPlanId<'g>,
    ) -> Option<(Obligation<'g>, RequirementId<'g>)> {
        if let Some(PlanFacts {
            obligation: Some(obligation),
            ..
        }) = self.plan_facts.get(&id)
        {
            return *obligation;
        }
        let obligation = match self.requirement_plans[id.0 as usize] {
            RequirementPlan::Leaf(id) => {
                let requirement = &self.requirement_values[id.0 as usize];
                if requirement.invalidated == Sequence::EMPTY {
                    Some((
                        Obligation {
                            invalidated: requirement.invalidated,
                            consumer: requirement.consumer,
                            condition: requirement.condition,
                        },
                        id,
                    ))
                } else {
                    None
                }
            }
            RequirementPlan::Transform(..) => None,
        };
        self.plan_facts.entry(id).or_default().obligation = Some(obligation);
        obligation
    }

    fn insert_requirement_id(
        &mut self,
        group: &mut RequirementGroup<'g>,
        id: RequirementPlanId<'g>,
    ) -> Result<(), CapacityError> {
        if let None = self.requirement_sets.contains(group.members, id) {
            group.members = self.requirement_sets.insert(group.members, id)?;
            group.ordered = self.requirement_sequences.push(group.ordered, id)?;
            if let Some((obligation, _)) = self.requirement_plan_obligation(id) {
                group.obligations = self.obligation_sets.insert(group.obligations, obligation)?;
            }
        }
        Ok(())
    }

    fn insert_requirement(
        &mut self,
        requirements: &mut Requirements<'g>,
        requirement: Requirement<'g>,
    ) -> Result<(), CapacityError> {
        if let None = self.requirement_consumer(requirement.consumer) {
            return Ok(());
        }
        let span = requirement.span;
        let requirement = self.requirement_core(requirement)?;
        let id = self.intern_requirement_core(requirement)?;
        let id = self.intern_requirement_plan(RequirementPlan::Leaf(id))?;
        let mut group = RequirementGroup::EMPTY;
        self.insert_requirement_id(&mut group, id)?;
        self.append_requirement_group(requirements, span, group)
    }

    fn filter_requirement_group(
        &mut self,
        group: RequirementGroup<'g>,
        previous: SetId<'g, RequirementPlanId<'g>>,
    ) -> Result<RequirementGroup<'g>, CapacityError> {
        enum Work<'g> {
            Visit(Sequence<'g, RequirementPlanId<'g>>),
            Join(
                Sequence<'g, RequirementPlanId<'g>>,
                Sequence<'g, RequirementPlanId<'g>>,
                Sequence<'g, RequirementPlanId<'g>>,
            ),
        }
        let mut pending = vec![Work::Visit(group.ordered)];
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(sequence) => {
                    if let Some(_) = self.requirement_filters.get(&(sequence, previous)) {
                        continue;
                    }
                    match self.requirement_sequences.parts(sequence)? {
                        crate::sequence::Parts::Empty => {
                            let filtered = RequirementGroup::EMPTY;
                            self.requirement_filters
                                .insert((sequence, previous), filtered);
                        }
                        crate::sequence::Parts::Leaf(id) => {
                            let mut filtered = RequirementGroup::EMPTY;
                            if let None = self.requirement_sets.contains(previous, id) {
                                self.insert_requirement_id(&mut filtered, id)?;
                            }
                            self.requirement_filters
                                .insert((sequence, previous), filtered);
                        }
                        crate::sequence::Parts::Branch(left, right) => {
                            pending.push(Work::Join(sequence, left, right));
                            pending.push(Work::Visit(right));
                            pending.push(Work::Visit(left));
                        }
                    }
                }
                Work::Join(sequence, left, right) => {
                    let left = self.requirement_filters[&(left, previous)];
                    let right = self.requirement_filters[&(right, previous)];
                    let filtered = self.join_requirement_groups(left, right)?;
                    self.requirement_filters
                        .insert((sequence, previous), filtered);
                }
            }
        }
        Ok(self.requirement_filters[&(group.ordered, previous)])
    }

    fn factor_requirement_group(
        &mut self,
        group: RequirementGroup<'g>,
    ) -> Step<RequirementGroup<'g>> {
        if let Some(PlanSequenceFacts {
            factors: Some(result),
            ..
        }) = self.plan_sequence_facts.get(&group.ordered)
        {
            return Ok(*result);
        }
        let plans = self
            .requirement_sequences
            .iter(group.ordered)
            .copied()
            .collect::<Vec<_>>();
        let mut distinct = Vec::new();
        let mut shared = FxIndexMap::default();
        let plans = plans.into_iter().enumerate();
        for (position, plan) in plans {
            self.work.requirement_join_visits = self.work.requirement_join_visits.saturating_add(1);
            let Some((obligation, id)) = self.requirement_plan_obligation(plan) else {
                distinct.push((position, plan));
                continue;
            };
            let requirement = self.requirement_values[id.0 as usize].clone();
            match shared.get_mut(&obligation) {
                Some((_, plan, previous)) => {
                    let applicability = self
                        .applicability
                        .intern(Applicability::Either(*previous, requirement.applicability))?;
                    let id = self.intern_requirement_core(RequirementCore {
                        applicability,
                        ..requirement
                    })?;
                    *plan = self.intern_requirement_plan(RequirementPlan::Leaf(id))?;
                    *previous = applicability;
                }
                None => {
                    shared.insert(obligation, (position, plan, requirement.applicability));
                }
            }
        }
        let mut result = RequirementGroup::EMPTY;
        let mut shared = shared.into_values().peekable();
        for (position, plan) in distinct {
            while let Some((_, prior, _)) = shared.next_if(|(prior, _, _)| *prior < position) {
                self.insert_requirement_id(&mut result, prior)?;
            }
            self.insert_requirement_id(&mut result, plan)?;
        }
        for (_, plan, _) in shared {
            self.insert_requirement_id(&mut result, plan)?;
        }
        self.plan_sequence_facts
            .entry(group.ordered)
            .or_default()
            .factors = Some(result);
        Ok(result)
    }

    fn join_requirement_groups(
        &mut self,
        mut left: RequirementGroup<'g>,
        mut right: RequirementGroup<'g>,
    ) -> Result<RequirementGroup<'g>, CapacityError> {
        if left.members == SetId::EMPTY {
            return Ok(right);
        }
        if right.members == SetId::EMPTY {
            return Ok(left);
        }
        let obligation_overlap = self.obligation_sets.combine(
            Combination::Intersection,
            left.obligations,
            right.obligations,
        )?;
        let overlap = self.requirement_sets.combine(
            Combination::Intersection,
            left.members,
            right.members,
        )?;
        if overlap != SetId::EMPTY {
            right = self.filter_requirement_group(right, left.members)?;
        }
        if right.members != SetId::EMPTY {
            left.ordered = self
                .requirement_sequences
                .append(left.ordered, right.ordered)?;
            left.members =
                self.requirement_sets
                    .combine(Combination::Union, left.members, right.members)?;
        }
        left.obligations = self.obligation_sets.combine(
            Combination::Union,
            left.obligations,
            right.obligations,
        )?;
        if obligation_overlap == SetId::EMPTY {
            Ok(left)
        } else {
            self.factor_requirement_group(left)
        }
    }

    fn append_requirement_group(
        &mut self,
        requirements: &mut Requirements<'g>,
        span: Span,
        mut group: RequirementGroup<'g>,
    ) -> Result<(), CapacityError> {
        let previous = requirements
            .members
            .get(&span)
            .copied()
            .unwrap_or(SetId::EMPTY);
        let overlap =
            self.requirement_sets
                .combine(Combination::Intersection, previous, group.members)?;
        if overlap != SetId::EMPTY {
            group = self.filter_requirement_group(group, previous)?;
        }
        if group.members == SetId::EMPTY {
            return Ok(());
        }
        let members = self
            .requirement_sets
            .combine(Combination::Union, previous, group.members)?;
        requirements.members.insert(span, members);
        if let Some(last) = requirements.groups.last_mut()
            && last.span == span
        {
            last.requirements = self.join_requirement_groups(last.requirements, group)?;
        } else {
            requirements.groups.push(ReportGroup {
                span,
                requirements: group,
            });
        }
        Ok(())
    }

    pub fn resolve_requirements(
        &mut self,
        def: DefId,
        demand: ReportDemand,
    ) -> Result<Vec<(Span, RequirementCursor<'g>)>, CapacityError> {
        if let None = self.requirement_candidates.get(&def) {
            return Ok(Vec::new());
        }
        let parameters = self.symbolic_arguments(def)?;
        let callable = self.graph.intern_value(InstanceNode {
            def,
            args: crate::values::GenericsId::EMPTY,
            dispatch: Dispatch::Item,
        })?;
        let parameters = ArgumentContextId::from(parameters);
        let Answer::Requirements(requirements) =
            schedule::evaluate(self, Query::Requirements(callable, parameters))?.value
        else {
            unreachable!("requirement query result")
        };
        let mut states = FxHashMap::default();
        let mut groups = Vec::new();
        let mut input = crate::sequence::Cursor::from((&self.requirement_groups, requirements.0));
        while let Some(group) = input.next(&self.requirement_groups).copied() {
            let Answer::ResolvedRequirements(requirements) = schedule::evaluate(
                self,
                Query::RequirementPlans(
                    group.requirements.ordered,
                    match demand {
                        ReportDemand::ExportedContract => RequirementOperation::Resolve,
                        ReportDemand::LocalFindings => RequirementOperation::LocalFindings,
                    },
                ),
            )?
            .value
            else {
                unreachable!("requirement plan query result")
            };
            if requirements.0.members == SetId::EMPTY {
                continue;
            }
            let state = std::rc::Rc::clone(states.entry(group.span).or_insert_with(|| {
                std::rc::Rc::new(std::cell::RefCell::new(RequirementCursorState {
                    applied: FxHashSet::default(),
                    reports: Vec::new(),
                }))
            }));
            let cursor = RequirementCursor::new(requirements, state);
            groups.push((group.span, cursor));
        }
        Ok(groups)
    }
    pub fn next_requirement(
        &mut self,
        cursor: &mut RequirementCursor<'g>,
    ) -> Step<Option<RequirementReport<'g>>> {
        loop {
            let report = cursor.state.borrow_mut().reports.pop();
            let Some(report) = report else {
                break;
            };
            self.work.requirement_visits = self.work.requirement_visits.saturating_add(1);
            match report {
                RequirementReport::Resolved(requirement) => {
                    return Ok(Some(RequirementReport::Resolved(requirement)));
                }
                RequirementReport::Pending(id) if cursor.state.borrow_mut().applied.insert(id) => {
                    return Ok(Some(RequirementReport::Pending(id)));
                }
                RequirementReport::Pending(_) => {}
            }
        }
        while let Some(sequence) = cursor.pending.pop() {
            self.work.requirement_visits = self.work.requirement_visits.saturating_add(1);
            if !cursor.visited.insert(sequence) {
                continue;
            }
            match self.requirement_sequences.parts(sequence)? {
                crate::sequence::Parts::Empty => {}
                crate::sequence::Parts::Branch(left, right) => {
                    cursor.pending.push(right);
                    cursor.pending.push(left);
                }
                crate::sequence::Parts::Leaf(id) => {
                    let RequirementPlan::Leaf(id) = self.requirement_plans[id.0 as usize] else {
                        unreachable!("resolved requirements contain only leaves")
                    };
                    if cursor.state.borrow_mut().applied.insert(id) {
                        return Ok(Some(RequirementReport::Pending(id)));
                    }
                }
            }
        }
        Ok(None)
    }
}

struct Evaluation<'s, 'a, 'tcx, 'g> {
    session: Session<'s, Evaluator<'a, 'tcx, 'g>>,
}

impl<'a, 'tcx, 'g> Evaluation<'_, 'a, 'tcx, 'g> {
    async fn expression(&self, value: ExprId<'g>, guards: GuardContextId<'g>) -> Step<ExprId<'g>> {
        let Answer::Expression(value) = self
            .session
            .query(Query::Expression(
                value,
                self.session
                    .with(|engine| engine.context(NodeId::Expr(value), guards))?,
            ))
            .await?
            .value
        else {
            unreachable!("expression query result")
        };
        Ok(value)
    }
    async fn condition(
        &self,
        value: ConditionId<'g>,
        guards: GuardContextId<'g>,
    ) -> Step<ConditionId<'g>> {
        let Answer::Condition(value) = self
            .session
            .query(Query::Condition(
                value,
                self.session
                    .with(|engine| engine.context(NodeId::Condition(value), guards))?,
            ))
            .await?
            .value
        else {
            unreachable!("condition query result")
        };
        Ok(value)
    }
    async fn guards(&self, guards: &Sequence<'g, ConditionId<'g>>) -> Step<GuardContextId<'g>> {
        let Answer::Guards(value) = self
            .session
            .query(Query::Guards(GuardContextId::from(*guards)))
            .await?
            .value
        else {
            unreachable!("guards query result")
        };
        Ok(self
            .session
            .with(|engine| engine.guard_prefixes[value.0 as usize].unique))
    }
    async fn targets(
        &self,
        target: TargetNode<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
        guards: GuardContextId<'g>,
    ) -> Step<Option<Sequence<'g, (InstanceId<'g>, Sequence<'g, ExprId<'g>>)>>> {
        let Answer::Targets(value) = self
            .session
            .query(Query::Targets(
                target,
                ArgumentContextId::from(*arguments),
                guards,
            ))
            .await?
            .value
        else {
            unreachable!("targets query result")
        };
        Ok(value)
    }
    async fn returned(
        &self,
        callable: InstanceId<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
        origin: Option<&OriginId<'g>>,
        guards: GuardContextId<'g>,
    ) -> Step<ExprId<'g>> {
        let origin = match self.session.with(|engine| {
            engine
                .definition_activity
                .get(&engine.graph[callable].def)
                .and_then(|activity| activity.active)
        }) {
            Some(_) => None,
            None => origin.cloned(),
        };
        let Answer::Expression(value) = self
            .session
            .query(Query::Returned(
                callable,
                ArgumentContextId::from(*arguments),
                origin,
                guards,
            ))
            .await?
            .value
        else {
            unreachable!("return query result")
        };
        Ok(value)
    }

    async fn step(&self, query: &Query<'g>) -> Step<Answer<'g>> {
        match query {
            Query::Reduced(values, guards) => {
                let result = match self
                    .session
                    .with(|engine| engine.graph.argument_prefix(*values))?
                {
                    None => None,
                    Some((prefix, value)) => {
                        let Answer::Reduced(previous) = self
                            .session
                            .query(Query::Reduced(prefix, *guards))
                            .await?
                            .value
                        else {
                            unreachable!("ordered reduction query result");
                        };
                        let value = self.expression(value, *guards).await?;
                        Some(match previous {
                            Some(previous) => self
                                .session
                                .with(|engine| engine.graph.join(previous, value, Join::Hull))?,
                            None => value,
                        })
                    }
                };
                Ok(Answer::Reduced(result))
            }
            Query::ChoiceTargets(root, target, arguments, guards) => self
                .step_choice_targets(*root, *target, *arguments, *guards)
                .await
                .map(Answer::Targets),
            Query::ChoiceCompletes(root, guards) => {
                let result = match self.session.with(|engine| engine.graph[*root].node) {
                    ChoiceNode::Value(value) => self.completes(value, *guards).await?,
                    ChoiceNode::Branch(left, right) => {
                        let Answer::Completes(left) = self
                            .session
                            .query(Query::ChoiceCompletes(left, *guards))
                            .await?
                            .value
                        else {
                            unreachable!("choice completion query result");
                        };
                        match left {
                            Completion::Possible => Completion::Possible,
                            Completion::Never => {
                                let Answer::Completes(right) = self
                                    .session
                                    .query(Query::ChoiceCompletes(right, *guards))
                                    .await?
                                    .value
                                else {
                                    unreachable!("choice completion query result");
                                };
                                right
                            }
                        }
                    }
                };
                Ok(Answer::Completes(result))
            }
            Query::Expression(value, guards) => self
                .step_expression(*value, *guards)
                .await
                .map(Answer::Expression),
            Query::Condition(value, guards) => self
                .step_condition(*value, *guards)
                .await
                .map(Answer::Condition),
            Query::Guards(guards) => self.step_guards(*guards).await.map(Answer::Guards),
            Query::Targets(target, arguments, guards) => self
                .step_targets(target, &arguments.0, *guards)
                .await
                .map(Answer::Targets),
            Query::Returned(callable, arguments, origin, guards) => self
                .step_returned(*callable, &arguments.0, origin.as_ref(), *guards)
                .await
                .map(Answer::Expression),
            Query::ReturnGuards(callable, arguments) => {
                let guards = self.step_return_guards(*callable, &arguments.0).await?;
                self.session.with(|engine| {
                    Ok(Answer::ReturnGuards(ReturnGuardsId(
                        engine.return_guards.from_iter(guards)?,
                    )))
                })
            }
            Query::Completes(value, guards) => self
                .step_completes(*value, *guards)
                .await
                .map(Answer::Completes),
            Query::Requirements(callable, arguments) => {
                let requirements = self.step_requirements(*callable, &arguments.0).await?;
                self.session.with(|engine| {
                    Ok(Answer::Requirements(RequirementsId(
                        engine.requirement_groups.from_iter(requirements.groups)?,
                    )))
                })
            }
            Query::TransformRequirements(requirements, arguments, guards) => self
                .step_transform_requirements(*requirements, *arguments, *guards)
                .await
                .map(Answer::ResolvedRequirements),
            Query::RequirementPlans(sequence, operation) => self
                .step_requirement_plans(*sequence, *operation)
                .await
                .map(Answer::ResolvedRequirements),
            Query::Materialized(target, arguments, guards, basis, span) => {
                let call = CallNode {
                    basis: match basis {
                        CheckBasis::Expression => CheckBasis::Expression,
                        CheckBasis::ControlFlow(basis) => CheckBasis::ControlFlow(basis.0),
                    },
                    target: target.clone(),
                    arguments: arguments.0,
                    guards: guards.0,
                    span: *span,
                };
                self.step_materialized(&call).await.map(Answer::Calls)
            }
            Query::Contextual(callable, arguments) => self
                .step_contextual(*callable, &arguments.0)
                .await
                .map(Answer::Calls),
        }
    }

    async fn step_expression(
        &self,
        expression: ExprId<'g>,
        guards: GuardContextId<'g>,
    ) -> Step<ExprId<'g>> {
        let node = match self.session.with(|engine| engine.graph[expression].clone()) {
            ExprNode::Select(condition, yes, no) => {
                let condition = self.condition(condition, guards).await?;
                return match self
                    .session
                    .with(|engine| engine.truth(condition, guards))?
                {
                    Truth::Proven => self.expression(yes, guards).await,
                    Truth::Refuted => self.expression(no, guards).await,
                    Truth::Unknown(_) => {
                        let yes = self.expression(yes, guards).await?;
                        let no = self.expression(no, guards).await?;
                        Ok(self.session.with(|engine| {
                            engine
                                .graph
                                .intern_expr(ExprNode::Select(condition, yes, no))
                        })?)
                    }
                };
            }
            ExprNode::Function(instance) => ExprNode::Function(
                self.session
                    .with(|engine| engine.captures.resolve_instance(instance))?,
            ),
            ExprNode::Typed(ty, value) => {
                let value = self.expression(value, guards).await?;
                return Ok(self.session.with(|engine| engine.graph.typed(ty, value))?);
            }
            ExprNode::Alternatives(root) => {
                let Some(root) = root else {
                    return Ok(self
                        .session
                        .with(|engine| engine.graph.intern_expr(ExprNode::Unknown))?);
                };
                let query = self.session.with(|engine| {
                    let values = engine.graph[root].values.clone();
                    Ok::<_, CapacityError>(Query::Reduced(ArgumentContextId::from(values), guards))
                })?;
                let Answer::Reduced(result) = self.session.query(query).await?.value else {
                    unreachable!("ordered reduction query result");
                };
                return Ok(match result {
                    Some(value) => value,
                    None => self
                        .session
                        .with(|engine| engine.graph.intern_expr(ExprNode::Unknown))?,
                });
            }
            ExprNode::Global(instance) => {
                let empty = crate::sequence::Sequence::EMPTY;
                return self.returned(instance, &empty, None, guards).await;
            }
            ExprNode::Call(target, arguments, origin) => {
                let fallback = self.session.with(|engine| {
                    engine.graph.intern_expr(match &origin {
                        Some(origin) => ExprNode::Opaque(*origin),
                        None => ExprNode::Unknown,
                    })
                })?;
                if let TargetNode::Direct(callable) = target
                    && let Dispatch::Item =
                        self.session.with(|engine| engine.graph[callable]).dispatch
                    && !self
                        .session
                        .with(|engine| engine.bodies.contains_key(&engine.graph[callable].def))
                {
                    return Ok(fallback);
                }
                let mut resolved = Vec::new();
                let mut inputs = self.session.with(|engine| engine.graph.scan(arguments));
                while let Some(argument) = inputs.next() {
                    resolved.push(self.expression(argument, guards).await?);
                }
                let arguments = self.session.with(|engine| {
                    crate::sequence::Sequences::from_iter(engine.graph.as_mut(), resolved)
                })?;
                let Some(targets) = self.targets(target, &arguments, guards).await? else {
                    return Ok(fallback);
                };
                let mut result = None;
                let mut targets = self
                    .session
                    .with(|engine| crate::sequence::Cursor::from((&engine.target_lists, targets)));
                while let Some((instance, arguments)) = self
                    .session
                    .with(|engine| targets.next(&engine.target_lists).copied())
                {
                    let value = self
                        .returned(instance, &arguments, origin.as_ref(), guards)
                        .await?;
                    result = Some(match result {
                        Some(previous) => self
                            .session
                            .with(|engine| engine.graph.join(previous, value, Join::Hull))?,
                        None => value,
                    });
                }
                return Ok(match result {
                    Some(value) => value,
                    None => fallback,
                });
            }
            ExprNode::Field(base, index) => {
                let base = self.expression(base, guards).await?;
                return Ok(self
                    .session
                    .with(|engine| engine.graph.field(base, index))?);
            }
            ExprNode::Element(base, index) => {
                let base = self.expression(base, guards).await?;
                let index = self.expression(index, guards).await?;
                if let (ExprNode::Aggregate(fields), ExprNode::Number(index)) = (
                    &self.session.with(|engine| engine.graph[base].clone()),
                    &self.session.with(|engine| engine.graph[index].clone()),
                ) {
                    let value = self.session.with(|engine| {
                        let arena: &crate::sequence::Sequences<'_, ExprId<'_>> =
                            engine.graph.as_ref();
                        if *index < arena.len(*fields) as u128 {
                            arena.get(*fields, *index as usize).copied()
                        } else {
                            None
                        }
                    });
                    return Ok(match value {
                        Some(value) => value,
                        None => self
                            .session
                            .with(|engine| engine.graph.intern_expr(ExprNode::Unknown))?,
                    });
                }
                ExprNode::Element(base, index)
            }
            ExprNode::Closure(def, values) => {
                let mut resolved = Vec::new();
                let mut inputs = self.session.with(|engine| engine.graph.scan(values));
                while let Some(value) = inputs.next() {
                    resolved.push(self.expression(value, guards).await?);
                }
                let resolved = self.session.with(|engine| {
                    crate::sequence::Sequences::from_iter(engine.graph.as_mut(), resolved)
                })?;
                ExprNode::Closure(def, resolved)
            }
            ExprNode::Aggregate(values) => {
                let mut resolved = Vec::new();
                let mut inputs = self.session.with(|engine| engine.graph.scan(values));
                while let Some(value) = inputs.next() {
                    resolved.push(self.expression(value, guards).await?);
                }
                let resolved = self.session.with(|engine| {
                    crate::sequence::Sequences::from_iter(engine.graph.as_mut(), resolved)
                })?;
                ExprNode::Aggregate(resolved)
            }
            ExprNode::Variant(def, variant, values) => {
                let mut resolved = Vec::new();
                let mut inputs = self.session.with(|engine| engine.graph.scan(values));
                while let Some(value) = inputs.next() {
                    resolved.push(self.expression(value, guards).await?);
                }
                let resolved = self.session.with(|engine| {
                    crate::sequence::Sequences::from_iter(engine.graph.as_mut(), resolved)
                })?;
                ExprNode::Variant(def, variant, resolved)
            }
            ExprNode::Arithmetic(op, left, right) => {
                let left = self.expression(left, guards).await?;
                let right = self.expression(right, guards).await?;
                match (
                    op,
                    &self.session.with(|engine| engine.graph[left].clone()),
                    &self.session.with(|engine| engine.graph[right].clone()),
                ) {
                    (Arithmetic::Subtract(_), ExprNode::Number(left), ExprNode::Number(right))
                        if let Some(difference) = left.checked_sub(*right) =>
                    {
                        ExprNode::Number(difference)
                    }
                    (
                        Arithmetic::WrappingSubtract(bits),
                        ExprNode::Number(left),
                        ExprNode::Number(right),
                    ) => ExprNode::Number(
                        left.wrapping_sub(*right) & (u128::MAX >> (u128::BITS as u64 - bits)),
                    ),
                    _ => ExprNode::Arithmetic(op, left, right),
                }
            }
            ExprNode::Trimmed(base) => {
                let base = self.expression(base, guards).await?;
                match &self.session.with(|engine| engine.graph[base].clone()) {
                    ExprNode::Text(text) => ExprNode::Text(self.session.with(|engine| {
                        let text = engine.graph[*text].trim_start().to_owned();
                        engine.graph.intern_value(text.as_str())
                    })?),
                    _ => ExprNode::Trimmed(base),
                }
            }
            ExprNode::Length(base) => {
                let base = self.expression(base, guards).await?;
                match &self.session.with(|engine| engine.graph[base].clone()) {
                    ExprNode::Text(text) => ExprNode::Number(
                        self.session.with(|engine| engine.graph[*text].len()) as u128,
                    ),
                    _ => ExprNode::Length(base),
                }
            }
            ExprNode::Found { text, pattern } => ExprNode::Found {
                text: self.expression(text, guards).await?,
                pattern: self.expression(pattern, guards).await?,
            },
            ExprNode::Matches { text, pattern } => ExprNode::Matches {
                text: self.expression(text, guards).await?,
                pattern: self.expression(pattern, guards).await?,
            },
            ExprNode::MatchIndex {
                text,
                pattern,
                occurrence,
            } => ExprNode::MatchIndex {
                text: self.expression(text, guards).await?,
                pattern: self.expression(pattern, guards).await?,
                occurrence: self.expression(occurrence, guards).await?,
            },
            ExprNode::MatchEntry(TextMatchNode {
                text,
                pattern,
                occurrence,
            }) => ExprNode::MatchEntry(TextMatchNode {
                text: self.expression(text, guards).await?,
                pattern: self.expression(pattern, guards).await?,
                occurrence: self.expression(occurrence, guards).await?,
            }),
            ExprNode::Tokens { text, consumed } => ExprNode::Tokens {
                text: self.expression(text, guards).await?,
                consumed: self.expression(consumed, guards).await?,
            },
            ExprNode::Token(TokenNode {
                text,
                start,
                length,
            }) => ExprNode::Token(TokenNode {
                text: self.expression(text, guards).await?,
                start: self.expression(start, guards).await?,
                length: self.expression(length, guards).await?,
            }),
            ExprNode::NextToken(TokenNode {
                text,
                start,
                length,
            }) => ExprNode::NextToken(TokenNode {
                text: self.expression(text, guards).await?,
                start: self.expression(start, guards).await?,
                length: self.expression(length, guards).await?,
            }),
            ExprNode::Partition {
                sequence,
                predicate,
            } => ExprNode::Partition {
                sequence: self.expression(sequence, guards).await?,
                predicate: self.expression(predicate, guards).await?,
            },
            ExprNode::Slice { text, start, end } => ExprNode::Slice {
                text: self.expression(text, guards).await?,
                start: self.expression(start, guards).await?,
                end: self.expression(end, guards).await?,
            },
            ExprNode::Test(condition) => {
                let condition = self.condition(condition, guards).await?;
                let value = self.session.with(|engine| {
                    let (value, support) = engine.test(condition, guards)?;
                    engine.observe(support)?;
                    Ok::<_, CapacityError>(value)
                })?;
                return Ok(value);
            }
            ExprNode::Unknown
            | ExprNode::Serialized { .. }
            | ExprNode::Cursor { .. }
            | ExprNode::Opaque(_)
            | ExprNode::Argument(_)
            | ExprNode::Range(_)
            | ExprNode::Number(_)
            | ExprNode::Text(_) => return Ok(expression),
        };
        Ok(self.session.with(|engine| engine.graph.intern_expr(node))?)
    }

    async fn step_condition(
        &self,
        condition: ConditionId<'g>,
        guards: GuardContextId<'g>,
    ) -> Step<ConditionId<'g>> {
        let node = match self.session.with(|engine| engine.graph[condition].clone()) {
            ConditionNode::Compare(order, left, right) => {
                let left = self.expression(left, guards).await?;
                let right = self.expression(right, guards).await?;
                let condition = self.session.with(|engine| {
                    engine
                        .graph
                        .intern_condition(ConditionNode::Compare(order, left, right))
                })?;
                for element in [left, right] {
                    let ExprNode::Element(base, index) =
                        self.session.with(|engine| engine.graph[element].clone())
                    else {
                        continue;
                    };
                    let ExprNode::Arithmetic(Arithmetic::Subtract(_), partition, amount) =
                        self.session.with(|engine| engine.graph[index].clone())
                    else {
                        continue;
                    };
                    let ExprNode::Partition {
                        sequence,
                        predicate,
                    } = self.session.with(|engine| engine.graph[partition].clone())
                    else {
                        continue;
                    };
                    let ExprNode::Closure(def, captures) =
                        self.session.with(|engine| engine.graph[predicate].clone())
                    else {
                        continue;
                    };
                    if base != sequence {
                        continue;
                    }
                    let ExprNode::Number(1) =
                        &self.session.with(|engine| engine.graph[amount].clone())
                    else {
                        continue;
                    };
                    let one = self
                        .session
                        .with(|engine| engine.graph.intern_expr(ExprNode::Number(1)))?;
                    let nonempty = self.session.with(|engine| {
                        engine.graph.intern_condition(ConditionNode::Compare(
                            Order::LessEqual,
                            one,
                            partition,
                        ))
                    })?;
                    if self.session.with(|engine| engine.truth(nonempty, guards))? != Truth::Proven
                    {
                        continue;
                    }
                    let environment = self
                        .session
                        .with(|engine| engine.graph.intern_expr(ExprNode::Aggregate(captures)))?;
                    let call = self.session.with(|engine| {
                        let instance = engine.graph.intern_value(InstanceNode {
                            def,
                            args: crate::values::GenericsId::EMPTY,
                            dispatch: Dispatch::Item,
                        })?;
                        let arguments = crate::sequence::Sequences::from_iter(
                            engine.graph.as_mut(),
                            [environment, element],
                        )?;
                        engine.graph.intern_expr(ExprNode::Call(
                            TargetNode::Direct(instance),
                            arguments,
                            None,
                        ))
                    })?;
                    let call = self.expression(call, guards).await?;
                    if let ExprNode::Test(required) =
                        &self.session.with(|engine| engine.graph[call].clone())
                        && *required == condition
                        && let Some(()) = self.session.with(|engine| {
                            engine
                                .graph
                                .known(crate::contracts::graph::NodeId::Condition(*required))
                        })
                    {
                        let zero = self
                            .session
                            .with(|engine| engine.graph.intern_expr(ExprNode::Number(0)))?;
                        return Ok(self.session.with(|engine| {
                            engine.graph.intern_condition(ConditionNode::Compare(
                                Order::Equal,
                                zero,
                                zero,
                            ))
                        })?);
                    }
                }
                match (
                    &self.session.with(|engine| engine.graph[left].clone()),
                    &self.session.with(|engine| engine.graph[right].clone()),
                    order,
                ) {
                    (
                        ExprNode::Test(condition),
                        ExprNode::Number(value),
                        Order::Equal | Order::NotEqual,
                    )
                    | (
                        ExprNode::Number(value),
                        ExprNode::Test(condition),
                        Order::Equal | Order::NotEqual,
                    ) => match (order, value) {
                        (Order::Equal, 1) | (Order::NotEqual, 0) => return Ok(*condition),
                        (Order::Equal, 0) | (Order::NotEqual, 1) => {
                            return Ok(self
                                .session
                                .with(|engine| engine.graph.negate(*condition))?);
                        }
                        _ => ConditionNode::Compare(order, left, right),
                    },
                    _ => ConditionNode::Compare(order, left, right),
                }
            }
            ConditionNode::Boundary(text, index) => ConditionNode::Boundary(
                self.expression(text, guards).await?,
                self.expression(index, guards).await?,
            ),
            ConditionNode::NotBoundary(text, index) => ConditionNode::NotBoundary(
                self.expression(text, guards).await?,
                self.expression(index, guards).await?,
            ),
            ConditionNode::Variant(value, variant) => {
                ConditionNode::Variant(self.expression(value, guards).await?, variant)
            }
            ConditionNode::NotVariant(value, variant) => {
                ConditionNode::NotVariant(self.expression(value, guards).await?, variant)
            }
            ConditionNode::Returned(target, arguments) => {
                let Some(alternatives) = self
                    .return_paths(target.clone(), &arguments.clone().into(), guards)
                    .await?
                else {
                    return Ok(self.session.with(|engine| {
                        engine
                            .graph
                            .intern_condition(ConditionNode::Returned(target, arguments))
                    })?);
                };
                let zero = self
                    .session
                    .with(|engine| engine.graph.intern_expr(ExprNode::Number(0)))?;
                let one = self
                    .session
                    .with(|engine| engine.graph.intern_expr(ExprNode::Number(1)))?;
                let mut result = zero;
                for conditions in alternatives {
                    let mut path = one;
                    let mut conditions = self.session.with(|engine| engine.graph.scan(conditions));
                    while let Some(condition) = conditions.next() {
                        path = self.session.with(|engine| {
                            engine
                                .graph
                                .intern_expr(ExprNode::Select(condition, path, zero))
                        })?;
                    }
                    let condition = self
                        .session
                        .with(|engine| engine.graph.from_expr(path, 1))?;
                    result = self.session.with(|engine| {
                        engine
                            .graph
                            .intern_expr(ExprNode::Select(condition, one, result))
                    })?;
                }
                return Ok(self
                    .session
                    .with(|engine| engine.graph.from_expr(result, 1))?);
            }
            ConditionNode::Unknown => ConditionNode::Unknown,
        };
        Ok(self
            .session
            .with(|engine| engine.graph.intern_condition(node))?)
    }

    async fn return_paths(
        &self,
        target: TargetNode<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
        guards: GuardContextId<'g>,
    ) -> Step<Option<Vec<Sequence<'g, ConditionId<'g>>>>> {
        let mut resolved = Vec::new();
        let mut inputs = self.session.with(|engine| engine.graph.scan(*arguments));
        while let Some(value) = inputs.next() {
            resolved.push(self.expression(value, guards).await?);
        }
        let arguments = self.session.with(|engine| {
            crate::sequence::Sequences::from_iter(engine.graph.as_mut(), resolved)
        })?;
        let Some(targets) = self.targets(target, &arguments, guards).await? else {
            return Ok(None);
        };
        let mut alternatives = Vec::new();
        let mut targets = self
            .session
            .with(|engine| crate::sequence::Cursor::from((&engine.target_lists, targets)));
        while let Some((callable, arguments)) = self
            .session
            .with(|engine| targets.next(&engine.target_lists).copied())
        {
            let Answer::ReturnGuards(conditions) = self
                .session
                .query(Query::ReturnGuards(
                    callable,
                    ArgumentContextId::from(arguments),
                ))
                .await?
                .value
            else {
                unreachable!("return guards query result")
            };
            let mut conditions = self.session.with(|engine| {
                crate::sequence::Cursor::from((&engine.return_guards, conditions.0))
            });
            while let Some(conditions) = self
                .session
                .with(|engine| conditions.next(&engine.return_guards).copied())
            {
                if let Some(()) = self
                    .session
                    .with(|engine| engine.refuted(&conditions, guards))?
                {
                    continue;
                }
                alternatives.push(conditions);
            }
        }
        Ok(Some(alternatives))
    }

    async fn step_guards(&self, guards: GuardContextId<'g>) -> Step<GuardPrefixId<'g>> {
        let Some((context, guard)) = self
            .session
            .with(|engine| engine.graph.guard_prefix(guards))?
        else {
            return self.session.with(|engine| {
                let prefix = GuardPrefix::default();
                engine.intern_guard_prefix(prefix)
            });
        };
        let Answer::Guards(previous) = self.session.query(Query::Guards(context)).await?.value
        else {
            unreachable!("guard-prefix query result")
        };
        let mut result = self
            .session
            .with(|engine| engine.guard_prefixes[previous.0 as usize]);
        match self.session.with(|engine| engine.graph[guard].clone()) {
            ConditionNode::Returned(target, arguments) => {
                let Some(alternatives) = self.return_paths(target, &arguments, result.raw).await?
                else {
                    return Ok(previous);
                };
                match alternatives.split_first() {
                    Some(_) => {
                        let common = self
                            .session
                            .with(|engine| engine.graph.common_guards(&alternatives))?;
                        let mut common = self.session.with(|engine| engine.graph.scan(common));
                        while let Some(condition) = common.next() {
                            self.session
                                .with(|engine| result.append(engine.graph, condition))?;
                        }
                    }
                    None => {
                        let zero = self
                            .session
                            .with(|engine| engine.graph.intern_expr(ExprNode::Number(0)))?;
                        let one = self
                            .session
                            .with(|engine| engine.graph.intern_expr(ExprNode::Number(1)))?;
                        let condition = self.session.with(|engine| {
                            engine.graph.intern_condition(ConditionNode::Compare(
                                Order::Equal,
                                zero,
                                one,
                            ))
                        })?;
                        self.session
                            .with(|engine| result.append(engine.graph, condition))?;
                    }
                }
            }
            _ => {
                let condition = self.condition(guard, result.raw).await?;
                self.session
                    .with(|engine| result.append(engine.graph, condition))?;
            }
        }
        self.session
            .with(|engine| engine.intern_guard_prefix(result))
    }

    async fn completes(&self, value: ExprId<'g>, guards: GuardContextId<'g>) -> Step<Completion> {
        let Answer::Completes(value) = self
            .session
            .query(Query::Completes(value, guards))
            .await?
            .value
        else {
            unreachable!("completion query result")
        };
        Ok(value)
    }

    async fn step_completes(
        &self,
        value: ExprId<'g>,
        guards: GuardContextId<'g>,
    ) -> Step<Completion> {
        let node = self.session.with(|engine| engine.graph[value].clone());
        match node {
            ExprNode::Select(condition, yes, no) => {
                let children = self.session.with(|engine| {
                    let mut children = Vec::new();
                    engine.graph.visit_children(
                        NodeId::Condition(condition),
                        |child| match child {
                            NodeId::Expr(value) => children.push(value),
                            NodeId::Condition(_) | NodeId::Choice(_) => {
                                unreachable!("condition nodes contain expressions")
                            }
                        },
                    );
                    children
                });
                for value in children {
                    if self.completes(value, guards).await? == Completion::Never {
                        return Ok(Completion::Never);
                    }
                }
                let condition = self.condition(condition, guards).await?;
                return match self
                    .session
                    .with(|engine| engine.truth(condition, guards))?
                {
                    Truth::Proven => self.completes(yes, guards).await,
                    Truth::Refuted => self.completes(no, guards).await,
                    Truth::Unknown(_) => {
                        let yes = self.completes(yes, guards).await?;
                        let no = self.completes(no, guards).await?;
                        Ok(match (yes, no) {
                            (Completion::Never, Completion::Never) => Completion::Never,
                            _ => Completion::Possible,
                        })
                    }
                };
            }
            ExprNode::Alternatives(root) => {
                let Some(root) = root else {
                    return Ok(Completion::Never);
                };
                let query = Query::ChoiceCompletes(root, guards);
                let Answer::Completes(result) = self.session.query(query).await?.value else {
                    unreachable!("choice completion query result");
                };
                return Ok(result);
            }
            _ => {}
        }
        let (children, conditions) = self.session.with(|engine| {
            let mut children = Vec::new();
            let mut conditions = Vec::new();
            engine
                .graph
                .visit_children(NodeId::Expr(value), |child| match child {
                    NodeId::Expr(value) => children.push(value),
                    NodeId::Condition(condition) => conditions.push(condition),
                    NodeId::Choice(_) => {
                        unreachable!("alternative completion is handled by its choice query")
                    }
                });
            (children, conditions)
        });
        for child in children {
            if self.completes(child, guards).await? == Completion::Never {
                return Ok(Completion::Never);
            }
        }
        for condition in conditions {
            let children = self.session.with(|engine| {
                let mut children = Vec::new();
                engine
                    .graph
                    .visit_children(NodeId::Condition(condition), |child| match child {
                        NodeId::Expr(value) => children.push(value),
                        NodeId::Condition(_) | NodeId::Choice(_) => {
                            unreachable!("condition nodes contain expressions")
                        }
                    });
                children
            });
            for child in children {
                if self.completes(child, guards).await? == Completion::Never {
                    return Ok(Completion::Never);
                }
            }
        }
        let (target, arguments) = match node {
            ExprNode::Call(target, arguments, _) => (target, arguments),
            ExprNode::Global(instance) => (
                TargetNode::Direct(instance),
                crate::sequence::Sequence::EMPTY,
            ),
            _ => return Ok(Completion::Possible),
        };
        let mut resolved = Vec::new();
        let mut inputs = self.session.with(|engine| engine.graph.scan(arguments));
        while let Some(argument) = inputs.next() {
            resolved.push(self.expression(argument, guards).await?);
        }
        let arguments = self.session.with(|engine| {
            crate::sequence::Sequences::from_iter(engine.graph.as_mut(), resolved)
        })?;
        let Some(targets) = self.targets(target, &arguments, guards).await? else {
            return Ok(Completion::Possible);
        };
        let mut targets = self
            .session
            .with(|engine| crate::sequence::Cursor::from((&engine.target_lists, targets)));
        while let Some((callable, arguments)) = self
            .session
            .with(|engine| targets.next(&engine.target_lists).copied())
        {
            let Answer::ReturnGuards(alternatives) = self
                .session
                .query(Query::ReturnGuards(
                    callable,
                    ArgumentContextId::from(arguments),
                ))
                .await?
                .value
            else {
                unreachable!("return guards query result")
            };
            let mut alternatives = self.session.with(|engine| {
                crate::sequence::Cursor::from((&engine.return_guards, alternatives.0))
            });
            while let Some(alternative) = self
                .session
                .with(|engine| alternatives.next(&engine.return_guards).copied())
            {
                if let None = self
                    .session
                    .with(|engine| engine.refuted(&alternative, guards))?
                {
                    return Ok(Completion::Possible);
                }
            }
        }
        Ok(Completion::Never)
    }

    async fn step_return_guards(
        &self,
        callable: InstanceId<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
    ) -> Step<Vec<Sequence<'g, ConditionId<'g>>>> {
        let Some(body) = self
            .session
            .with(|engine| engine.bodies.get(&engine.graph[callable].def).cloned())
        else {
            return Ok(vec![crate::sequence::Sequence::EMPTY]);
        };
        let invocation = Invocation {
            relocation: Relocation::Into(None),
            generics: self
                .session
                .with(|engine| engine.graph[callable])
                .args
                .clone(),
        };
        let mut alternatives = Vec::new();
        let mut returns = self.session.with(|engine| {
            engine
                .graph
                .scan(engine.body_values[body.0 as usize].returns)
        });
        while let Some(returned) = returns.next() {
            let guards = self.session.with(|engine| {
                engine
                    .graph
                    .substitute_guards(&returned.guards, arguments, &invocation)
            })?;
            let context = self.guards(&guards).await?;
            let guards = context.0;
            let empty = GuardContextId(crate::sequence::Sequence::EMPTY);
            if let Some(()) = self.session.with(|engine| engine.refuted(&guards, empty))? {
                continue;
            }
            let value = self.session.with(|engine| {
                engine
                    .graph
                    .substitute_expr(returned.value, arguments, &invocation)
            })?;
            if self.completes(value, context).await? == Completion::Never {
                continue;
            }
            alternatives.push(guards);
        }
        Ok(alternatives)
    }

    async fn step_returned(
        &self,
        callable: InstanceId<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
        origin: Option<&OriginId<'g>>,
        guards: GuardContextId<'g>,
    ) -> Step<ExprId<'g>> {
        let fallback = self.session.with(|engine| {
            engine.graph.intern_expr(match origin {
                Some(origin) => ExprNode::Opaque(*origin),
                None => ExprNode::Unknown,
            })
        })?;
        let Some(body) = self
            .session
            .with(|engine| engine.bodies.get(&engine.graph[callable].def).cloned())
        else {
            return Ok(fallback);
        };
        let invocation = Invocation {
            relocation: Relocation::Into(
                origin
                    .and_then(|origin| self.session.with(|engine| engine.graph[*origin].identity)),
            ),
            generics: self
                .session
                .with(|engine| engine.graph[callable])
                .args
                .clone(),
        };
        let mut result = None;
        let mut returns = self.session.with(|engine| {
            engine
                .graph
                .scan(engine.body_values[body.0 as usize].returns)
        });
        while let Some(returned) = returns.next() {
            let mut conditions = crate::sequence::Sequence::EMPTY;
            let mut input = self
                .session
                .with(|engine| engine.graph.scan(returned.guards));
            while let Some(condition) = input.next() {
                let condition = self.session.with(|engine| {
                    engine
                        .graph
                        .substitute_condition(condition, arguments, &invocation)
                })?;
                let condition = self.condition(condition, guards).await?;
                conditions = self
                    .session
                    .with(|engine| engine.graph.push(conditions, condition))?;
            }
            let conditions = self.guards(&conditions).await?;
            let conditions = conditions.0;
            if let Some(()) = self
                .session
                .with(|engine| engine.refuted(&conditions, guards))?
            {
                continue;
            }
            let value = self.session.with(|engine| {
                engine
                    .graph
                    .substitute_expr(returned.value, arguments, &invocation)
            })?;
            let value = self.expression(value, guards).await?;
            result = Some(match result {
                Some(previous) => self
                    .session
                    .with(|engine| engine.graph.join(previous, value, Join::Hull))?,
                None => value,
            });
        }
        Ok(match result {
            Some(value) => value,
            None => fallback,
        })
    }

    async fn step_choice_targets(
        &self,
        root: ChoiceId<'g>,
        target: ChoiceTarget<'g>,
        arguments: ArgumentContextId<'g>,
        guards: GuardContextId<'g>,
    ) -> Step<Option<Sequence<'g, (InstanceId<'g>, Sequence<'g, ExprId<'g>>)>>> {
        match self.session.with(|engine| engine.graph[root].node) {
            ChoiceNode::Value(value) => {
                let mut arguments = arguments.0;
                let target = match target {
                    ChoiceTarget::Indirect => TargetNode::Indirect(value),
                    ChoiceTarget::Receiver(callable) => {
                        arguments = self
                            .session
                            .with(|engine| {
                                crate::sequence::Sequences::replace(
                                    engine.graph.as_mut(),
                                    arguments,
                                    0,
                                    value,
                                )
                            })?
                            .expect("virtual dispatch has a receiver argument");
                        TargetNode::Direct(callable)
                    }
                };
                self.targets(target, &arguments, guards).await
            }
            ChoiceNode::Branch(left, right) => {
                let Answer::Targets(left) = self
                    .session
                    .query(Query::ChoiceTargets(left, target, arguments, guards))
                    .await?
                    .value
                else {
                    unreachable!("choice target query result");
                };
                let Some(left) = left else {
                    return Ok(None);
                };
                let Answer::Targets(right) = self
                    .session
                    .query(Query::ChoiceTargets(right, target, arguments, guards))
                    .await?
                    .value
                else {
                    unreachable!("choice target query result");
                };
                let Some(right) = right else {
                    return Ok(None);
                };
                Ok(Some(
                    self.session
                        .with(|engine| engine.target_lists.append(left, right))?,
                ))
            }
        }
    }

    async fn step_targets(
        &self,
        target: &TargetNode<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
        guards: GuardContextId<'g>,
    ) -> Step<Option<Sequence<'g, (InstanceId<'g>, Sequence<'g, ExprId<'g>>)>>> {
        match target {
            TargetNode::Indirect(value) => {
                let value = self.expression(*value, guards).await?;
                match self.session.with(|engine| engine.graph[value].clone()) {
                    ExprNode::Function(instance) => {
                        self.targets(TargetNode::Direct(instance), arguments, guards)
                            .await
                    }
                    ExprNode::Closure(def, _) => {
                        let callable = self.session.with(|engine| {
                            let args = crate::values::GenericsId::EMPTY;
                            engine.graph.intern_value(InstanceNode {
                                def,
                                args,
                                dispatch: Dispatch::Item,
                            })
                        })?;
                        let arguments = self.session.with(|engine| {
                            let prefix = crate::sequence::Sequences::from_iter(
                                engine.graph.as_mut(),
                                [value],
                            )?;
                            engine.graph.append(prefix, *arguments)
                        })?;
                        Ok(Some(self.session.with(|engine| {
                            engine.target_lists.from_iter([(callable, arguments)])
                        })?))
                    }
                    ExprNode::Typed(_, value) => {
                        self.targets(TargetNode::Indirect(value), arguments, guards)
                            .await
                    }
                    ExprNode::Select(_, yes, no) => {
                        let Some(targets) = self
                            .targets(TargetNode::Indirect(yes), arguments, guards)
                            .await?
                        else {
                            return Ok(None);
                        };
                        let Some(other) = self
                            .targets(TargetNode::Indirect(no), arguments, guards)
                            .await?
                        else {
                            return Ok(None);
                        };
                        Ok(Some(self.session.with(|engine| {
                            engine.target_lists.append(targets, other)
                        })?))
                    }
                    ExprNode::Alternatives(root) => match root {
                        None => Ok(Some(crate::sequence::Sequence::EMPTY)),
                        Some(root) => {
                            let query = Query::ChoiceTargets(
                                root,
                                ChoiceTarget::Indirect,
                                ArgumentContextId::from(*arguments),
                                guards,
                            );
                            let Answer::Targets(result) = self.session.query(query).await?.value
                            else {
                                unreachable!("choice target query result");
                            };
                            Ok(result)
                        }
                    },
                    _ => Ok(None),
                }
            }
            TargetNode::Direct(callable) => {
                let instance = self.session.with(|engine| engine.graph[*callable]);
                let callable_trait = match self
                    .session
                    .with(|engine| engine.tcx)
                    .trait_of_assoc(instance.def)
                {
                    Some(owner)
                        if Some(owner)
                            == self
                                .session
                                .with(|engine| engine.tcx)
                                .lang_items()
                                .fn_trait()
                            || Some(owner)
                                == self
                                    .session
                                    .with(|engine| engine.tcx)
                                    .lang_items()
                                    .fn_mut_trait()
                            || Some(owner)
                                == self
                                    .session
                                    .with(|engine| engine.tcx)
                                    .lang_items()
                                    .fn_once_trait() =>
                    {
                        Some(())
                    }
                    _ => None,
                };
                let (first, second, len) = self.session.with(|engine| {
                    (
                        crate::sequence::Sequences::get(engine.graph.as_ref(), *arguments, 0)
                            .copied(),
                        crate::sequence::Sequences::get(engine.graph.as_ref(), *arguments, 1)
                            .copied(),
                        crate::sequence::Sequences::len(engine.graph.as_ref(), *arguments),
                    )
                });
                if let Some(()) = callable_trait {
                    let (Some(function), Some(values), 2) = (first, second, len) else {
                        return Ok(None);
                    };
                    let ExprNode::Aggregate(values) =
                        self.session.with(|engine| engine.graph[values])
                    else {
                        return Ok(None);
                    };
                    return self
                        .targets(TargetNode::Indirect(function), &values, guards)
                        .await;
                }
                if self
                    .session
                    .with(|engine| engine.tcx)
                    .def_kind(instance.def)
                    == rustc_hir::def::DefKind::Closure
                {
                    let arguments = match (first, second, len) {
                        (Some(environment), Some(values), 2) => {
                            match self.session.with(|engine| engine.graph[values]) {
                                ExprNode::Aggregate(values) => self.session.with(|engine| {
                                    let prefix = crate::sequence::Sequences::from_iter(
                                        engine.graph.as_mut(),
                                        [environment],
                                    )?;
                                    engine.graph.append(prefix, values)
                                })?,
                                _ => *arguments,
                            }
                        }
                        _ => *arguments,
                    };
                    return Ok(Some(self.session.with(|engine| {
                        engine.target_lists.from_iter([(*callable, arguments)])
                    })?));
                }
                let mut instance = instance;
                if let Dispatch::Virtual = instance.dispatch {
                    let Some(receiver) = first else {
                        return Ok(None);
                    };
                    match self.session.with(|engine| engine.graph[receiver]) {
                        ExprNode::Typed(ty, _) => {
                            let changed = self.session.with(|engine| {
                                engine.graph.specialize_receiver(&mut instance, ty)
                            })?;
                            if let None = changed {
                                return Ok(None);
                            }
                        }
                        ExprNode::Select(_, yes, no) => {
                            let mut resolved = crate::sequence::Sequence::EMPTY;
                            for receiver in [yes, no] {
                                let arguments = self
                                    .session
                                    .with(|engine| {
                                        crate::sequence::Sequences::replace(
                                            engine.graph.as_mut(),
                                            *arguments,
                                            0,
                                            receiver,
                                        )
                                    })?
                                    .expect("receiver argument exists");
                                let Some(targets) =
                                    self.targets(*target, &arguments, guards).await?
                                else {
                                    return Ok(None);
                                };
                                resolved = self
                                    .session
                                    .with(|engine| engine.target_lists.append(resolved, targets))?;
                            }
                            return Ok(Some(resolved));
                        }
                        ExprNode::Alternatives(root) => {
                            let Some(root) = root else {
                                return Ok(Some(crate::sequence::Sequence::EMPTY));
                            };
                            let query = Query::ChoiceTargets(
                                root,
                                ChoiceTarget::Receiver(*callable),
                                ArgumentContextId(*arguments),
                                guards,
                            );
                            let Answer::Targets(result) = self.session.query(query).await?.value
                            else {
                                unreachable!("choice receiver query result");
                            };
                            return Ok(result);
                        }
                        _ => return Ok(None),
                    }
                }
                let instance = self.session.with(|engine| {
                    let id = engine.graph.intern_value(instance)?;
                    engine.captures.resolve_instance(id)
                })?;
                Ok(
                    match self.session.with(|engine| engine.graph[instance].dispatch) {
                        Dispatch::Item => Some(self.session.with(|engine| {
                            engine.target_lists.from_iter([(instance, *arguments)])
                        })?),
                        Dispatch::Virtual | Dispatch::Shim | Dispatch::Unresolved => None,
                    },
                )
            }
        }
    }

    async fn step_requirements(
        &self,
        callable: InstanceId<'g>,
        parameters: &Sequence<'g, ExprId<'g>>,
    ) -> Step<Requirements<'g>> {
        let instance = self.session.with(|engine| engine.graph[callable]);
        let Some(body) = self
            .session
            .with(|engine| engine.bodies.get(&instance.def).cloned())
        else {
            return Ok(Requirements::default());
        };
        let invocation = Invocation {
            relocation: Relocation::Preserve,
            generics: instance.args,
        };
        let mut result = Requirements::default();
        let mut induction_edges = Vec::new();
        let mut requirements = self.session.with(|engine| {
            crate::sequence::Cursor::from((
                &engine.body_requirements,
                engine.body_values[body.0 as usize].requirements,
            ))
        });
        while let Some((id, span)) = self
            .session
            .with(|engine| requirements.next(&engine.body_requirements).copied())
        {
            let eligible = self.session.with(|engine| {
                let consumer = engine.requirement_values[id.0 as usize].consumer;
                engine.requirement_consumer(consumer)
            });
            if let None = eligible {
                continue;
            }
            let requirement = self.session.with(|engine| {
                let requirement = engine.requirement_values[id.0 as usize].clone();
                engine.substitute_requirement(&requirement, parameters, &invocation)
            })?;
            self.session.with(|engine| {
                let id = engine.intern_requirement_core(requirement)?;
                let plan = engine.intern_requirement_plan(RequirementPlan::Leaf(id))?;
                let mut group = RequirementGroup::EMPTY;
                engine.insert_requirement_id(&mut group, plan)?;
                engine.append_requirement_group(&mut result, span, group)
            })?;
        }
        let calls = self
            .session
            .with(|engine| engine.graph.scan(engine.body_values[body.0 as usize].calls));
        for call in calls {
            let call = self
                .session
                .with(|engine| engine.graph.substitute_call(&call, parameters, &invocation))?;
            let context = self.guards(&call.guards).await?;
            let guards = context.0;
            let empty = GuardContextId(crate::sequence::Sequence::EMPTY);
            if let Some(()) = self.session.with(|engine| engine.refuted(&guards, empty))? {
                continue;
            }
            let mut arguments = crate::sequence::Sequence::EMPTY;
            let mut input = self
                .session
                .with(|engine| engine.graph.scan(call.arguments));
            while let Some(value) = input.next() {
                let value = self.expression(value, context).await?;
                arguments = self
                    .session
                    .with(|engine| engine.graph.push(arguments, value))?;
            }
            let Some(targets) = self.targets(call.target, &arguments, context).await? else {
                continue;
            };
            let mut targets = self
                .session
                .with(|engine| crate::sequence::Cursor::from((&engine.target_lists, targets)));
            while let Some((callee, arguments)) = self
                .session
                .with(|engine| targets.next(&engine.target_lists).copied())
            {
                let finite = self
                    .session
                    .with(|engine| engine.finite_arguments(callee, &arguments));
                let callee_def = self.session.with(|engine| engine.graph[callee].def);
                if let (Some(_), None) = (
                    self.session
                        .with(|engine| engine.recursion.edge(instance.def, callee_def))?,
                    finite,
                ) {
                    self.session.with(|engine| {
                        engine.recursive_edge_requirements(
                            &mut result,
                            &mut induction_edges,
                            callable,
                            callee,
                            &call,
                            guards,
                        )
                    })?;
                    continue;
                }
                if let None = self
                    .session
                    .with(|engine| engine.requirement_candidates.get(&callee_def).copied())
                {
                    continue;
                }
                let mut values = arguments.clone();
                let parameters = match finite {
                    Some(()) => arguments,
                    None => {
                        let mut parameters = crate::sequence::Sequence::EMPTY;
                        let bindings = self.session.with(|engine| engine.graph.scan(arguments));
                        let mut index = 0;
                        for value in bindings {
                            let binding = self.session.with(|engine| {
                                engine.graph.intern_expr(ExprNode::Argument(index))
                            })?;
                            let value = self.session.with(|engine| {
                                engine.graph.parameter(value, binding, &mut values)
                            })?;
                            parameters = self
                                .session
                                .with(|engine| engine.graph.push(parameters, value))?;
                            index += 1;
                        }
                        parameters
                    }
                };
                let Answer::Requirements(requirements) = self
                    .session
                    .query(Query::Requirements(
                        callee,
                        ArgumentContextId::from(parameters),
                    ))
                    .await?
                    .value
                else {
                    unreachable!("requirements query result")
                };
                if let (Some(_), None) = (
                    self.session
                        .with(|engine| engine.recursion.edge(instance.def, callee_def))?,
                    finite,
                ) {
                    self.session.with(|engine| {
                        engine.recursive_edge_requirements(
                            &mut result,
                            &mut induction_edges,
                            callable,
                            callee,
                            &call,
                            guards,
                        )
                    })?;
                    continue;
                }
                let values = ArgumentContextId::from(values);
                let mut groups = self.session.with(|engine| {
                    crate::sequence::Cursor::from((&engine.requirement_groups, requirements.0))
                });
                while let Some(group) = self
                    .session
                    .with(|engine| groups.next(&engine.requirement_groups).copied())
                {
                    let plan = self.session.with(|engine| {
                        engine.intern_requirement_plan(RequirementPlan::Transform(
                            group.requirements.ordered,
                            values,
                            context,
                        ))
                    })?;
                    let mut transformed = RequirementGroup::EMPTY;
                    self.session
                        .with(|engine| engine.insert_requirement_id(&mut transformed, plan))?;
                    if let Some(_) = self
                        .session
                        .with(|engine| engine.recursion.edge(instance.def, callee_def))?
                    {
                        let Answer::ResolvedRequirements(result) = self
                            .session
                            .query(Query::RequirementPlans(
                                transformed.ordered,
                                RequirementOperation::Resolve,
                            ))
                            .await?
                            .value
                        else {
                            unreachable!("requirement plan query result")
                        };
                        transformed = result.0;
                    }
                    self.session.with(|engine| {
                        engine.append_requirement_group(&mut result, call.span, transformed)
                    })?;
                }
            }
        }
        // A recursive frame may run under different guards from its caller.
        // Check the ordinary obligations once with unconstrained, symbolic inputs.
        if !induction_edges.is_empty() {
            let universal = self
                .session
                .with(|engine| engine.symbolic_arguments(instance.def))?;
            let closed = if universal == *parameters {
                result.groups.is_empty()
            } else {
                let context = ArgumentContextId::from(universal);
                let Answer::Requirements(requirements) = self
                    .session
                    .query(Query::Requirements(callable, context))
                    .await?
                    .value
                else {
                    unreachable!("requirements query result")
                };
                requirements.0 == Sequence::EMPTY
            };
            if !closed {
                for (span, guards) in induction_edges {
                    self.session.with(|engine| {
                        engine.recursive_requirement(&mut result, instance.def, span, guards)
                    })?;
                }
            }
        }
        Ok(result)
    }

    async fn classify_local_requirement(&self, id: RequirementId<'g>) -> Step<ReportDisposition> {
        self.session.with(|engine| {
            engine.work.reporting_classifications =
                engine.work.reporting_classifications.saturating_add(1)
        });
        let requirement = self
            .session
            .with(|engine| engine.requirement_values[id.0 as usize].clone());
        if requirement.invalidated != Sequence::EMPTY {
            return Ok(ReportDisposition::Retain);
        }
        if let ConditionNode::Unknown = self
            .session
            .with(|engine| engine.graph[requirement.condition])
        {
            return Ok(ReportDisposition::Discard);
        }
        if let Some(()) = self.session.with(|engine| {
            engine.report_requirement_has_one_unproven_witness(
                requirement.condition,
                requirement.applicability,
            )
        })? {
            return Ok(ReportDisposition::Discard);
        }
        let applicability = self
            .session
            .with(|engine| engine.applicability[requirement.applicability]);
        let mut resolved_condition = None;
        let context = match applicability {
            Applicability::Context(guards) => self.guards(&guards).await?,
            Applicability::Prefix(..) | Applicability::Either(..) => {
                let Some(shared) = self
                    .session
                    .with(|engine| engine.shared_requirement(&requirement, Sequence::EMPTY))?
                else {
                    return Ok(ReportDisposition::Retain);
                };
                match shared.sharing {
                    Sharing::Independent | Sharing::Stable => GuardContextId(Sequence::EMPTY),
                    Sharing::Contextual => {
                        let certificate = self.session.with(|engine| {
                            engine.report_condition_certificate(requirement.condition)
                        })?;
                        match certificate {
                            Some(condition) => resolved_condition = Some(condition),
                            None => {
                                let outcome_certificate = self.session.with(|engine| {
                                    engine.report_outcome_certificate(
                                        requirement.condition,
                                        requirement.applicability,
                                    )
                                })?;
                                match outcome_certificate {
                                    Some(condition) => resolved_condition = Some(condition),
                                    None => {
                                        let Some(()) = self.session.with(|engine| {
                                            engine.report_condition_context_independent(
                                                requirement.condition,
                                                requirement.applicability,
                                            )
                                        })?
                                        else {
                                            return Ok(ReportDisposition::Retain);
                                        };
                                        let condition = self
                                            .condition(
                                                requirement.condition,
                                                GuardContextId(Sequence::EMPTY),
                                            )
                                            .await?;
                                        let Some(()) = self.session.with(|engine| {
                                            engine.report_condition_shape_certificate(condition)
                                        }) else {
                                            return Ok(ReportDisposition::Retain);
                                        };
                                        resolved_condition = Some(condition);
                                    }
                                }
                            }
                        }
                        GuardContextId(Sequence::EMPTY)
                    }
                }
            }
        };
        if self
            .session
            .with(|engine| engine.graph.conjunction(&context.0, &Sequence::EMPTY))?
            == Truth::Refuted
        {
            return Ok(ReportDisposition::Discard);
        }
        let condition = match resolved_condition {
            Some(condition) => condition,
            None => self.condition(requirement.condition, context).await?,
        };
        let Truth::Unknown(_) = self
            .session
            .with(|engine| engine.truth(condition, context))?
        else {
            return Ok(ReportDisposition::Retain);
        };
        let disposition = self.session.with(|engine| match engine.graph[condition] {
            ConditionNode::Compare(Order::Less | Order::LessEqual, left, right) => {
                match (&engine.graph[left], &engine.graph[right]) {
                    (ExprNode::Field(..), ExprNode::Field(..)) => ReportDisposition::Retain,
                    _ => ReportDisposition::Discard,
                }
            }
            ConditionNode::Compare(_, _, _)
            | ConditionNode::Boundary(..)
            | ConditionNode::NotBoundary(..)
            | ConditionNode::Variant(..)
            | ConditionNode::NotVariant(..)
            | ConditionNode::Unknown
            | ConditionNode::Returned(..) => ReportDisposition::Discard,
        });
        Ok(disposition)
    }

    async fn step_requirement_plans(
        &self,
        sequence: Sequence<'g, RequirementPlanId<'g>>,
        operation: RequirementOperation<'g>,
    ) -> Step<ResolvedRequirements<'g>> {
        self.session.with(|engine| {
            engine.work.requirement_visits = engine.work.requirement_visits.saturating_add(1);
            if let RequirementOperation::LocalFindings = operation {
                engine.work.reporting_plan_visits =
                    engine.work.reporting_plan_visits.saturating_add(1);
            }
        });
        let mut result = RequirementGroup::EMPTY;
        match self
            .session
            .with(|engine| engine.requirement_sequences.parts(sequence))?
        {
            crate::sequence::Parts::Empty => {}
            crate::sequence::Parts::Branch(left, right) => {
                let Answer::ResolvedRequirements(left) = self
                    .session
                    .query(Query::RequirementPlans(left, operation))
                    .await?
                    .value
                else {
                    unreachable!("requirement plan query result")
                };
                let Answer::ResolvedRequirements(right) = self
                    .session
                    .query(Query::RequirementPlans(right, operation))
                    .await?
                    .value
                else {
                    unreachable!("requirement plan query result")
                };
                result = self
                    .session
                    .with(|engine| engine.join_requirement_groups(left.0, right.0))?;
            }
            crate::sequence::Parts::Leaf(plan) => {
                match self
                    .session
                    .with(|engine| engine.requirement_plans[plan.0 as usize])
                {
                    RequirementPlan::Leaf(id) => match operation {
                        RequirementOperation::Resolve => self
                            .session
                            .with(|engine| engine.insert_requirement_id(&mut result, plan))?,
                        RequirementOperation::LocalFindings => {
                            match self.classify_local_requirement(id).await? {
                                ReportDisposition::Retain => self.session.with(|engine| {
                                    engine.insert_requirement_id(&mut result, plan)
                                })?,
                                ReportDisposition::Discard => {}
                            }
                        }
                        RequirementOperation::Transform(arguments, guards) => {
                            self.session.with(|engine| {
                                engine.work.requirement_applications =
                                    engine.work.requirement_applications.saturating_add(1)
                            });
                            let Answer::ResolvedRequirements(value) = self
                                .session
                                .query(Query::TransformRequirements(id, arguments, guards))
                                .await?
                                .value
                            else {
                                unreachable!("requirement transformation query result")
                            };
                            result = value.0;
                        }
                    },
                    RequirementPlan::Transform(sequence, arguments, guards) => {
                        let Answer::ResolvedRequirements(inner) = self
                            .session
                            .query(Query::RequirementPlans(
                                sequence,
                                RequirementOperation::Transform(arguments, guards),
                            ))
                            .await?
                            .value
                        else {
                            unreachable!("requirement plan query result")
                        };
                        result = match operation {
                            RequirementOperation::Resolve => inner.0,
                            RequirementOperation::Transform(..)
                            | RequirementOperation::LocalFindings => {
                                let Answer::ResolvedRequirements(outer) = self
                                    .session
                                    .query(Query::RequirementPlans(inner.0.ordered, operation))
                                    .await?
                                    .value
                                else {
                                    unreachable!("requirement plan query result")
                                };
                                outer.0
                            }
                        };
                    }
                }
            }
        }
        Ok(ResolvedRequirements(result))
    }

    async fn step_transform_requirements(
        &self,
        id: RequirementId<'g>,
        arguments: ArgumentContextId<'g>,
        guards: GuardContextId<'g>,
    ) -> Step<ResolvedRequirements<'g>> {
        self.session.with(|engine| {
            engine.work.requirement_transformations =
                engine.work.requirement_transformations.saturating_add(1)
        });
        let mut requirement = self.session.with(|engine| {
            let requirement = engine.requirement_values[id.0 as usize].clone();
            let invocation = Invocation {
                relocation: Relocation::Into(None),
                generics: GenericsId::EMPTY,
            };
            engine.substitute_requirement(&requirement, &arguments.0, &invocation)
        })?;
        let mut result = RequirementGroup::EMPTY;
        let applicability = self
            .session
            .with(|engine| engine.applicability[requirement.applicability]);
        let shared = self
            .session
            .with(|engine| engine.shared_requirement(&requirement, guards.0))?;
        if let (
            Applicability::Context(inner_guards),
            Some(SharedRequirement {
                sharing: Sharing::Contextual,
                ..
            }),
        ) = (applicability, shared.as_ref())
        {
            let context_guards = self
                .session
                .with(|engine| engine.graph.append(guards.0, inner_guards))?;
            let context = self.guards(&context_guards).await?;
            let condition = self.condition(requirement.condition, context).await?;
            if self
                .session
                .with(|engine| engine.truth(condition, context))?
                != Truth::Proven
            {
                self.session.with(|engine| {
                    let applicability = if context.0 == context_guards
                        && condition == requirement.condition
                    {
                        engine
                            .applicability
                            .intern(Applicability::Prefix(guards.0, requirement.applicability))?
                    } else {
                        engine
                            .applicability
                            .intern(Applicability::Context(context.0))?
                    };
                    let requirement = RequirementCore {
                        condition,
                        applicability,
                        ..requirement
                    };
                    let id = engine.intern_requirement_core(requirement)?;
                    let plan = engine.intern_requirement_plan(RequirementPlan::Leaf(id))?;
                    engine.insert_requirement_id(&mut result, plan)
                })?;
            }
            return Ok(ResolvedRequirements(result));
        }
        if let Some(shared) = shared {
            if let Sharing::Independent = shared.sharing {
                requirement.condition = self
                    .condition(requirement.condition, GuardContextId(Sequence::EMPTY))
                    .await?;
            }
            requirement.applicability = self.session.with(|engine| {
                engine
                    .applicability
                    .intern(Applicability::Prefix(shared.prefix, shared.applicability))
            })?;
            self.session.with(|engine| {
                let id = engine.intern_requirement_core(requirement)?;
                let plan = engine.intern_requirement_plan(RequirementPlan::Leaf(id))?;
                engine.insert_requirement_id(&mut result, plan)
            })?;
            return Ok(ResolvedRequirements(result));
        }
        requirement.applicability = self.session.with(|engine| {
            engine
                .applicability
                .intern(Applicability::Prefix(guards.0, requirement.applicability))
        })?;
        self.session.with(|engine| {
            let id = engine.intern_requirement_core(requirement)?;
            let plan = engine.intern_requirement_plan(RequirementPlan::Leaf(id))?;
            engine.insert_requirement_id(&mut result, plan)
        })?;
        Ok(ResolvedRequirements(result))
    }

    async fn step_materialized(&self, call: &CallNode<'g>) -> Step<Sequence<'g, CallNode<'g>>> {
        let context = self.guards(&call.guards).await?;
        let guards = context.0;
        let mut arguments = crate::sequence::Sequence::EMPTY;
        let mut input = self
            .session
            .with(|engine| engine.graph.scan(call.arguments));
        while let Some(argument) = input.next() {
            let argument = self.expression(argument, context).await?;
            arguments = self
                .session
                .with(|engine| engine.graph.push(arguments, argument))?;
        }
        let calls: Vec<_> = match self.targets(call.target, &arguments, context).await? {
            Some(targets) => self.session.with(|engine| {
                engine
                    .target_lists
                    .iter(targets)
                    .map(|&(callable, arguments)| CallNode {
                        basis: call.basis,
                        target: TargetNode::Direct(callable),
                        arguments,
                        guards,
                        span: call.span,
                    })
                    .collect()
            }),
            None => vec![CallNode {
                basis: call.basis,
                target: call.target,
                arguments,
                guards,
                span: call.span,
            }],
        };
        self.session
            .with(|engine| crate::sequence::Sequences::from_iter(engine.graph.as_mut(), calls))
    }

    async fn step_contextual(
        &self,
        callable: InstanceId<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
    ) -> Step<Sequence<'g, CallNode<'g>>> {
        let instance = self.session.with(|engine| engine.graph[callable]);
        let Some(body) = self
            .session
            .with(|engine| engine.bodies.get(&instance.def).cloned())
        else {
            return Ok(Sequence::EMPTY);
        };
        let invocation = Invocation {
            relocation: Relocation::Into(None),
            generics: instance.args,
        };
        let mut result = Vec::new();
        let calls = self
            .session
            .with(|engine| engine.graph.scan(engine.body_values[body.0 as usize].calls));
        for call in calls {
            let call = self
                .session
                .with(|engine| engine.graph.substitute_call(&call, arguments, &invocation))?;
            let Answer::Calls(calls) = self
                .session
                .query(Query::Materialized(
                    call.target,
                    ArgumentContextId::from(call.arguments),
                    GuardContextId::from(call.guards),
                    match &call.basis {
                        CheckBasis::Expression => CheckBasis::Expression,
                        CheckBasis::ControlFlow(basis) => {
                            CheckBasis::ControlFlow(GuardContextId::from(*basis))
                        }
                    },
                    call.span,
                ))
                .await?
                .value
            else {
                unreachable!("materialized call query result")
            };
            let calls = self.session.with(|engine| engine.graph.scan(calls));
            for call in calls {
                if let TargetNode::Direct(callee) = call.target {
                    self.session.with(|engine| {
                        engine
                            .recursion
                            .insert(instance.def, engine.graph[callee].def)
                    })?;
                }
                result.push(call);
            }
        }
        self.session
            .with(|engine| crate::sequence::Sequences::from_iter(engine.graph.as_mut(), result))
    }
}

impl<'a, 'tcx, 'g> Engine for Evaluator<'a, 'tcx, 'g> {
    type Query = Query<'g>;
    type Answer = Derived<'g>;
    type Error = CapacityError;
    type Frame = Frame<'g>;

    fn lookup(&mut self, query: &Self::Query) -> Result<Lookup<Self::Answer>, Self::Error> {
        let slot = self.cache_slot(query)?;
        match self.cache.get(query, self.revision(query), slot) {
            Some(Memo::Ready(value)) => {
                self.observe(value.support)?;
                return Ok(Lookup::Ready(value));
            }
            Some(Memo::Active(id)) => {
                self.dependencies.observe(Dependency::Blocked(id));
                let value = Derived {
                    value: self.fallback(query)?,
                    support: Support {
                        facts: Evidence::default(),
                        derivation: Derivation::Recursive,
                    },
                };
                self.observe(value.support)?;
                return Ok(Lookup::Ready(value));
            }
            Some(Memo::Deferred { value, dependency }) => {
                if let Some(_) = self.dependencies.pending(dependency) {
                    self.dependencies.observe(dependency);
                    self.observe(value.support)?;
                    return Ok(Lookup::Ready(value));
                }
            }
            None => {
                if let Query::Expression(value, guards) = query
                    && let ExprNode::Test(condition) = &self.graph[*value]
                    && let Some(GuardDependence::Independent) =
                        self.guard_dependence.get(&NodeId::Condition(*condition))
                {
                    let condition = *condition;
                    let empty = GuardContextId(crate::sequence::Sequence::EMPTY);
                    let query = Query::Condition(condition, empty);
                    if let Some(Memo::Ready(Derived {
                        value: Answer::Condition(resolved),
                        support,
                    })) = self.cache.get(
                        &query,
                        self.revision(&query),
                        CacheSlot::Condition(condition, empty),
                    ) && support == Support::default()
                    {
                        let (value, mut support) = self.test(resolved, *guards)?;
                        support.facts = self.graph.discharge(support.facts, *guards)?;
                        self.observe(support)?;
                        return Ok(Lookup::Ready(Derived {
                            value: Answer::Expression(value),
                            support,
                        }));
                    }
                }
            }
        }
        let recursive = match query {
            Query::Returned(callable, arguments, _, _)
            | Query::ReturnGuards(callable, arguments) => Some((*callable, arguments)),
            _ => None,
        };
        if let Some((callable, arguments)) = recursive {
            let def = self.graph[callable].def;
            if let Some(id) = self
                .definition_activity
                .get(&def)
                .and_then(|activity| activity.active)
                && let None = self.finite_arguments(callable, &arguments.0)
            {
                self.dependencies.observe(Dependency::Blocked(id));
                let value = Derived {
                    value: self.fallback(query)?,
                    support: Support {
                        facts: Evidence::default(),
                        derivation: Derivation::Recursive,
                    },
                };
                self.observe(value.support)?;
                return Ok(Lookup::Ready(value));
            }
        }
        Ok(Lookup::Missing)
    }
    fn enter(&mut self, query: Query<'g>) -> Result<Frame<'g>, CapacityError> {
        let revision = self.revision(&query);
        let slot = self.cache_slot(&query)?;
        let previous = self.cache.get(&query, revision, slot);
        let id = self.dependencies.enter().ok_or(CapacityError::Queries)?;
        if let Query::ReturnGuards(..) = &query {
            self.returning.push(self.queries.len());
        }
        match &query {
            Query::Returned(callable, ..)
            | Query::ReturnGuards(callable, ..)
            | Query::Requirements(callable, ..)
            | Query::Contextual(callable, ..) => {
                let instance = self.graph[*callable];
                let def = instance.def;
                let arguments = instance.args.clone();
                *self
                    .definition_activity
                    .entry(def)
                    .or_default()
                    .generics
                    .get_or_insert_default()
                    .entry(arguments)
                    .or_default() += 1;
            }
            _ => {}
        }
        self.queries.push(Activation {
            query: query.clone(),
            support: Support::default(),
        });
        self.cache
            .insert(&query, (revision, Memo::Active(id)), slot, &mut self.work);
        let first_return = match &query {
            Query::Returned(callable, ..) | Query::ReturnGuards(callable, ..) => {
                let def = self.graph[*callable].def;
                let activity = self.definition_activity.entry(def).or_default();
                match activity.active {
                    None => {
                        activity.active = Some(id);
                        Some(def)
                    }
                    Some(_) => None,
                }
            }
            _ => None,
        };
        Ok(Frame {
            first_return,
            query,
            previous,
            revision,
            slot,
        })
    }
    fn finish(
        &mut self,
        frame: Self::Frame,
        answer: Self::Answer,
    ) -> Finished<Self::Query, Self::Answer> {
        if let Query::ReturnGuards(..) = &frame.query {
            self.returning
                .pop()
                .expect("return-guard query has an index");
        }
        match &frame.query {
            Query::Returned(callable, ..)
            | Query::ReturnGuards(callable, ..)
            | Query::Requirements(callable, ..)
            | Query::Contextual(callable, ..) => {
                let instance = self.graph[*callable];
                let def = instance.def;
                let arguments = instance.args.clone();
                let activity = self
                    .definition_activity
                    .get_mut(&def)
                    .expect("scheduled callable has a generic context");
                let contexts = activity
                    .generics
                    .as_mut()
                    .expect("scheduled callable has a generic context");
                let count = contexts
                    .get_mut(&arguments)
                    .expect("scheduled generic context is active");
                *count -= 1;
                if *count == 0 {
                    contexts.swap_remove(&arguments);
                }
                if contexts.is_empty() {
                    activity.generics = None;
                }
            }
            _ => {}
        }
        if let Some(def) = frame.first_return
            && let Some(activity) = self.definition_activity.get_mut(&def)
        {
            activity.active = None;
        }
        self.queries
            .pop()
            .expect("scheduled query owns dependencies");
        let dependency = self.dependencies.finish();
        let (memo, progress) = match dependency {
            Dependency::Independent => (Memo::Ready(answer.clone()), Progress::Settled),
            Dependency::Blocked(_) => (
                Memo::Deferred {
                    value: answer.clone(),
                    dependency,
                },
                Progress::Blocked,
            ),
            Dependency::Observed => match frame.previous {
                Some(Memo::Deferred { value, .. }) if value == answer => {
                    (Memo::Ready(answer.clone()), Progress::Settled)
                }
                _ => (
                    Memo::Deferred {
                        value: answer.clone(),
                        dependency,
                    },
                    Progress::Retry,
                ),
            },
        };
        let graph_changed = frame.revision != self.revision(&frame.query);
        self.cache.insert(
            &frame.query,
            (frame.revision, memo),
            frame.slot,
            &mut self.work,
        );

        match (progress, graph_changed) {
            (Progress::Retry, _) | (_, true) => Finished::Retry(frame.query),
            _ => Finished::Ready(answer),
        }
    }
    async fn execute(
        session: Session<'_, Self>,
        query: Self::Query,
    ) -> Result<Self::Answer, Self::Error> {
        let value = Evaluation { session }.step(&query).await?;
        let mut support = session.with(|engine| {
            engine
                .queries
                .last()
                .expect("executing query owns proof support")
                .support
        });
        match query {
            Query::Guards(_)
            | Query::ReturnGuards(..)
            | Query::Requirements(..)
            | Query::TransformRequirements(..)
            | Query::RequirementPlans(..)
            | Query::Materialized(..)
            | Query::Contextual(..) => support.facts = Evidence::default(),
            Query::Reduced(_, guards)
            | Query::ChoiceTargets(_, _, _, guards)
            | Query::ChoiceCompletes(_, guards)
            | Query::Expression(_, guards)
            | Query::Condition(_, guards)
            | Query::Targets(_, _, guards)
            | Query::Returned(_, _, _, guards)
            | Query::Completes(_, guards) => {
                support.facts =
                    session.with(|engine| engine.graph.discharge(support.facts, guards))?;
            }
        }
        Ok(Derived { value, support })
    }
}
