//! Canonical identities shared by the linked contract analysis.

mod choices;
mod collections;
pub(crate) mod comparisons;
pub mod evidence;
pub(crate) mod flows;
pub use choices::{Choice, ChoiceId, ChoiceNode};
pub mod operations;
mod sequences;
pub mod sets;
pub mod summaries;

use crate::values::{self, InstanceId, OriginId, TextId, TypeId, Values};
use flows::Flow;

use crate::arena::{ArenaId, Intern};
use crate::memo::Memo;
use crate::sequence::{self, Sequence};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Local;
use rustc_span::Span;

use crate::calls::Target;
use crate::contracts::Encoding;
use crate::contracts::graph::comparisons::Comparisons;
use crate::contracts::tree::{
    Binary, CallTarget, Collection, ConditionBuild, ExprBuild, Input, Leaf, Output, Root, Ternary,
    TextMatch, Token, Unary,
};
use crate::contracts::{Arithmetic, Condition, Expr, Interval, Join, Order, Truth};
use operations::{InputUse, Inputs, Parameter, Query, RewriteKey};
use sets::{SetId, Sets};

enum BinaryNode<K, V> {
    Ready(V),
    Children(K, K),
}

fn fold_binary<S, K: Copy, V>(
    state: &mut S,
    mut node: K,
    mut visit: impl FnMut(&mut S, K) -> Result<BinaryNode<K, V>, CapacityError>,
    mut join: impl FnMut(&mut S, K, V, V) -> Result<V, CapacityError>,
) -> Result<V, CapacityError> {
    enum Frame<K, V> {
        Second { parent: K, child: K },
        Join { parent: K, first: V },
    }
    let mut frames = Vec::new();
    loop {
        let mut value = match visit(state, node)? {
            BinaryNode::Ready(value) => value,
            BinaryNode::Children(first, second) => {
                frames.push(Frame::Second {
                    parent: node,
                    child: second,
                });
                node = first;
                continue;
            }
        };
        loop {
            match frames.pop() {
                None => return Ok(value),
                Some(Frame::Second { parent, child }) => {
                    frames.push(Frame::Join {
                        parent,
                        first: value,
                    });
                    node = child;
                    break;
                }
                Some(Frame::Join { parent, first }) => value = join(state, parent, first, value)?,
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ExprId<'g> {
    index: u32,
    brand: PhantomData<fn(&'g ()) -> &'g ()>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ConditionId<'g> {
    index: u32,
    brand: PhantomData<fn(&'g ()) -> &'g ()>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FlowId<'g> {
    index: u32,
    brand: PhantomData<fn(&'g ()) -> &'g ()>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AlternativeId<'g> {
    index: u32,
    brand: PhantomData<fn(&'g ()) -> &'g ()>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Alternative<'g> {
    pub previous: Option<AlternativeId<'g>>,
    pub value: FlowId<'g>,
    members: SetId<'g, FlowId<'g>>,
}

macro_rules! arena_id {
    ($($id:ident),* $(,)?) => {$ (
        impl ArenaId for $id<'_> {
            fn from_index(index: u32) -> Self { Self { index, brand: PhantomData } }
            fn index(self) -> u32 { self.index }
        }
    )*};
}
arena_id!(ExprId, ConditionId, FlowId, AlternativeId, RewriteId);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct GuardContextId<'g>(pub(crate) Sequence<'g, ConditionId<'g>>);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ArgumentContextId<'g>(pub(crate) Sequence<'g, ExprId<'g>>);

impl<'g> From<Sequence<'g, ConditionId<'g>>> for GuardContextId<'g> {
    fn from(sequence: Sequence<'g, ConditionId<'g>>) -> Self {
        Self(sequence)
    }
}

impl<'g> From<Sequence<'g, ExprId<'g>>> for ArgumentContextId<'g> {
    fn from(sequence: Sequence<'g, ExprId<'g>>) -> Self {
        Self(sequence)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct RewriteId<'g> {
    index: u32,
    brand: PhantomData<fn(&'g ()) -> &'g ()>,
}

pub use crate::arena::CapacityError;

/// Prevents identities from escaping their owning graph or entering a different graph.
// shapelint: allow(shallow-helper) The higher-ranked closure gives each arena a fresh identity scope.
pub fn with_graph<R>(f: impl for<'g> FnOnce(Graph<'g>) -> R) -> R {
    let graph = Graph::new();
    f(graph)
}

impl<'g> Graph<'g> {
    pub(crate) fn new() -> Self {
        Graph {
            substitution_work: operations::SubstitutionWork::default(),
            argument_projections: Memo::new(),
            projected_argument_sequences: sequence::Sequences::new(),
            sequence_input_summaries: Memo::new(),
            proof_work: ProofWork::default(),
            values: Values::new(),
            summaries: summaries::Summaries::new(),
            flows: Intern::new(),
            choices: choices::Choices::default(),
            choice_fields: Memo::new(),
            widened_choices: Memo::new(),
            rewritten_choices: Memo::new(),
            choice_parameters: Memo::new(),
            parameter_choice_values: Memo::new(),
            alternatives: Intern::new(),
            flow_members: Sets::new(),
            flow_joins: Memo::new(),
            input_sets: Sets::new(),
            function_sets: Sets::new(),
            input_summaries: Memo::new(),
            function_summaries: Memo::new(),
            fields: Memo::new(),
            joins: Memo::new(),
            parameters: Memo::new(),
            parameter_values: Memo::new(),
            expressions: Intern::new(),
            conditions: Intern::new(),
            truths: Memo::new(),
            comparisons: Comparisons::default(),
            projected_guards: Memo::new(),
            prepared_guards: Memo::new(),
            guard_projections: Memo::new(),
            guard_projection_summaries: sequence::Fold::default(),
            guard_projection_filters: sequence::TransformCache::default(),
            guard_projection_conditions: sequence::Fold::default(),
            guard_endpoints: sequence::Fold::default(),
            guard_members: sequence::Fold::default(),
            guard_intersections: sequence::TransformCache::default(),
            guard_member_sets: Sets::new(),
            evidence_sequences: Memo::new(),
            guard_classifications: sequence::Fold::default(),
            reference_summaries: Memo::new(),
            reference_sets: Sets::new(),
            conjunctions: Memo::new(),
            condition_sequences: sequence::Sequences::new(),
            expression_sequences: sequence::Sequences::new(),
            invalidated_sequences: sequence::Sequences::new(),
            guard_segments: sequence::Sequences::new(),
            comparison_edges: sequence::Sequences::new(),
            rewrites: Intern::new(),
            rewritten_expressions: Memo::new(),
            rewritten_conditions: Memo::new(),
            rewritten_guard_sequences: sequence::Remap::default(),
            rewritten_argument_sequences: sequence::Remap::default(),
            rewritten_invalidated_sequences: sequence::Remap::default(),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum NodeId<'g> {
    Choice(ChoiceId<'g>),
    Expr(ExprId<'g>),
    Condition(ConditionId<'g>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FlowNodeId<'g> {
    Flow(FlowId<'g>),
    Alternative(AlternativeId<'g>),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ProofWork {
    pub reference_nodes: usize,
    pub flow_join_steps: usize,
    /// Counts top-level conjunction queries, including exact-cache hits.
    pub conjunction_queries: usize,
    /// Counts conjunction fragment results served from the exact memo.
    pub conjunction_cache_hits: usize,
    /// Counts condition leaves whose truth was evaluated for a conjunction.
    pub conjunction_condition_visits: usize,
    /// Counts newly retained `(fragment, guards)` conjunction results.
    pub conjunction_cache_entries: usize,
    pub comparison_states: usize,
    pub comparison_edges: usize,
    /// Counts segment leaves inspected while indexing or materializing projections.
    pub guard_segments: usize,
    /// Counts uncached fragment selections after retaining only relevant target identities.
    pub guard_projection_fragments: usize,
}

pub struct Graph<'g> {
    pub substitution_work: operations::SubstitutionWork,
    pub(crate) argument_projections:
        Memo<(SetId<'g, usize>, ArgumentContextId<'g>), operations::ArgumentProjection<'g>>,
    pub(crate) projected_argument_sequences: sequence::Sequences<'g, (usize, Option<ExprId<'g>>)>,
    pub(crate) sequence_input_summaries:
        Memo<(InputUse, operations::InputSequence<'g>), Inputs<'g>>,
    /// Counts executed proof work on this graph handle; forks start at zero.
    pub proof_work: ProofWork,
    pub values: Values<'g>,
    pub summaries: summaries::Summaries<'g>,
    pub(crate) reference_summaries: Memo<NodeId<'g>, SetId<'g, NodeId<'g>>>,
    pub reference_sets: Sets<'g, NodeId<'g>>,
    conjunctions: Memo<(Sequence<'g, ConditionId<'g>>, Sequence<'g, ConditionId<'g>>), Truth>,
    pub(crate) choices: choices::Choices<'g>,
    pub(crate) widened_choices: Memo<ChoiceId<'g>, Option<ChoiceId<'g>>>,
    pub(crate) choice_fields: Memo<(ChoiceId<'g>, usize), Option<ChoiceId<'g>>>,
    pub(crate) rewritten_choices: Memo<(RewriteId<'g>, ChoiceId<'g>), Option<ChoiceId<'g>>>,
    pub(crate) choice_parameters: Memo<ChoiceId<'g>, Parameter>,
    pub(crate) parameter_choice_values:
        Memo<(ChoiceId<'g>, Option<ExprId<'g>>), Option<ChoiceId<'g>>>,
    flows: Intern<FlowId<'g>, Flow<'g>>,
    alternatives: Intern<AlternativeId<'g>, Alternative<'g>>,
    flow_members: Sets<'g, FlowId<'g>>,
    flow_joins: Memo<(FlowId<'g>, FlowId<'g>), FlowId<'g>>,
    pub input_sets: Sets<'g, usize>,
    pub function_sets: Sets<'g, DefId>,
    pub(crate) input_summaries: Memo<(InputUse, NodeId<'g>), Inputs<'g>>,
    pub(crate) function_summaries: Memo<NodeId<'g>, SetId<'g, DefId>>,
    pub(crate) fields: Memo<(ExprId<'g>, usize), ExprId<'g>>,
    pub(crate) joins: Memo<(ExprId<'g>, ExprId<'g>, Join), ExprId<'g>>,
    pub(crate) parameters: Memo<ExprId<'g>, Parameter>,
    pub(crate) parameter_values: Memo<(ExprId<'g>, Option<ExprId<'g>>), ExprId<'g>>,
    pub(crate) truths: Memo<Query<'g>, evidence::Proof<'g>>,
    pub(crate) comparisons: Comparisons<'g>,
    pub(crate) guard_projections:
        Memo<(GuardContextId<'g>, SetId<'g, NodeId<'g>>), GuardContextId<'g>>,
    pub(crate) guard_projection_summaries:
        sequence::Fold<'g, operations::GuardSegment<'g>, operations::GuardProjectionSummary<'g>>,
    pub(crate) guard_projection_filters:
        sequence::TransformCache<'g, operations::GuardSegment<'g>, SetId<'g, NodeId<'g>>>,
    pub(crate) guard_projection_conditions:
        sequence::Fold<'g, operations::GuardSegment<'g>, Sequence<'g, ConditionId<'g>>>,
    pub(crate) projected_guards: Memo<(ConditionId<'g>, GuardContextId<'g>), GuardContextId<'g>>,
    pub(crate) prepared_guards: Memo<GuardContextId<'g>, operations::PreparedGuards<'g>>,
    pub(crate) guard_members: sequence::Fold<'g, ConditionId<'g>, SetId<'g, ConditionId<'g>>>,
    pub(crate) guard_member_sets: Sets<'g, ConditionId<'g>>,
    pub(crate) guard_intersections:
        sequence::TransformCache<'g, ConditionId<'g>, SetId<'g, ConditionId<'g>>>,
    pub(crate) evidence_sequences:
        Memo<SetId<'g, ConditionId<'g>>, sequence::Sequence<'g, ConditionId<'g>>>,
    pub(crate) guard_endpoints: sequence::Fold<'g, ConditionId<'g>, operations::GuardEndpoints<'g>>,
    pub(crate) guard_classifications:
        sequence::Fold<'g, ConditionId<'g>, operations::GuardClassification<'g>>,
    pub(crate) rewritten_expressions: Memo<(RewriteId<'g>, ExprId<'g>), ExprId<'g>>,
    pub(crate) rewritten_conditions: Memo<(RewriteId<'g>, ConditionId<'g>), ConditionId<'g>>,
    pub(crate) rewritten_guard_sequences: sequence::Remap<'g, ConditionId<'g>, RewriteId<'g>>,
    pub(crate) rewritten_argument_sequences: sequence::Remap<'g, ExprId<'g>, RewriteId<'g>>,
    pub(crate) rewritten_invalidated_sequences:
        sequence::Remap<'g, crate::contracts::InvalidatedFact<ConditionId<'g>>, RewriteId<'g>>,
    pub(crate) rewrites: Intern<RewriteId<'g>, RewriteKey<'g>>,
    pub condition_sequences: sequence::Sequences<'g, ConditionId<'g>>,
    pub expression_sequences: sequence::Sequences<'g, ExprId<'g>>,
    pub invalidated_sequences:
        sequence::Sequences<'g, crate::contracts::InvalidatedFact<ConditionId<'g>>>,
    pub(crate) guard_segments: sequence::Sequences<'g, operations::GuardSegment<'g>>,
    pub(crate) comparison_edges:
        sequence::Sequences<'g, crate::contracts::graph::comparisons::Edge<'g>>,
    expressions: Intern<ExprId<'g>, Expression<'g>>,
    conditions: Intern<ConditionId<'g>, KnownCondition<'g>>,
}

impl<'g> Graph<'g> {
    pub(crate) fn fork(&self) -> Self {
        // Fold results depend only on canonical sequence nodes and shared graph facts.
        Graph {
            substitution_work: operations::SubstitutionWork::default(),
            argument_projections: self.argument_projections.clone(),
            projected_argument_sequences: self.projected_argument_sequences.share(),
            sequence_input_summaries: self.sequence_input_summaries.clone(),
            proof_work: ProofWork::default(),
            values: self.values.share(),
            summaries: self.summaries.share(),
            flows: self.flows.clone(),
            choices: self.choices.share(),
            choice_fields: self.choice_fields.clone(),
            widened_choices: self.widened_choices.clone(),
            rewritten_choices: self.rewritten_choices.clone(),
            choice_parameters: self.choice_parameters.clone(),
            parameter_choice_values: self.parameter_choice_values.clone(),
            alternatives: self.alternatives.clone(),
            flow_members: self.flow_members.share(),
            flow_joins: self.flow_joins.clone(),
            input_sets: self.input_sets.share(),
            function_sets: self.function_sets.share(),
            input_summaries: self.input_summaries.clone(),
            function_summaries: self.function_summaries.clone(),
            fields: self.fields.clone(),
            joins: self.joins.clone(),
            parameters: self.parameters.clone(),
            parameter_values: self.parameter_values.clone(),
            expressions: self.expressions.clone(),
            conditions: self.conditions.clone(),
            truths: self.truths.clone(),
            comparisons: self.comparisons.share(),
            projected_guards: self.projected_guards.clone(),
            prepared_guards: self.prepared_guards.clone(),
            guard_projections: self.guard_projections.clone(),
            guard_projection_summaries: self.guard_projection_summaries.share(),
            guard_projection_filters: self.guard_projection_filters.share(),
            guard_projection_conditions: self.guard_projection_conditions.share(),
            guard_endpoints: self.guard_endpoints.share(),
            guard_members: self.guard_members.share(),
            guard_intersections: self.guard_intersections.share(),
            guard_member_sets: self.guard_member_sets.share(),
            evidence_sequences: self.evidence_sequences.clone(),
            guard_classifications: self.guard_classifications.share(),
            reference_summaries: self.reference_summaries.clone(),
            reference_sets: self.reference_sets.share(),
            conjunctions: self.conjunctions.clone(),
            condition_sequences: self.condition_sequences.share(),
            expression_sequences: self.expression_sequences.share(),
            invalidated_sequences: self.invalidated_sequences.share(),
            guard_segments: self.guard_segments.share(),
            comparison_edges: self.comparison_edges.share(),
            rewrites: self.rewrites.clone(),
            rewritten_expressions: self.rewritten_expressions.clone(),
            rewritten_conditions: self.rewritten_conditions.clone(),
            rewritten_guard_sequences: self.rewritten_guard_sequences.share(),
            rewritten_argument_sequences: self.rewritten_argument_sequences.share(),
            rewritten_invalidated_sequences: self.rewritten_invalidated_sequences.share(),
        }
    }

    pub fn known(&self, node: NodeId<'g>) -> Option<()> {
        match node {
            NodeId::Choice(_) => None,
            NodeId::Expr(id) => self.expressions.get(id).known,
            NodeId::Condition(id) => self.conditions.get(id).known,
        }
    }

    // shapelint: allow(shallow-helper) Read-only access keeps canonical graph storage private.
    pub fn expressions(&self) -> impl Iterator<Item = &ExprNode<'g>> {
        self.expressions.iter().map(|entry| &entry.node)
    }

    // shapelint: allow(shallow-helper) Read-only access keeps canonical graph storage private.
    pub fn expression_count(&self) -> usize {
        self.expressions.len()
    }

    // shapelint: allow(shallow-helper) Read-only access keeps canonical graph storage private.
    pub fn condition_count(&self) -> usize {
        self.conditions.len()
    }

    // shapelint: allow(shallow-helper) Read-only access keeps canonical graph storage private.
    pub fn flows(&self) -> impl Iterator<Item = &Flow<'g>> {
        self.flows.iter()
    }

    // shapelint: allow(shallow-helper) Read-only access keeps canonical graph storage private.
    pub fn flow_alternatives(&self) -> impl Iterator<Item = &Alternative<'g>> {
        self.alternatives.iter()
    }

    pub fn freeze(
        &mut self,
        summary: crate::contracts::Summary<
            'g,
            ExprId<'g>,
            ConditionId<'g>,
            TargetNode<'g>,
            FlowId<'g>,
        >,
    ) -> Result<summaries::SummaryId<'g>, CapacityError> {
        self.summaries.freeze(
            &mut self.values,
            &mut self.function_sets,
            &mut self.input_sets,
            &mut self.expression_sequences,
            summary,
        )
    }
}

impl<'g> std::ops::Index<FlowId<'g>> for Graph<'g> {
    type Output = Flow<'g>;
    fn index(&self, id: FlowId<'g>) -> &Self::Output {
        self.flows.get(id)
    }
}

impl<'g> std::ops::Index<AlternativeId<'g>> for Graph<'g> {
    type Output = Alternative<'g>;
    fn index(&self, id: AlternativeId<'g>) -> &Self::Output {
        self.alternatives.get(id)
    }
}

impl<'g> std::ops::Index<ExprId<'g>> for Graph<'g> {
    type Output = ExprNode<'g>;
    fn index(&self, id: ExprId<'g>) -> &Self::Output {
        &self.expressions.get(id).node
    }
}
impl<'g> std::ops::Index<ConditionId<'g>> for Graph<'g> {
    type Output = ConditionNode<'g>;
    fn index(&self, id: ConditionId<'g>) -> &Self::Output {
        &self.conditions.get(id).node
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ExpressionKey<'g> {
    Alternatives(SetId<'g, ExprId<'g>>),
    Node(ExprNode<'g>),
}

struct Expression<'g> {
    key: ExpressionKey<'g>,
    node: ExprNode<'g>,
    known: Option<()>,
}

impl PartialEq for Expression<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}
impl Eq for Expression<'_> {}
impl Hash for Expression<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.key.hash(state);
    }
}

struct KnownCondition<'g> {
    node: ConditionNode<'g>,
    known: Option<()>,
}
impl PartialEq for KnownCondition<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.node == other.node
    }
}
impl Eq for KnownCondition<'_> {}
impl Hash for KnownCondition<'_> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.node.hash(state);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TargetNode<'g> {
    Direct(InstanceId<'g>),
    Indirect(ExprId<'g>),
}

impl<'g> TargetNode<'g> {
    fn visit_call(
        self,
        arguments: Sequence<'g, ExprId<'g>>,
        sequences: &sequence::Sequences<'g, ExprId<'g>>,
        mut visit: impl FnMut(NodeId<'g>),
    ) {
        if let Self::Indirect(value) = self {
            visit(NodeId::Expr(value));
        }
        for &argument in sequences.iter(arguments) {
            visit(NodeId::Expr(argument));
        }
    }

    pub fn definition(
        &self,
        values: &impl std::ops::Index<InstanceId<'g>, Output = values::InstanceNode<'g>>,
    ) -> Option<DefId> {
        match self {
            Self::Direct(instance) => {
                let instance = values[*instance];
                match instance.dispatch {
                    values::Dispatch::Item => Some(instance.def),
                    values::Dispatch::Virtual
                    | values::Dispatch::Shim
                    | values::Dispatch::Unresolved => None,
                }
            }
            Self::Indirect(_) => None,
        }
    }
}

pub type TextMatchNode<'g> = TextMatch<ExprId<'g>>;
pub type TokenNode<'g> = Token<ExprId<'g>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ExprNode<'g> {
    Serialized {
        value: ExprId<'g>,
        def: DefId,
        span: Span,
        encoding: Encoding,
        ty: Fingerprint,
    },
    Unknown,
    Function(InstanceId<'g>),
    Typed(TypeId<'g>, ExprId<'g>),
    Alternatives(Option<ChoiceId<'g>>),
    Select(ConditionId<'g>, ExprId<'g>, ExprId<'g>),
    Opaque(OriginId<'g>),
    Global(InstanceId<'g>),
    Argument(usize),
    Number(u128),
    Range(Interval),
    Text(TextId<'g>),
    Field(ExprId<'g>, usize),
    Element(ExprId<'g>, ExprId<'g>),
    Closure(DefId, Sequence<'g, ExprId<'g>>),
    Aggregate(Sequence<'g, ExprId<'g>>),
    Variant(DefId, usize, Sequence<'g, ExprId<'g>>),
    Length(ExprId<'g>),
    Trimmed(ExprId<'g>),
    Found {
        text: ExprId<'g>,
        pattern: ExprId<'g>,
    },
    MatchIndex {
        text: ExprId<'g>,
        pattern: ExprId<'g>,
        occurrence: ExprId<'g>,
    },
    Matches {
        text: ExprId<'g>,
        pattern: ExprId<'g>,
    },
    MatchEntry(TextMatchNode<'g>),
    Tokens {
        text: ExprId<'g>,
        consumed: ExprId<'g>,
    },
    Token(TokenNode<'g>),
    NextToken(TokenNode<'g>),
    Cursor {
        def: DefId,
        local: Local,
    },
    Partition {
        sequence: ExprId<'g>,
        predicate: ExprId<'g>,
    },
    Slice {
        text: ExprId<'g>,
        start: ExprId<'g>,
        end: ExprId<'g>,
    },
    Arithmetic(Arithmetic, ExprId<'g>, ExprId<'g>),
    Call(
        TargetNode<'g>,
        Sequence<'g, ExprId<'g>>,
        Option<OriginId<'g>>,
    ),
    Test(ConditionId<'g>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ConditionNode<'g> {
    Unknown,
    Compare(Order, ExprId<'g>, ExprId<'g>),
    Boundary(ExprId<'g>, ExprId<'g>),
    NotBoundary(ExprId<'g>, ExprId<'g>),
    Variant(ExprId<'g>, usize),
    NotVariant(ExprId<'g>, usize),
    Returned(TargetNode<'g>, Sequence<'g, ExprId<'g>>),
}

enum Lower<'a> {
    Visit(Input<'a>),
    Expr(&'a Expr),
    Condition(&'a Condition),
}

impl<'g> Graph<'g> {
    pub fn conjunction(
        &mut self,
        conditions: &Sequence<'g, ConditionId<'g>>,
        guards: &Sequence<'g, ConditionId<'g>>,
    ) -> Result<Truth, CapacityError> {
        self.proof_work.conjunction_queries = self.proof_work.conjunction_queries.saturating_add(1);
        self.conjunction_fragment(*conditions, *guards)
    }

    fn conjunction_fragment(
        &mut self,
        conditions: Sequence<'g, ConditionId<'g>>,
        guards: Sequence<'g, ConditionId<'g>>,
    ) -> Result<Truth, CapacityError> {
        let key = (conditions, guards);
        if let Some(result) = self.conjunctions.get(&key) {
            self.proof_work.conjunction_cache_hits =
                self.proof_work.conjunction_cache_hits.saturating_add(1);
            return Ok(result);
        }
        let result = match self.condition_sequences.parts(conditions)? {
            sequence::Parts::Empty => Truth::Proven,
            sequence::Parts::Leaf(condition) => {
                self.proof_work.conjunction_condition_visits = self
                    .proof_work
                    .conjunction_condition_visits
                    .saturating_add(1);
                self.truth(condition, &guards)?
            }
            sequence::Parts::Branch(left, right) => {
                let left = self.conjunction_fragment(left, guards)?;
                match left {
                    Truth::Refuted => Truth::Refuted,
                    Truth::Proven => self.conjunction_fragment(right, guards)?,
                    Truth::Unknown(reason) => match self.conjunction_fragment(right, guards)? {
                        Truth::Refuted => Truth::Refuted,
                        Truth::Proven => Truth::Unknown(reason),
                        unknown @ Truth::Unknown(_) => unknown,
                    },
                }
            }
        };
        if let None = self.conjunctions.insert(key, result) {
            self.proof_work.conjunction_cache_entries =
                self.proof_work.conjunction_cache_entries.saturating_add(1);
        }
        Ok(result)
    }

    pub(crate) fn guard_prefix(
        &mut self,
        context: GuardContextId<'g>,
    ) -> Result<Option<(GuardContextId<'g>, ConditionId<'g>)>, CapacityError> {
        Ok(self
            .condition_sequences
            .prefix(context.0)?
            .map(|(prefix, condition)| (GuardContextId(prefix), condition)))
    }

    /// Treats alternatives as a set, retaining the first interned member order.
    /// Collapses equal selection branches, recognizes Boolean tests, and normalizes comparisons.
    pub fn intern_expr(&mut self, mut node: ExprNode<'g>) -> Result<ExprId<'g>, CapacityError> {
        if let ExprNode::Select(condition, yes, no) = node {
            if yes == no {
                return Ok(yes);
            }
            node = match (&self[yes], &self[no]) {
                (ExprNode::Number(1), ExprNode::Number(0)) => ExprNode::Test(condition),
                (ExprNode::Number(0), ExprNode::Number(1)) => {
                    let negated = self.negate(condition)?;
                    match self[negated] {
                        // A return guard has no representable negation. Keep its call identity.
                        ConditionNode::Unknown if negated != condition => node,
                        _ => ExprNode::Test(negated),
                    }
                }
                _ => match self[condition] {
                    ConditionNode::Compare(Order::LessEqual | Order::NotEqual, ..) => {
                        ExprNode::Select(self.negate(condition)?, no, yes)
                    }
                    _ => ExprNode::Select(condition, yes, no),
                },
            };
        }

        let members = match &node {
            ExprNode::Alternatives(Some(root)) => {
                if let ChoiceNode::Value(value) = self[*root].node {
                    return Ok(value);
                }
                Some(self[*root].members)
            }
            ExprNode::Alternatives(None) => Some(SetId::EMPTY),
            _ => None,
        };
        let key = match members {
            Some(members) => ExpressionKey::Alternatives(members),
            None => ExpressionKey::Node(node),
        };
        let known = match &node {
            ExprNode::Global(_)
            | ExprNode::Alternatives(_)
            | ExprNode::Serialized { .. }
            | ExprNode::Unknown
            | ExprNode::Call(..)
            | ExprNode::Range(_) => None,
            ExprNode::Opaque(origin) => self.values[*origin].identity.map(|_| ()),
            _ => {
                let mut known = Some(());
                node.visit_children(&self.expression_sequences, |child| {
                    known = known.and(self.known(child));
                });
                known
            }
        };
        self.expressions
            .intern(Expression { key, node, known }, CapacityError::Expressions)
    }

    pub fn intern_condition(
        &mut self,
        node: ConditionNode<'g>,
    ) -> Result<ConditionId<'g>, CapacityError> {
        let known = match &node {
            ConditionNode::Unknown => None,
            ConditionNode::Returned(..) => Some(()),
            _ => {
                let mut known = Some(());
                node.visit_children(&self.expression_sequences, |child| {
                    known = known.and(self.known(child));
                });
                known
            }
        };
        self.conditions
            .intern(KnownCondition { node, known }, CapacityError::Conditions)
    }

    pub fn lower_expr(&mut self, expression: &Expr) -> Result<ExprId<'g>, CapacityError> {
        let (expressions, _) = self.lower(Input::Expr(expression))?;
        Ok(expressions[&(expression as *const Expr)])
    }
    pub fn lower_condition(
        &mut self,
        condition: &Condition,
    ) -> Result<ConditionId<'g>, CapacityError> {
        let (_, conditions) = self.lower(Input::Condition(condition))?;
        Ok(conditions[&(condition as *const Condition)])
    }

    fn lower(
        &mut self,
        input: Input<'_>,
    ) -> Result<
        (
            FxHashMap<*const Expr, ExprId<'g>>,
            FxHashMap<*const Condition, ConditionId<'g>>,
        ),
        CapacityError,
    > {
        let mut expressions = FxHashMap::default();
        let mut conditions = FxHashMap::default();
        let mut pending = vec![Lower::Visit(input)];
        while let Some(work) = pending.pop() {
            match work {
                Lower::Visit(Input::Expr(expression)) => {
                    pending.push(Lower::Expr(expression));
                    pending.extend(expression.children().into_iter().rev().map(Lower::Visit));
                }
                Lower::Visit(Input::Condition(condition)) => {
                    pending.push(Lower::Condition(condition));
                    pending.extend(condition.children().into_iter().rev().map(Lower::Visit));
                }
                Lower::Expr(expression) => {
                    let expr = |expression: &Expr| expressions[&(expression as *const Expr)];
                    let condition_id =
                        |condition: &Condition| conditions[&(condition as *const Condition)];
                    let node = match expression {
                        Expr::Serialized(value) => ExprNode::Serialized {
                            value: expr(&value.value),
                            def: value.def,
                            span: value.span,
                            encoding: value.encoding,
                            ty: value.ty,
                        },
                        Expr::Unknown => ExprNode::Unknown,
                        Expr::Function(instance) => {
                            ExprNode::Function(self.values.intern_instance(instance)?)
                        }
                        Expr::Typed(ty, value) => {
                            ExprNode::Typed(self.values.intern_type(ty)?, expr(value))
                        }
                        Expr::Alternatives(values) => {
                            let id = self.alternatives(values.iter().map(expr))?;
                            expressions.insert(expression as *const Expr, id);
                            continue;
                        }
                        Expr::Select(condition, yes, no) => {
                            ExprNode::Select(condition_id(condition), expr(yes), expr(no))
                        }
                        Expr::Opaque(origin) => {
                            ExprNode::Opaque(self.values.intern_origin(origin)?)
                        }
                        Expr::Global(instance) => {
                            ExprNode::Global(self.values.intern_instance(instance)?)
                        }
                        Expr::Argument(index) => ExprNode::Argument(*index),
                        Expr::Number(value) => ExprNode::Number(*value),
                        Expr::Range(interval) => ExprNode::Range(interval.clone()),
                        Expr::Text(text) => ExprNode::Text(self.values.intern_text(text)?),
                        Expr::Field(value, field) => ExprNode::Field(expr(value), *field),
                        Expr::Element(value, index) => ExprNode::Element(expr(value), expr(index)),
                        Expr::Closure(def, values) => ExprNode::Closure(
                            *def,
                            self.expression_sequences
                                .from_iter(values.iter().map(expr))?,
                        ),
                        Expr::Aggregate(values) => ExprNode::Aggregate(
                            self.expression_sequences
                                .from_iter(values.iter().map(expr))?,
                        ),
                        Expr::Variant(def, variant, values) => ExprNode::Variant(
                            *def,
                            *variant,
                            self.expression_sequences
                                .from_iter(values.iter().map(expr))?,
                        ),
                        Expr::Length(value) => ExprNode::Length(expr(value)),
                        Expr::Trimmed(value) => ExprNode::Trimmed(expr(value)),
                        Expr::Found { text, pattern } => ExprNode::Found {
                            text: expr(text),
                            pattern: expr(pattern),
                        },
                        Expr::MatchIndex {
                            text,
                            pattern,
                            occurrence,
                        } => ExprNode::MatchIndex {
                            text: expr(text),
                            pattern: expr(pattern),
                            occurrence: expr(occurrence),
                        },
                        Expr::Matches { text, pattern } => ExprNode::Matches {
                            text: expr(text),
                            pattern: expr(pattern),
                        },
                        Expr::MatchEntry(value) => ExprNode::MatchEntry(TextMatchNode {
                            text: expr(&value.text),
                            pattern: expr(&value.pattern),
                            occurrence: expr(&value.occurrence),
                        }),
                        Expr::Tokens { text, consumed } => ExprNode::Tokens {
                            text: expr(text),
                            consumed: expr(consumed),
                        },
                        Expr::Token(value) => ExprNode::Token(TokenNode {
                            text: expr(&value.text),
                            start: expr(&value.start),
                            length: expr(&value.length),
                        }),
                        Expr::NextToken(value) => ExprNode::NextToken(TokenNode {
                            text: expr(&value.text),
                            start: expr(&value.start),
                            length: expr(&value.length),
                        }),
                        Expr::Cursor { def, local } => ExprNode::Cursor {
                            def: *def,
                            local: *local,
                        },
                        Expr::Partition {
                            sequence,
                            predicate,
                        } => ExprNode::Partition {
                            sequence: expr(sequence),
                            predicate: expr(predicate),
                        },
                        Expr::Slice { text, start, end } => ExprNode::Slice {
                            text: expr(text),
                            start: expr(start),
                            end: expr(end),
                        },
                        Expr::Arithmetic(operation, left, right) => {
                            ExprNode::Arithmetic(*operation, expr(left), expr(right))
                        }
                        Expr::Call(target, arguments, origin) => ExprNode::Call(
                            lower_target(&mut self.values, target, &expr)?,
                            self.expression_sequences
                                .from_iter(arguments.iter().map(expr))?,
                            origin
                                .as_ref()
                                .map(|origin| self.values.intern_origin(origin))
                                .transpose()?,
                        ),
                        Expr::Test(condition) => ExprNode::Test(condition_id(condition)),
                    };
                    let id = self.intern_expr(node)?;
                    expressions.insert(expression as *const Expr, id);
                }
                Lower::Condition(value) => {
                    let expr = |expression: &Expr| expressions[&(expression as *const Expr)];
                    let node = match value {
                        Condition::Unknown => ConditionNode::Unknown,
                        Condition::Compare(order, left, right) => {
                            ConditionNode::Compare(*order, expr(left), expr(right))
                        }
                        Condition::Boundary(text, offset) => {
                            ConditionNode::Boundary(expr(text), expr(offset))
                        }
                        Condition::NotBoundary(text, offset) => {
                            ConditionNode::NotBoundary(expr(text), expr(offset))
                        }
                        Condition::Variant(value, variant) => {
                            ConditionNode::Variant(expr(value), *variant)
                        }
                        Condition::NotVariant(value, variant) => {
                            ConditionNode::NotVariant(expr(value), *variant)
                        }
                        Condition::Returned(target, arguments) => ConditionNode::Returned(
                            lower_target(&mut self.values, target, &expr)?,
                            self.expression_sequences
                                .from_iter(arguments.iter().map(expr))?,
                        ),
                    };
                    let id = self.intern_condition(node)?;
                    conditions.insert(value as *const Condition, id);
                }
            }
        }
        Ok((expressions, conditions))
    }

    pub fn raise_expr(&self, expression: ExprId<'g>) -> Expr {
        match self.raise(Root::Expr(expression)) {
            Output::Expr(value) => value,
            Output::Condition(_) => unreachable!("expression root"),
        }
    }
    pub fn raise_condition(&self, condition: ConditionId<'g>) -> Condition {
        match self.raise(Root::Condition(condition)) {
            Output::Condition(value) => value,
            Output::Expr(_) => unreachable!("condition root"),
        }
    }

    fn raise(&self, root: Root<ExprId<'g>, ConditionId<'g>>) -> Output {
        root.build(
            |id| match self[id] {
                ExprNode::Serialized {
                    value,
                    def,
                    span,
                    encoding,
                    ty,
                } => ExprBuild::One(Unary::Serialized(def, span, encoding, ty), value),
                ExprNode::Unknown => ExprBuild::Value(Leaf::Unknown),
                ExprNode::Function(value) => {
                    ExprBuild::Value(Leaf::Function(self.values.export_instance(value)))
                }
                ExprNode::Global(value) => {
                    ExprBuild::Value(Leaf::Global(self.values.export_instance(value)))
                }
                ExprNode::Opaque(value) => {
                    ExprBuild::Value(Leaf::Opaque(self.values.export_origin(value)))
                }
                ExprNode::Argument(value) => ExprBuild::Value(Leaf::Argument(value)),
                ExprNode::Number(value) => ExprBuild::Value(Leaf::Number(value)),
                ExprNode::Range(value) => ExprBuild::Value(Leaf::Range(value)),
                ExprNode::Text(value) => {
                    ExprBuild::Value(Leaf::Text(self.values[value].to_owned()))
                }
                ExprNode::Cursor { def, local } => ExprBuild::Value(Leaf::Cursor { def, local }),
                ExprNode::Typed(ty, value) => {
                    ExprBuild::One(Unary::Typed(self.values.export_type(ty)), value)
                }
                ExprNode::Field(value, field) => ExprBuild::One(Unary::Field(field), value),
                ExprNode::Length(value) => ExprBuild::One(Unary::Length, value),
                ExprNode::Trimmed(value) => ExprBuild::One(Unary::Trimmed, value),
                ExprNode::Element(left, right) => ExprBuild::Two(Binary::Element, left, right),
                ExprNode::Found { text, pattern } => ExprBuild::Two(Binary::Found, text, pattern),
                ExprNode::Matches { text, pattern } => {
                    ExprBuild::Two(Binary::Matches, text, pattern)
                }
                ExprNode::Partition {
                    sequence,
                    predicate,
                } => ExprBuild::Two(Binary::Partition, sequence, predicate),
                ExprNode::Tokens { text, consumed } => {
                    ExprBuild::Two(Binary::Tokens, text, consumed)
                }
                ExprNode::Arithmetic(op, left, right) => {
                    ExprBuild::Two(Binary::Arithmetic(op), left, right)
                }
                ExprNode::MatchIndex {
                    text,
                    pattern,
                    occurrence,
                } => ExprBuild::Three(Ternary::MatchIndex, text, pattern, occurrence),
                ExprNode::MatchEntry(value) => ExprBuild::MatchEntry(value),
                ExprNode::Slice { text, start, end } => {
                    ExprBuild::Three(Ternary::Slice, text, start, end)
                }
                ExprNode::Token(value) => ExprBuild::Token(value),
                ExprNode::NextToken(value) => ExprBuild::NextToken(value),
                ExprNode::Select(guard, yes, no) => ExprBuild::Select(guard, yes, no),
                ExprNode::Test(condition) => ExprBuild::Test(condition),
                ExprNode::Aggregate(values) => ExprBuild::List(
                    Collection::Aggregate,
                    self.expression_sequences.iter(values).copied().collect(),
                ),
                ExprNode::Closure(def, values) => ExprBuild::List(
                    Collection::Closure(def),
                    self.expression_sequences.iter(values).copied().collect(),
                ),
                ExprNode::Variant(def, variant, values) => ExprBuild::List(
                    Collection::Variant(def, variant),
                    self.expression_sequences.iter(values).copied().collect(),
                ),
                ExprNode::Alternatives(root) => ExprBuild::List(
                    Collection::Alternatives,
                    root.into_iter()
                        .flat_map(|root| self.expression_sequences.iter(self[root].values).copied())
                        .collect(),
                ),
                ExprNode::Call(target, args, origin) => ExprBuild::Call(
                    self.tree_target(target),
                    self.expression_sequences.iter(args).copied().collect(),
                    origin.map(|origin| self.values.export_origin(origin)),
                ),
            },
            |id| match self[id] {
                ConditionNode::Unknown => ConditionBuild::Unknown,
                ConditionNode::Compare(order, left, right) => {
                    ConditionBuild::Compare(order, left, right)
                }
                ConditionNode::Boundary(left, right) => ConditionBuild::Boundary(left, right),
                ConditionNode::NotBoundary(left, right) => ConditionBuild::NotBoundary(left, right),
                ConditionNode::Variant(value, index) => ConditionBuild::Variant(value, index),
                ConditionNode::NotVariant(value, index) => ConditionBuild::NotVariant(value, index),
                ConditionNode::Returned(target, args) => ConditionBuild::Returned(
                    self.tree_target(target),
                    self.expression_sequences.iter(args).copied().collect(),
                ),
            },
        )
    }

    fn tree_target(&self, target: TargetNode<'g>) -> CallTarget<ExprId<'g>> {
        match target {
            TargetNode::Direct(instance) => {
                CallTarget::Direct(self.values.export_instance(instance))
            }
            TargetNode::Indirect(value) => CallTarget::Indirect(value),
        }
    }
}

fn lower_target<'g>(
    values: &mut Values<'g>,
    target: &Target,
    expr: &impl Fn(&Expr) -> ExprId<'g>,
) -> Result<TargetNode<'g>, CapacityError> {
    Ok(match target {
        Target::Direct(instance) => TargetNode::Direct(values.intern_instance(instance)?),
        Target::Indirect(value) => TargetNode::Indirect(expr(value)),
    })
}

impl<'g> ExprNode<'g> {
    fn visit_children(
        &self,
        sequences: &sequence::Sequences<'g, ExprId<'g>>,
        mut visit: impl FnMut(NodeId<'g>),
    ) {
        match self {
            Self::Serialized {
                value,
                def: _,
                span: _,
                encoding: _,
                ty: _,
            } => {
                visit(NodeId::Expr(*value));
            }
            Self::Unknown => {}
            Self::Function(_) => {}
            Self::Typed(_, value) => {
                visit(NodeId::Expr(*value));
            }
            Self::Alternatives(root) => {
                if let Some(root) = root {
                    visit(NodeId::Choice(*root));
                }
            }
            Self::Select(condition, yes, no) => {
                visit(NodeId::Condition(*condition));
                visit(NodeId::Expr(*yes));
                visit(NodeId::Expr(*no));
            }
            Self::Opaque(_) => {}
            Self::Global(_) => {}
            Self::Argument(_) => {}
            Self::Number(_) => {}
            Self::Range(_) => {}
            Self::Text(_) => {}
            Self::Field(value, _) => {
                visit(NodeId::Expr(*value));
            }
            Self::Element(value, index) => {
                visit(NodeId::Expr(*value));
                visit(NodeId::Expr(*index));
            }
            Self::Closure(_, values) | Self::Aggregate(values) | Self::Variant(_, _, values) => {
                for value in sequences.iter(*values) {
                    visit(NodeId::Expr(*value));
                }
            }
            Self::Length(value) => {
                visit(NodeId::Expr(*value));
            }
            Self::Trimmed(value) => {
                visit(NodeId::Expr(*value));
            }
            Self::Found { text, pattern } => {
                visit(NodeId::Expr(*text));
                visit(NodeId::Expr(*pattern));
            }
            Self::MatchIndex {
                text,
                pattern,
                occurrence,
            } => {
                visit(NodeId::Expr(*text));
                visit(NodeId::Expr(*pattern));
                visit(NodeId::Expr(*occurrence));
            }
            Self::Matches { text, pattern } => {
                visit(NodeId::Expr(*text));
                visit(NodeId::Expr(*pattern));
            }
            Self::MatchEntry(value) => {
                visit(NodeId::Expr(value.text));
                visit(NodeId::Expr(value.pattern));
                visit(NodeId::Expr(value.occurrence));
            }
            Self::Tokens { text, consumed } => {
                visit(NodeId::Expr(*text));
                visit(NodeId::Expr(*consumed));
            }
            Self::Token(value) | Self::NextToken(value) => {
                visit(NodeId::Expr(value.text));
                visit(NodeId::Expr(value.start));
                visit(NodeId::Expr(value.length));
            }
            Self::Cursor { def: _, local: _ } => {}
            Self::Partition {
                sequence,
                predicate,
            } => {
                visit(NodeId::Expr(*sequence));
                visit(NodeId::Expr(*predicate));
            }
            Self::Slice { text, start, end } => {
                visit(NodeId::Expr(*text));
                visit(NodeId::Expr(*start));
                visit(NodeId::Expr(*end));
            }
            Self::Arithmetic(_, left, right) => {
                visit(NodeId::Expr(*left));
                visit(NodeId::Expr(*right));
            }
            Self::Call(target, arguments, _) => {
                target.visit_call(*arguments, sequences, visit);
            }
            Self::Test(condition) => {
                visit(NodeId::Condition(*condition));
            }
        }
    }
}

impl<'g> ConditionNode<'g> {
    fn visit_children(
        &self,
        sequences: &sequence::Sequences<'g, ExprId<'g>>,
        mut visit: impl FnMut(NodeId<'g>),
    ) {
        match self {
            Self::Unknown => {}
            Self::Compare(_, left, right) => {
                visit(NodeId::Expr(*left));
                visit(NodeId::Expr(*right));
            }
            Self::Boundary(text, offset) => {
                visit(NodeId::Expr(*text));
                visit(NodeId::Expr(*offset));
            }
            Self::NotBoundary(text, offset) => {
                visit(NodeId::Expr(*text));
                visit(NodeId::Expr(*offset));
            }
            Self::Variant(value, _) | Self::NotVariant(value, _) => {
                visit(NodeId::Expr(*value));
            }
            Self::Returned(target, arguments) => {
                target.visit_call(*arguments, sequences, visit);
            }
        }
    }
}
