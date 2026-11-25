use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;
use rustc_span::Span;

use crate::sequence::Sequence;
use graph::CapacityError;

pub mod graph;
pub use graph::{operations, summaries};
pub(crate) mod tree;
pub use crate::values::{Identity, Invocation, Origin, Relocation};
pub use tree::{Condition, Expr, Input, Serialized, Target};
pub type TextMatch = tree::TextMatch<Box<Expr>>;
pub type Token = tree::Token<Box<Expr>>;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Encoding {
    Value,
    Text,
    Bytes,
}

/// Equal intervals do not establish equal runtime values.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Interval {
    pub lower: u128,
    pub upper: u128,
}

impl std::fmt::Display for Interval {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..={}", self.lower, self.upper)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Join {
    Hull,
    Widen,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Arithmetic {
    Add(ty::UintTy),
    Subtract(ty::UintTy),
    WrappingSubtract(u64),
}

impl std::fmt::Display for Arithmetic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Add(_) => "+",
            Self::Subtract(_) => "-",
            Self::WrappingSubtract(_) => "wrapping_sub",
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Order {
    Less,
    LessEqual,
    Equal,
    NotEqual,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Truth {
    Proven,
    Refuted,
    Unknown(ProofGap),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ProofGap {
    Value,
    Comparison,
    Boundary,
    Variant,
    Return,
}

impl std::fmt::Display for ProofGap {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Value => {
                "At least one value used by this check could not be tracked through the analysis."
            }
            Self::Comparison => {
                "The known bounds and comparisons do not establish this requirement."
            }
            Self::Boundary => {
                "No UTF-8 boundary guarantee was established for this offset in this string."
            }
            Self::Variant => {
                "The analysis has not established which enum variant reaches this operation."
            }
            Self::Return => {
                "The analysis could not establish the called function's return conditions."
            }
        })
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub enum Operation {
    Condition,
    Subtraction {
        left: Option<String>,
        right: Option<String>,
    },
    Unsupported(String),
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Consumer {
    pub def: DefId,
    pub span: Span,
    pub operation: Operation,
}

#[derive(Clone, Eq, Hash)]
pub struct Requirement<'g, C = Condition> {
    pub invalidated: Sequence<'g, InvalidatedFact<C>>,
    pub consumer: Consumer,
    pub condition: C,
    pub guards: Sequence<'g, C>,
    pub span: Span,
}

impl<C: Eq> PartialEq for Requirement<'_, C> {
    fn eq(&self, other: &Self) -> bool {
        self.invalidated == other.invalidated
            && self.consumer == other.consumer
            && self.condition == other.condition
            && self.guards == other.guards
            && self.span == other.span
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct InvalidatedFact<C = Condition> {
    pub condition: C,
    pub def: DefId,
    pub span: Span,
}

#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum Writes<'g> {
    #[default]
    None,
    Arguments(crate::contracts::graph::sets::SetId<'g, usize>),
    Unknown,
}

/// Combines write footprints in the arena that issued their argument-set handles.
pub trait ArgumentUnion<'g> {
    fn union_arguments(
        &mut self,
        left: graph::sets::SetId<'g, usize>,
        right: graph::sets::SetId<'g, usize>,
    ) -> Result<graph::sets::SetId<'g, usize>, CapacityError>;
}

impl<'g> ArgumentUnion<'g> for graph::sets::Sets<'g, usize> {
    fn union_arguments(
        &mut self,
        left: graph::sets::SetId<'g, usize>,
        right: graph::sets::SetId<'g, usize>,
    ) -> Result<graph::sets::SetId<'g, usize>, CapacityError> {
        self.combine(graph::sets::Combination::Union, left, right)
    }
}

impl<'g> Writes<'g> {
    pub fn merge(
        &mut self,
        other: &Self,
        sets: &mut impl ArgumentUnion<'g>,
    ) -> Result<(), CapacityError> {
        match (&mut *self, other) {
            (Self::Unknown, _) | (_, Self::None) => {}
            (_, Self::Unknown) => *self = Self::Unknown,
            (Self::None, Self::Arguments(arguments)) => *self = Self::Arguments(*arguments),
            (Self::Arguments(current), Self::Arguments(other)) => {
                *current = sets.union_arguments(*current, *other)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Default)]
pub enum Behavior {
    #[default]
    Pure,
    Calls(FxHashSet<DefId>),
    Unknown,
}

impl Behavior {
    pub fn merge(&mut self, other: &Self) {
        match (&mut *self, other) {
            (Self::Unknown, _) | (_, Self::Pure) => {}
            (_, Self::Unknown) => *self = Self::Unknown,
            (Self::Pure, Self::Calls(calls)) => *self = Self::Calls(calls.clone()),
            (Self::Calls(current), Self::Calls(other)) => current.extend(other),
        }
    }
}

#[derive(Clone, Copy, Default, PartialEq, Eq, Hash)]
pub enum CheckBasis<S> {
    #[default]
    Expression,
    ControlFlow(S),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Check<'g, C = Condition> {
    pub basis: CheckBasis<Sequence<'g, C>>,
    pub loop_writes: Option<Writes<'g>>,
    pub condition: C,
    pub guards: Sequence<'g, C>,
    pub span: Span,
}

#[derive(Clone, Copy, Eq, Hash)]
pub struct Call<'g, E = Expr, C = Condition, T = Target> {
    pub basis: CheckBasis<Sequence<'g, C>>,
    pub target: T,
    pub arguments: Sequence<'g, E>,
    pub guards: Sequence<'g, C>,
    pub span: Span,
}

impl<E: Eq, C: Eq, T: PartialEq> PartialEq for Call<'_, E, C, T> {
    fn eq(&self, other: &Self) -> bool {
        self.basis == other.basis
            && self.target == other.target
            && self.arguments == other.arguments
            && self.guards == other.guards
            && self.span == other.span
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Return<'g, E = Expr, C = Condition> {
    pub value: E,
    pub guards: Sequence<'g, C>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Construction<'g, E = Expr, C = Condition> {
    pub owner: DefId,
    pub value: E,
    pub guards: Sequence<'g, C>,
}

pub struct Summary<'g, E = Expr, C = Condition, T = Target, F = std::convert::Infallible> {
    pub protocol_checks: Vec<crate::contracts::graph::flows::Obligation<'g, C, F>>,
    pub protocol_returns: Vec<crate::contracts::graph::flows::Return<F>>,
    pub inspections: Vec<E>,
    pub escapes: FxHashSet<DefId>,
    pub escaped_arguments: FxHashSet<usize>,
    pub behavior: Behavior,
    pub loops: Vec<Span>,
    pub checks: Vec<Check<'g, C>>,
    pub requirements: Vec<Requirement<'g, C>>,
    pub calls: Vec<Call<'g, E, C, T>>,
    pub returns: Vec<Return<'g, E, C>>,
    pub constructions: Vec<Construction<'g, E, C>>,
    pub mutations: FxHashSet<DefId>,
    pub output: Option<DefId>,
}

impl<E, C, T, F> Default for Summary<'_, E, C, T, F> {
    fn default() -> Self {
        Self {
            protocol_checks: Vec::new(),
            protocol_returns: Vec::new(),
            inspections: Vec::new(),
            escapes: FxHashSet::default(),
            escaped_arguments: FxHashSet::default(),
            behavior: Behavior::default(),
            loops: Vec::new(),
            checks: Vec::new(),
            requirements: Vec::new(),
            calls: Vec::new(),
            returns: Vec::new(),
            constructions: Vec::new(),
            mutations: FxHashSet::default(),
            output: None,
        }
    }
}

/// Sums work across reporting evaluators, saturating each counter at [`usize::MAX`].
/// Cache sizes count entries retained by each evaluator.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Work {
    /// Counts contextual call expansions for boundary witnesses, including cached callees.
    pub caller_expansions: usize,
    /// Counts plan visits, including visits rejected by traversal deduplication.
    pub requirement_visits: usize,
    /// Counts stage applications, including memoized transformation lookups.
    pub requirement_applications: usize,
    /// Counts transformation query executions rather than cache hits.
    pub requirement_transformations: usize,
    /// Counts distinct obligation/applicability records actually inserted.
    pub requirement_nodes: usize,
    /// Records the final number of interned applicability DAG nodes.
    pub applicability_nodes: usize,
    /// Counts reporting DAG walk frames, including cached or refuted frames.
    pub applicability_visits: usize,
    /// Counts plan IDs scanned while factoring overlapping obligation groups.
    pub requirement_join_visits: usize,
    /// Counts cursor obligations selected for report materialization after demand filtering.
    pub reporting_visits: usize,
    /// Counts executed local leaf classifiers, excluding report-query cache hits.
    pub reporting_classifications: usize,
    /// Counts executed report-demand plan queries, including retries.
    pub reporting_plan_visits: usize,
    /// Counts concrete report occurrences returned after feasibility selection.
    pub reporting_materializations: usize,
    /// Counts check descriptions rendered for selected findings.
    pub descriptions_rendered: usize,
    /// Counts known-input projection cache misses; full-context fallback allocates no projection.
    pub argument_projections: usize,
    /// Counts argument positions read while building sparse projections.
    pub argument_projection_positions: usize,
    /// Counts completed rewrite build frames, including substitution, invalidation, and provenance.
    pub rewritten_nodes: usize,
    /// Counts plan-dependency work frames, including cached frames.
    pub plan_input_visits: usize,
    /// Counts requests to establish conditional-obligation sharing eligibility.
    pub sharing_probes: usize,
    /// Counts sharing probes rejected because condition dependencies are unknown.
    pub sharing_unknown_rejections: usize,
    /// Counts empty-context proof requests performed by sharing probes.
    pub sharing_proof_queries: usize,
    /// Counts distinct applicability Prefix nodes actually interned.
    pub applicability_prefix_nodes: usize,
    /// Counts first-path traversal frames, including cached frames reached during traversal.
    pub applicability_first_visits: usize,
    /// Counts entries retained in the applicability substitution memo.
    pub applicability_substitution_entries: usize,
    /// Counts applicability membership traversal frames, including cached frames.
    pub applicability_membership_visits: usize,
    /// Counts guard-sequence fragment frames in exact-membership folds.
    pub applicability_membership_guard_sequence_visits: usize,
    /// Counts guard-sequence fragment lookups satisfied by the memoized fold.
    pub applicability_membership_guard_sequence_cache_hits: usize,
    /// Counts condition comparisons at uncached applicability guard-sequence leaves.
    pub applicability_membership_guard_leaf_comparisons: usize,
    /// Records cached exact-membership answers for whole guard sequences.
    pub applicability_membership_guard_sequence_entries: usize,
    /// Records cached applicability and exact-condition membership answers.
    pub applicability_membership_entries: usize,
    /// Counts graph input-summary work frames.
    pub input_visits: usize,
    /// Records final requirement dependency-summary cache cardinality.
    pub requirement_input_entries: usize,
    /// Records final plan dependency-summary cache cardinality.
    pub plan_input_entries: usize,
    /// Records final plan-sequence dependency-summary cache cardinality.
    pub plan_sequence_input_entries: usize,
    /// Records final semantic and local-report plan query cache cardinality.
    pub requirement_plan_cache_entries: usize,
    /// Counts used binding positions inspected while transferring plan dependencies.
    pub plan_input_positions: usize,
    /// Counts nodes allocated in the persistent structural report-support DAG.
    pub report_support_nodes: usize,
    /// Counts structural expression and applicability support work visits.
    pub report_support_visits: usize,
    /// Counts condition and applicability support summaries retained in caches.
    pub report_support_entries: usize,
    /// Counts structural support locations retained by report certificates.
    pub report_support_elements: usize,
    /// Counts support-tree work frames for location overlap and containment.
    pub report_support_overlap_visits: usize,
    /// Counts applicability nodes retaining a structural support summary.
    pub report_support_retained: usize,
    /// Counts context and sequence-fragment work frames during report projection.
    pub report_projection_visits: usize,
    /// Counts guard conditions inspected by the no-Proven-path report certificate.
    pub report_path_certificate_guard_visits: usize,
    /// Counts incoming guards inspected while projecting report contexts.
    pub report_projection_guards: usize,
    /// Counts new persistent condition-sequence nodes allocated by report projection.
    pub report_projection_storage: usize,
}

impl std::ops::AddAssign for Work {
    fn add_assign(&mut self, other: Self) {
        *self = Self {
            caller_expansions: self
                .caller_expansions
                .saturating_add(other.caller_expansions),
            requirement_visits: self
                .requirement_visits
                .saturating_add(other.requirement_visits),
            requirement_applications: self
                .requirement_applications
                .saturating_add(other.requirement_applications),
            requirement_transformations: self
                .requirement_transformations
                .saturating_add(other.requirement_transformations),
            requirement_nodes: self
                .requirement_nodes
                .saturating_add(other.requirement_nodes),
            applicability_nodes: self
                .applicability_nodes
                .saturating_add(other.applicability_nodes),
            applicability_visits: self
                .applicability_visits
                .saturating_add(other.applicability_visits),
            requirement_join_visits: self
                .requirement_join_visits
                .saturating_add(other.requirement_join_visits),
            reporting_visits: self.reporting_visits.saturating_add(other.reporting_visits),
            reporting_classifications: self
                .reporting_classifications
                .saturating_add(other.reporting_classifications),
            reporting_plan_visits: self
                .reporting_plan_visits
                .saturating_add(other.reporting_plan_visits),
            reporting_materializations: self
                .reporting_materializations
                .saturating_add(other.reporting_materializations),
            descriptions_rendered: self
                .descriptions_rendered
                .saturating_add(other.descriptions_rendered),
            argument_projections: self
                .argument_projections
                .saturating_add(other.argument_projections),
            argument_projection_positions: self
                .argument_projection_positions
                .saturating_add(other.argument_projection_positions),
            rewritten_nodes: self.rewritten_nodes.saturating_add(other.rewritten_nodes),
            plan_input_visits: self
                .plan_input_visits
                .saturating_add(other.plan_input_visits),
            sharing_probes: self.sharing_probes.saturating_add(other.sharing_probes),
            sharing_unknown_rejections: self
                .sharing_unknown_rejections
                .saturating_add(other.sharing_unknown_rejections),
            sharing_proof_queries: self
                .sharing_proof_queries
                .saturating_add(other.sharing_proof_queries),
            applicability_prefix_nodes: self
                .applicability_prefix_nodes
                .saturating_add(other.applicability_prefix_nodes),
            applicability_first_visits: self
                .applicability_first_visits
                .saturating_add(other.applicability_first_visits),
            applicability_substitution_entries: self
                .applicability_substitution_entries
                .saturating_add(other.applicability_substitution_entries),
            applicability_membership_visits: self
                .applicability_membership_visits
                .saturating_add(other.applicability_membership_visits),
            applicability_membership_guard_sequence_visits: self
                .applicability_membership_guard_sequence_visits
                .saturating_add(other.applicability_membership_guard_sequence_visits),
            applicability_membership_guard_sequence_cache_hits: self
                .applicability_membership_guard_sequence_cache_hits
                .saturating_add(other.applicability_membership_guard_sequence_cache_hits),
            applicability_membership_guard_leaf_comparisons: self
                .applicability_membership_guard_leaf_comparisons
                .saturating_add(other.applicability_membership_guard_leaf_comparisons),
            applicability_membership_guard_sequence_entries: self
                .applicability_membership_guard_sequence_entries
                .saturating_add(other.applicability_membership_guard_sequence_entries),
            applicability_membership_entries: self
                .applicability_membership_entries
                .saturating_add(other.applicability_membership_entries),
            input_visits: self.input_visits.saturating_add(other.input_visits),
            requirement_input_entries: self
                .requirement_input_entries
                .saturating_add(other.requirement_input_entries),
            plan_input_entries: self
                .plan_input_entries
                .saturating_add(other.plan_input_entries),
            plan_sequence_input_entries: self
                .plan_sequence_input_entries
                .saturating_add(other.plan_sequence_input_entries),
            requirement_plan_cache_entries: self
                .requirement_plan_cache_entries
                .saturating_add(other.requirement_plan_cache_entries),
            plan_input_positions: self
                .plan_input_positions
                .saturating_add(other.plan_input_positions),
            report_support_nodes: self
                .report_support_nodes
                .saturating_add(other.report_support_nodes),
            report_support_visits: self
                .report_support_visits
                .saturating_add(other.report_support_visits),
            report_support_entries: self
                .report_support_entries
                .saturating_add(other.report_support_entries),
            report_support_elements: self
                .report_support_elements
                .saturating_add(other.report_support_elements),
            report_support_overlap_visits: self
                .report_support_overlap_visits
                .saturating_add(other.report_support_overlap_visits),
            report_support_retained: self
                .report_support_retained
                .saturating_add(other.report_support_retained),
            report_projection_visits: self
                .report_projection_visits
                .saturating_add(other.report_projection_visits),
            report_path_certificate_guard_visits: self
                .report_path_certificate_guard_visits
                .saturating_add(other.report_path_certificate_guard_visits),
            report_projection_guards: self
                .report_projection_guards
                .saturating_add(other.report_projection_guards),
            report_projection_storage: self
                .report_projection_storage
                .saturating_add(other.report_projection_storage),
        };
    }
}

impl std::fmt::Display for Order {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Less => "<",
            Self::LessEqual => "<=",
            Self::Equal => "==",
            Self::NotEqual => "!=",
        })
    }
}
