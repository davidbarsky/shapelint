//! Canonical completed summaries and their ordered contents.
use crate::arena::{ArenaId, Intern};
use crate::contracts::graph::sets::{SetId, Sets};
use crate::contracts::graph::{CapacityError, ConditionId, ExprId, FlowId, TargetNode};
use crate::contracts::{self, Consumer, Operation};
use crate::sequence::{Sequence, Sequences};
use crate::values::{TextId, Values};
use rustc_hir::def_id::DefId;
use rustc_span::Span;
use std::marker::PhantomData;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SummaryId<'g>(u32, PhantomData<fn(&'g ()) -> &'g ()>);
impl ArenaId for SummaryId<'_> {
    fn from_index(index: u32) -> Self {
        Self(index, PhantomData)
    }
    fn index(self) -> u32 {
        self.0
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ConsumerId<'g>(u32, PhantomData<fn(&'g ()) -> &'g ()>);
impl ArenaId for ConsumerId<'_> {
    fn from_index(index: u32) -> Self {
        Self(index, PhantomData)
    }
    fn index(self) -> u32 {
        self.0
    }
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum OperationNode<'g> {
    Condition,
    Subtraction {
        left: Option<TextId<'g>>,
        right: Option<TextId<'g>>,
    },
    Unsupported(TextId<'g>),
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ConsumerNode<'g> {
    pub def: DefId,
    pub span: Span,
    pub operation: OperationNode<'g>,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct RequirementNode<'g> {
    pub invalidated: Sequence<'g, contracts::InvalidatedFact<ConditionId<'g>>>,
    pub consumer: ConsumerId<'g>,
    pub condition: ConditionId<'g>,
    pub guards: Sequence<'g, ConditionId<'g>>,
    pub span: Span,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum BehaviorNode<'g> {
    Pure,
    Calls(SetId<'g, DefId>),
    Unknown,
}
pub(crate) type CallNode<'g> = contracts::Call<'g, ExprId<'g>, ConditionId<'g>, TargetNode<'g>>;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct SummaryNode<'g> {
    pub protocol_checks:
        Sequence<'g, crate::protocols::Obligation<'g, ConditionId<'g>, FlowId<'g>>>,
    pub protocol_returns: Sequence<'g, crate::protocols::Return<FlowId<'g>>>,
    pub inspections: Sequence<'g, ExprId<'g>>,
    pub escapes: SetId<'g, DefId>,
    pub escaped_arguments: SetId<'g, usize>,
    pub behavior: BehaviorNode<'g>,
    pub loops: Sequence<'g, Span>,
    pub checks: Sequence<'g, contracts::Check<'g, ConditionId<'g>>>,
    pub requirements: Sequence<'g, RequirementNode<'g>>,
    pub calls: Sequence<'g, CallNode<'g>>,
    pub returns: Sequence<'g, contracts::Return<'g, ExprId<'g>, ConditionId<'g>>>,
    pub constructions: Sequence<'g, contracts::Construction<'g, ExprId<'g>, ConditionId<'g>>>,
    pub mutations: SetId<'g, DefId>,
    pub output: Option<DefId>,
}

type Builder<'g> = contracts::Summary<'g, ExprId<'g>, ConditionId<'g>, TargetNode<'g>, FlowId<'g>>;
pub struct Summaries<'g> {
    nodes: Intern<SummaryId<'g>, SummaryNode<'g>>,
    consumers: Intern<ConsumerId<'g>, ConsumerNode<'g>>,
    pub protocol_checks:
        Sequences<'g, crate::protocols::Obligation<'g, ConditionId<'g>, FlowId<'g>>>,
    pub protocol_returns: Sequences<'g, crate::protocols::Return<FlowId<'g>>>,
    pub loops: Sequences<'g, Span>,
    pub checks: Sequences<'g, contracts::Check<'g, ConditionId<'g>>>,
    pub requirements: Sequences<'g, RequirementNode<'g>>,
    pub calls: Sequences<'g, CallNode<'g>>,
    pub returns: Sequences<'g, contracts::Return<'g, ExprId<'g>, ConditionId<'g>>>,
    pub constructions: Sequences<'g, contracts::Construction<'g, ExprId<'g>, ConditionId<'g>>>,
}
impl<'g> std::ops::Index<SummaryId<'g>> for Summaries<'g> {
    type Output = SummaryNode<'g>;
    fn index(&self, id: SummaryId<'g>) -> &Self::Output {
        self.nodes.get(id)
    }
}
impl<'g> std::ops::Index<ConsumerId<'g>> for Summaries<'g> {
    type Output = ConsumerNode<'g>;
    fn index(&self, id: ConsumerId<'g>) -> &Self::Output {
        self.consumers.get(id)
    }
}
impl<'g> Summaries<'g> {
    pub(crate) fn new() -> Self {
        Self {
            nodes: Intern::new(),
            consumers: Intern::new(),
            protocol_checks: Sequences::new(),
            protocol_returns: Sequences::new(),
            loops: Sequences::new(),
            checks: Sequences::new(),
            requirements: Sequences::new(),
            calls: Sequences::new(),
            returns: Sequences::new(),
            constructions: Sequences::new(),
        }
    }
    /// Creates a view that interns into the same canonical summaries.
    pub fn share(&self) -> Self {
        Self {
            nodes: self.nodes.clone(),
            consumers: self.consumers.clone(),
            protocol_checks: self.protocol_checks.share(),
            protocol_returns: self.protocol_returns.share(),
            loops: self.loops.share(),
            checks: self.checks.share(),
            requirements: self.requirements.share(),
            calls: self.calls.share(),
            returns: self.returns.share(),
            constructions: self.constructions.share(),
        }
    }
    pub fn export_consumer(&self, values: &Values<'g>, id: ConsumerId<'g>) -> Consumer {
        let consumer = self[id];
        consumer.export(values)
    }
    // shapelint: allow(shallow-helper) Consumer identities are checked and scoped to this summary store.
    pub(crate) fn intern_consumer(
        &mut self,
        node: ConsumerNode<'g>,
    ) -> Result<ConsumerId<'g>, CapacityError> {
        self.consumers.intern(node, CapacityError::Values)
    }
    pub fn freeze(
        &mut self,
        values: &mut Values<'g>,
        definitions: &mut Sets<'g, DefId>,
        arguments: &mut Sets<'g, usize>,
        expressions: &mut Sequences<'g, ExprId<'g>>,
        summary: Builder<'g>,
    ) -> Result<SummaryId<'g>, CapacityError> {
        let contracts::Summary {
            protocol_checks,
            protocol_returns,
            inspections,
            escapes,
            escaped_arguments,
            behavior,
            loops,
            checks,
            requirements,
            calls,
            returns,
            constructions,
            mutations,
            output,
        } = summary;
        let mut def_set =
            |input: rustc_data_structures::fx::FxHashSet<DefId>| -> Result<_, CapacityError> {
                let mut set = SetId::EMPTY;
                for def in input {
                    set = definitions.insert(set, def)?;
                }
                Ok(set)
            };
        let escapes = def_set(escapes)?;
        let behavior = match behavior {
            contracts::Behavior::Pure => BehaviorNode::Pure,
            contracts::Behavior::Calls(calls) => BehaviorNode::Calls(def_set(calls)?),
            contracts::Behavior::Unknown => BehaviorNode::Unknown,
        };
        let mutations = def_set(mutations)?;
        let mut escaped = SetId::EMPTY;
        for arg in escaped_arguments {
            escaped = arguments.insert(escaped, arg)?;
        }
        let mut mapped = Vec::new();
        for requirement in requirements {
            let Consumer {
                def,
                span,
                operation,
            } = requirement.consumer;
            let operation = match operation {
                Operation::Condition => OperationNode::Condition,
                Operation::Subtraction { left, right } => OperationNode::Subtraction {
                    left: left.as_deref().map(|s| values.intern_text(s)).transpose()?,
                    right: right
                        .as_deref()
                        .map(|s| values.intern_text(s))
                        .transpose()?,
                },
                Operation::Unsupported(s) => OperationNode::Unsupported(values.intern_text(&s)?),
            };
            let consumer = ConsumerNode {
                def,
                span,
                operation,
            };
            let consumer = self.intern_consumer(consumer)?;
            mapped.push(RequirementNode {
                invalidated: requirement.invalidated,
                consumer,
                condition: requirement.condition,
                guards: requirement.guards,
                span: requirement.span,
            });
        }
        let node = SummaryNode {
            protocol_checks: self.protocol_checks.from_iter(protocol_checks)?,
            protocol_returns: self.protocol_returns.from_iter(protocol_returns)?,
            inspections: expressions.from_iter(inspections)?,
            escapes,
            escaped_arguments: escaped,
            behavior,
            loops: self.loops.from_iter(loops)?,
            checks: self.checks.from_iter(checks)?,
            requirements: self.requirements.from_iter(mapped)?,
            calls: self.calls.from_iter(calls)?,
            returns: self.returns.from_iter(returns)?,
            constructions: self.constructions.from_iter(constructions)?,
            mutations,
            output,
        };
        self.nodes.intern(node, CapacityError::Values)
    }
}

impl<'g> ConsumerNode<'g> {
    pub(crate) fn export(
        self,
        values: &impl std::ops::Index<TextId<'g>, Output = str>,
    ) -> Consumer {
        let ConsumerNode {
            def,
            span,
            operation,
        } = self;
        let operation = match operation {
            OperationNode::Condition => Operation::Condition,
            OperationNode::Subtraction { left, right } => Operation::Subtraction {
                left: left.map(|id| values[id].to_owned()),
                right: right.map(|id| values[id].to_owned()),
            },
            OperationNode::Unsupported(id) => Operation::Unsupported(values[id].to_owned()),
        };
        Consumer {
            def,
            span,
            operation,
        }
    }
}
