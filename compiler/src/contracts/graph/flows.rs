use crate::contracts::Join;
use crate::contracts::graph::sets::SetId;
use crate::contracts::graph::{
    Alternative, AlternativeId, CapacityError, ConditionId, FlowId, Graph,
};
use rustc_hir::def_id::DefId;
use rustc_span::{Span, Symbol};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Flow<'g> {
    Incoming,
    Unknown,
    Ready,
    Dirty {
        def: DefId,
        span: Span,
    },
    Call {
        callee: DefId,
        argument: usize,
        input: FlowId<'g>,
    },
    Alternatives(Option<AlternativeId<'g>>),
    Select(ConditionId<'g>, FlowId<'g>, FlowId<'g>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Obligation<'g, C, F> {
    pub name: Symbol,
    pub span: Span,
    pub flow: F,
    pub guards: crate::sequence::Sequence<'g, C>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Return<F> {
    pub name: Symbol,
    pub argument: usize,
    pub flow: F,
}

enum FlowJoin<'g> {
    Stable(FlowId<'g>),
    Widen,
    Select(ConditionId<'g>, FlowId<'g>, FlowId<'g>),
    Alternatives(FlowId<'g>, FlowId<'g>),
}

impl<'g> From<(FlowId<'g>, FlowId<'g>, Join, Option<ConditionId<'g>>)> for FlowJoin<'g> {
    fn from(
        (left, right, join, decision): (FlowId<'g>, FlowId<'g>, Join, Option<ConditionId<'g>>),
    ) -> Self {
        if left == right {
            return Self::Stable(left);
        }
        match (join, decision) {
            (Join::Widen, _) => Self::Widen,
            (Join::Hull, Some(condition)) => Self::Select(condition, left, right),
            (Join::Hull, None) => Self::Alternatives(left, right),
        }
    }
}

impl<'g> Graph<'g> {
    // shapelint: allow(shallow-helper) The graph owns flow identities and their capacity error.
    pub fn intern_flow(&mut self, flow: Flow<'g>) -> Result<FlowId<'g>, CapacityError> {
        self.flows.intern(flow, CapacityError::Flows)
    }

    pub fn intern_alternatives(
        &mut self,
        values: impl IntoIterator<Item = FlowId<'g>>,
    ) -> Result<FlowId<'g>, CapacityError> {
        let mut previous = None;
        for value in values {
            previous = Some(self.intern_alternative(previous, value)?);
        }
        self.intern_flow(Flow::Alternatives(previous))
    }

    pub fn intern_alternative(
        &mut self,
        previous: Option<AlternativeId<'g>>,
        value: FlowId<'g>,
    ) -> Result<AlternativeId<'g>, CapacityError> {
        let members = previous.map(|id| self[id].members).unwrap_or(SetId::EMPTY);
        let members = self.flow_members.insert(members, value)?;
        self.alternatives.intern(
            Alternative {
                previous,
                value,
                members,
            },
            CapacityError::Flows,
        )
    }

    pub fn join_flow(
        &mut self,
        left: FlowId<'g>,
        right: FlowId<'g>,
        join: Join,
        decision: Option<ConditionId<'g>>,
    ) -> Result<FlowId<'g>, CapacityError> {
        let (left, right) = match FlowJoin::from((left, right, join, decision)) {
            FlowJoin::Stable(flow) => return Ok(flow),
            FlowJoin::Widen => return self.intern_flow(Flow::Unknown),
            FlowJoin::Select(condition, left, right) => {
                return self.intern_flow(Flow::Select(condition, left, right));
            }
            FlowJoin::Alternatives(left, right) => (left, right),
        };
        if let Some(result) = self.flow_joins.get(&(left, right)) {
            return Ok(result);
        }
        let mut result = match self[left] {
            Flow::Alternatives(sequence) => sequence,
            Flow::Incoming
            | Flow::Unknown
            | Flow::Ready
            | Flow::Dirty { .. }
            | Flow::Call { .. }
            | Flow::Select(..) => Some(self.intern_alternative(None, left)?),
        };
        let mut current = match self[right] {
            Flow::Alternatives(sequence) => sequence,
            Flow::Incoming
            | Flow::Unknown
            | Flow::Ready
            | Flow::Dirty { .. }
            | Flow::Call { .. }
            | Flow::Select(..) => Some(self.intern_alternative(None, right)?),
        };
        let mut suffix = Vec::new();
        while let Some(id) = current {
            self.proof_work.flow_join_steps = self.proof_work.flow_join_steps.saturating_add(1);
            if let Some(result) = result {
                let (left, right) = (self[id].members, self[result].members);
                if let Some(()) = self.flow_members.subset(left, right) {
                    break;
                }
            }
            let Alternative {
                previous,
                value,
                members: _,
            } = self[id];
            suffix.push(value);
            current = previous;
        }
        let suffix = suffix.into_iter().rev();
        for value in suffix {
            if let Some(id) = result {
                if let Some(()) = self.flow_members.contains(self[id].members, value) {
                    continue;
                }
            }
            result = Some(self.intern_alternative(result, value)?);
        }
        let result = self.intern_flow(Flow::Alternatives(result))?;
        self.flow_joins.insert((left, right), result);
        Ok(result)
    }
}
