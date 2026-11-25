//! Resolves branded sequence handles to their canonical contract storage.

use std::hash::Hash;

use rustc_span::Span;

use crate::contracts::{
    self,
    graph::{ConditionId, ExprId, FlowId, Graph, summaries},
};
use crate::sequence::{self, Cursor, Sequence, Sequences};

macro_rules! graph_sequence {
    ($item:ty, $field:ident) => {
        impl<'g> AsRef<Sequences<'g, $item>> for Graph<'g> {
            fn as_ref(&self) -> &Sequences<'g, $item> {
                &self.$field
            }
        }
        impl<'g> AsMut<Sequences<'g, $item>> for Graph<'g> {
            fn as_mut(&mut self) -> &mut Sequences<'g, $item> {
                &mut self.$field
            }
        }
    };
}

graph_sequence!(ExprId<'g>, expression_sequences);
graph_sequence!(ConditionId<'g>, condition_sequences);
graph_sequence!(
    contracts::InvalidatedFact<ConditionId<'g>>,
    invalidated_sequences
);

macro_rules! summary_sequence {
    ($item:ty, $field:ident) => {
        impl<'g> AsRef<Sequences<'g, $item>> for summaries::Summaries<'g> {
            fn as_ref(&self) -> &Sequences<'g, $item> {
                &self.$field
            }
        }
        impl<'g> AsRef<Sequences<'g, $item>> for Graph<'g> {
            fn as_ref(&self) -> &Sequences<'g, $item> {
                self.summaries.as_ref()
            }
        }
    };
}

summary_sequence!(
    crate::contracts::graph::flows::Obligation<'g, ConditionId<'g>, FlowId<'g>>,
    protocol_checks
);
summary_sequence!(
    crate::contracts::graph::flows::Return<FlowId<'g>>,
    protocol_returns
);
summary_sequence!(Span, loops);
summary_sequence!(contracts::Check<'g, ConditionId<'g>>, checks);
summary_sequence!(summaries::RequirementNode<'g>, requirements);
summary_sequence!(summaries::CallNode<'g>, calls);
summary_sequence!(contracts::Return<'g, ExprId<'g>, ConditionId<'g>>, returns);
summary_sequence!(
    contracts::Construction<'g, ExprId<'g>, ConditionId<'g>>,
    constructions
);

impl<'g> AsMut<Sequences<'g, summaries::CallNode<'g>>> for summaries::Summaries<'g> {
    fn as_mut(&mut self) -> &mut Sequences<'g, summaries::CallNode<'g>> {
        &mut self.calls
    }
}

impl<'g> AsMut<Sequences<'g, summaries::CallNode<'g>>> for Graph<'g> {
    fn as_mut(&mut self) -> &mut Sequences<'g, summaries::CallNode<'g>> {
        self.summaries.as_mut()
    }
}

impl<'g> Graph<'g> {
    pub fn items<T>(&self, sequence: Sequence<'g, T>) -> sequence::Iter<'_, T>
    where
        Self: AsRef<Sequences<'g, T>>,
    {
        let arena = self.as_ref();
        arena.iter(sequence)
    }

    /// Keeps the sequence readable while the graph interns other nodes.
    pub fn scan<T: Copy>(&self, sequence: Sequence<'g, T>) -> impl Iterator<Item = T> + use<'g, T>
    where
        Self: AsRef<Sequences<'g, T>>,
    {
        let arena = self.as_ref().share();
        let mut cursor = Cursor::from((&arena, sequence));
        std::iter::from_fn(move || cursor.next(&arena).copied())
    }

    pub fn push<T: Clone + Eq + Hash>(
        &mut self,
        sequence: Sequence<'g, T>,
        value: T,
    ) -> Result<Sequence<'g, T>, crate::arena::CapacityError>
    where
        Self: AsMut<Sequences<'g, T>>,
    {
        let arena = self.as_mut();
        arena.push(sequence, value)
    }

    pub fn append<T: Clone + Eq + Hash>(
        &mut self,
        left: Sequence<'g, T>,
        right: Sequence<'g, T>,
    ) -> Result<Sequence<'g, T>, crate::arena::CapacityError>
    where
        Self: AsMut<Sequences<'g, T>>,
    {
        let arena = self.as_mut();
        arena.append(left, right)
    }
}

impl<'g> std::ops::Index<summaries::SummaryId<'g>> for Graph<'g> {
    type Output = summaries::SummaryNode<'g>;
    fn index(&self, id: summaries::SummaryId<'g>) -> &Self::Output {
        &self.summaries[id]
    }
}

impl<'g> std::ops::Index<summaries::ConsumerId<'g>> for Graph<'g> {
    type Output = summaries::ConsumerNode<'g>;
    fn index(&self, id: summaries::ConsumerId<'g>) -> &Self::Output {
        &self.summaries[id]
    }
}
