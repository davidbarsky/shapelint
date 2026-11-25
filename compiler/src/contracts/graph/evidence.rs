use crate::contracts::graph::sets::{Combination, SetId};
use crate::contracts::graph::{CapacityError, ConditionId, Graph, GuardContextId};
use crate::contracts::{ProofGap, Truth};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct Evidence<'g>(pub(crate) SetId<'g, ConditionId<'g>>);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Proof<'g> {
    Proven(Evidence<'g>),
    Refuted(Evidence<'g>),
    Unknown(ProofGap),
}

impl From<Proof<'_>> for Truth {
    fn from(proof: Proof<'_>) -> Self {
        match proof {
            Proof::Proven(_) => Self::Proven,
            Proof::Refuted(_) => Self::Refuted,
            Proof::Unknown(gap) => Self::Unknown(gap),
        }
    }
}

impl<'g> Graph<'g> {
    /// Shares projected set fragments across proofs from this graph.
    pub fn evidence_sequence(
        &mut self,
        evidence: Evidence<'g>,
    ) -> Result<crate::sequence::Sequence<'g, ConditionId<'g>>, CapacityError> {
        use crate::contracts::graph::sets::NodeKind;
        use crate::contracts::graph::{BinaryNode, fold_binary};
        use crate::sequence::Sequence;

        fold_binary(
            self,
            evidence.0,
            |graph, node| {
                if let Some(sequence) = graph.evidence_sequences.get(&node) {
                    return Ok(BinaryNode::Ready(sequence));
                }
                let sequence = match graph.guard_member_sets[node].kind {
                    NodeKind::Empty => Sequence::EMPTY,
                    NodeKind::Leaf(condition) => {
                        graph.condition_sequences.push(Sequence::EMPTY, condition)?
                    }
                    NodeKind::Branch(left, right) => return Ok(BinaryNode::Children(right, left)),
                };
                graph.evidence_sequences.insert(node, sequence);
                Ok(BinaryNode::Ready(sequence))
            },
            |graph, node, right, left| {
                let sequence = graph.condition_sequences.append(left, right)?;
                graph.evidence_sequences.insert(node, sequence);
                Ok(sequence)
            },
        )
    }

    pub(crate) fn discharge(
        &mut self,
        evidence: Evidence<'g>,
        guards: GuardContextId<'g>,
    ) -> Result<Evidence<'g>, CapacityError> {
        match evidence.0 {
            SetId::EMPTY => Ok(Evidence::default()),
            root => {
                let members = self.guard_membership(guards)?;
                self.guard_member_sets
                    .combine(Combination::Intersection, root, members)
                    .map(Evidence)
            }
        }
    }
}
