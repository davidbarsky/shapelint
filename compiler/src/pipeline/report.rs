pub mod evaluator;

use crate::contracts::{CheckBasis, graph::ConditionId};
use crate::sequence::Sequence;
use shapelint::CheckOutcome;

pub struct EstablishedCheck<'g> {
    pub basis: CheckBasis<Sequence<'g, ConditionId<'g>>>,
    pub condition: ConditionId<'g>,
    pub outcome: CheckOutcome,
    pub support: evaluator::Support<'g>,
}
