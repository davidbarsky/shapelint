use rustc_data_structures::fx::{FxHashMap, FxIndexSet};

use crate::contracts::Invocation;
use crate::contracts::graph::{CapacityError, ConditionId, ExprId, Graph};
use crate::contracts::operations::{ArgumentProjection, InputSequence, InputUse, Inputs};
use crate::sequence::{Parts, Sequence};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct ApplicabilityId<'g>(u32, std::marker::PhantomData<fn(&'g ()) -> &'g ()>);

/// Preserves ordered occurrence contexts even when their combined coverage is unconditional.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Applicability<'g> {
    Context(Sequence<'g, ConditionId<'g>>),
    Prefix(Sequence<'g, ConditionId<'g>>, ApplicabilityId<'g>),
    Either(ApplicabilityId<'g>, ApplicabilityId<'g>),
}

#[derive(Clone, Copy)]
pub(crate) enum Traversal<'g> {
    Visit(ApplicabilityId<'g>),
    Finish(ApplicabilityId<'g>),
}

#[derive(Default)]
pub(crate) struct ApplicabilityWork {
    pub prefix_nodes: usize,
    pub first_visits: usize,
    pub substitution_entries: usize,
    pub membership_visits: usize,
    pub membership_guard_sequence_visits: usize,
    pub membership_guard_sequence_cache_hits: usize,
    pub membership_guard_leaf_comparisons: usize,
    pub membership_guard_sequence_entries: usize,
    pub membership_entries: usize,
}

#[derive(Default)]
pub(crate) struct Applicabilities<'g> {
    nodes: FxIndexSet<Applicability<'g>>,
    pub work: ApplicabilityWork,
    substitutions: FxHashMap<
        (ApplicabilityId<'g>, ArgumentProjection<'g>, Invocation<'g>),
        ApplicabilityId<'g>,
    >,
    first: FxHashMap<ApplicabilityId<'g>, Sequence<'g, ConditionId<'g>>>,
    inputs: FxHashMap<(InputUse, ApplicabilityId<'g>), Inputs<'g>>,
    membership: FxHashMap<(ApplicabilityId<'g>, ConditionId<'g>), Option<()>>,
    membership_guards: FxHashMap<(Sequence<'g, ConditionId<'g>>, ConditionId<'g>), Option<()>>,
}

impl<'g> Applicabilities<'g> {
    pub(crate) fn record_work(&self, work: &mut crate::contracts::Work) {
        work.applicability_nodes = self.nodes.len();
        work.applicability_prefix_nodes = self.work.prefix_nodes;
        work.applicability_first_visits = self.work.first_visits;
        work.applicability_substitution_entries = self.work.substitution_entries;
        work.applicability_membership_visits = self.work.membership_visits;
        work.applicability_membership_guard_sequence_visits =
            self.work.membership_guard_sequence_visits;
        work.applicability_membership_guard_sequence_cache_hits =
            self.work.membership_guard_sequence_cache_hits;
        work.applicability_membership_guard_leaf_comparisons =
            self.work.membership_guard_leaf_comparisons;
        work.applicability_membership_guard_sequence_entries =
            self.work.membership_guard_sequence_entries;
        work.applicability_membership_entries = self.work.membership_entries;
    }

    pub fn contains(
        &mut self,
        graph: &mut Graph<'g>,
        root: ApplicabilityId<'g>,
        target: ConditionId<'g>,
    ) -> Result<Option<()>, CapacityError> {
        if let Some(result) = self.membership.get(&(root, target)) {
            return Ok(*result);
        }
        enum MembershipFrame<'g> {
            Visit(ApplicabilityId<'g>),
            Prefix(ApplicabilityId<'g>, ApplicabilityId<'g>),
            EitherLeft(
                ApplicabilityId<'g>,
                ApplicabilityId<'g>,
                ApplicabilityId<'g>,
            ),
            EitherRight(ApplicabilityId<'g>, ApplicabilityId<'g>),
        }
        let mut pending = vec![MembershipFrame::Visit(root)];
        while let Some(frame) = pending.pop() {
            self.work.membership_visits = self.work.membership_visits.saturating_add(1);
            match frame {
                MembershipFrame::Visit(id) => {
                    if let Some(_) = self.membership.get(&(id, target)) {
                        continue;
                    }
                    match self[id] {
                        Applicability::Context(guards) => {
                            let result = self.contains_guards(graph, guards, target)?;
                            self.membership.insert((id, target), result);
                        }
                        Applicability::Prefix(guards, child) => {
                            match self.contains_guards(graph, guards, target)? {
                                Some(()) => {
                                    self.membership.insert((id, target), Some(()));
                                }
                                None => {
                                    pending.push(MembershipFrame::Prefix(id, child));
                                    pending.push(MembershipFrame::Visit(child));
                                }
                            }
                        }
                        Applicability::Either(left, right) => {
                            pending.push(MembershipFrame::EitherLeft(id, left, right));
                            pending.push(MembershipFrame::Visit(left));
                        }
                    }
                }
                MembershipFrame::Prefix(id, child) => {
                    let result = self.membership[&(child, target)];
                    self.membership.insert((id, target), result);
                }
                MembershipFrame::EitherLeft(id, left, right) => {
                    match self.membership[&(left, target)] {
                        Some(()) => {
                            self.membership.insert((id, target), Some(()));
                        }
                        None => {
                            pending.push(MembershipFrame::EitherRight(id, right));
                            pending.push(MembershipFrame::Visit(right));
                        }
                    }
                }
                MembershipFrame::EitherRight(id, right) => {
                    let result = self.membership[&(right, target)];
                    self.membership.insert((id, target), result);
                }
            }
        }
        self.work.membership_entries = self.membership.len();
        self.work.membership_guard_sequence_entries = self.membership_guards.len();
        Ok(self.membership[&(root, target)])
    }

    fn contains_guards(
        &mut self,
        graph: &mut Graph<'g>,
        guards: Sequence<'g, ConditionId<'g>>,
        target: ConditionId<'g>,
    ) -> Result<Option<()>, CapacityError> {
        enum Frame<'g> {
            Visit(Sequence<'g, ConditionId<'g>>),
            BranchLeft(
                Sequence<'g, ConditionId<'g>>,
                Sequence<'g, ConditionId<'g>>,
                Sequence<'g, ConditionId<'g>>,
            ),
            BranchRight(Sequence<'g, ConditionId<'g>>, Sequence<'g, ConditionId<'g>>),
        }
        let mut pending = vec![Frame::Visit(guards)];
        while let Some(frame) = pending.pop() {
            self.work.membership_guard_sequence_visits =
                self.work.membership_guard_sequence_visits.saturating_add(1);
            match frame {
                Frame::Visit(sequence) => {
                    if let Some(_) = self.membership_guards.get(&(sequence, target)) {
                        self.work.membership_guard_sequence_cache_hits = self
                            .work
                            .membership_guard_sequence_cache_hits
                            .saturating_add(1);
                        continue;
                    }
                    match crate::sequence::Sequences::parts(graph.as_mut(), sequence)? {
                        Parts::Empty => {
                            self.membership_guards.insert((sequence, target), None);
                        }
                        Parts::Leaf(condition) => {
                            self.work.membership_guard_leaf_comparisons = self
                                .work
                                .membership_guard_leaf_comparisons
                                .saturating_add(1);
                            let result = (condition == target).then_some(());
                            self.membership_guards.insert((sequence, target), result);
                        }
                        Parts::Branch(left, right) => {
                            pending.push(Frame::BranchLeft(sequence, left, right));
                            pending.push(Frame::Visit(left));
                        }
                    }
                }
                Frame::BranchLeft(sequence, left, right) => {
                    match self.membership_guards[&(left, target)] {
                        Some(()) => {
                            self.membership_guards.insert((sequence, target), Some(()));
                        }
                        None => {
                            pending.push(Frame::BranchRight(sequence, right));
                            pending.push(Frame::Visit(right));
                        }
                    }
                }
                Frame::BranchRight(sequence, right) => {
                    let result = self.membership_guards[&(right, target)];
                    self.membership_guards.insert((sequence, target), result);
                }
            }
        }
        self.work.membership_guard_sequence_entries = self.membership_guards.len();
        Ok(self.membership_guards[&(guards, target)])
    }

    pub fn intern(
        &mut self,
        node: Applicability<'g>,
    ) -> Result<ApplicabilityId<'g>, CapacityError> {
        if let Applicability::Prefix(guards, child) = node {
            if guards == Sequence::EMPTY {
                return Ok(child);
            }
            match self[child] {
                Applicability::Context(child_guards) if child_guards == guards => {
                    return Ok(child);
                }
                Applicability::Prefix(child_guards, grandchild) if child_guards == guards => {
                    return self.intern(Applicability::Prefix(guards, grandchild));
                }
                Applicability::Context(_)
                | Applicability::Prefix(..)
                | Applicability::Either(..) => {}
            }
        }
        if let Applicability::Either(left, right) = node {
            if left == right {
                return Ok(left);
            }
            if let (
                Applicability::Prefix(left_guards, left_child),
                Applicability::Prefix(right_guards, right_child),
            ) = (self[left], self[right])
                && left_guards == right_guards
            {
                let child = self.intern(Applicability::Either(left_child, right_child))?;
                return self.intern(Applicability::Prefix(left_guards, child));
            }
        }
        let index = match self.nodes.get_index_of(&node) {
            Some(index) => index,
            None => {
                u32::try_from(self.nodes.len()).map_err(|_| CapacityError::Sets)?;
                if let Applicability::Prefix(..) = node {
                    self.work.prefix_nodes = self.work.prefix_nodes.saturating_add(1);
                }
                self.nodes.insert_full(node).0
            }
        };
        Ok(ApplicabilityId(index as u32, std::marker::PhantomData))
    }

    pub fn substitute(
        &mut self,
        graph: &mut Graph<'g>,
        root: ApplicabilityId<'g>,
        arguments: Sequence<'g, ExprId<'g>>,
        invocation: Invocation<'g>,
    ) -> Result<ApplicabilityId<'g>, CapacityError> {
        if let Applicability::Context(guards) = self[root] {
            let guards = graph.substitute_guards(&guards, &arguments, &invocation)?;
            return self.intern(Applicability::Context(guards));
        }
        let inputs = self.inputs(graph, root, InputUse::Substitution)?;
        let projection = graph.project_arguments(
            inputs,
            crate::contracts::graph::ArgumentContextId(arguments),
        )?;
        let mut pending = vec![Traversal::Visit(root)];
        while let Some(frame) = pending.pop() {
            let id = match frame {
                Traversal::Visit(id) | Traversal::Finish(id) => id,
            };
            if self
                .substitutions
                .contains_key(&(id, projection, invocation))
            {
                continue;
            }
            let node = self[id];
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
            let node =
                match node {
                    Applicability::Context(guards) => Applicability::Context(
                        graph.substitute_guards(&guards, &arguments, &invocation)?,
                    ),
                    Applicability::Prefix(guards, child) => Applicability::Prefix(
                        graph.substitute_guards(&guards, &arguments, &invocation)?,
                        self.substitutions[&(child, projection, invocation)],
                    ),
                    Applicability::Either(left, right) => Applicability::Either(
                        self.substitutions[&(left, projection, invocation)],
                        self.substitutions[&(right, projection, invocation)],
                    ),
                };
            let result = self.intern(node)?;
            self.substitutions
                .insert((id, projection, invocation), result);
            self.work.substitution_entries = self.work.substitution_entries.saturating_add(1);
        }
        Ok(self.substitutions[&(root, projection, invocation)])
    }

    pub fn first(
        &mut self,
        graph: &mut Graph<'g>,
        root: ApplicabilityId<'g>,
    ) -> Result<Sequence<'g, ConditionId<'g>>, CapacityError> {
        if let Some(first) = self.first.get(&root) {
            return Ok(*first);
        }
        let mut pending = vec![Traversal::Visit(root)];
        while let Some(frame) = pending.pop() {
            self.work.first_visits = self.work.first_visits.saturating_add(1);
            let id = match frame {
                Traversal::Visit(id) | Traversal::Finish(id) => id,
            };
            if self.first.contains_key(&id) {
                continue;
            }
            let node = self[id];
            if let Traversal::Visit(_) = frame {
                pending.push(Traversal::Finish(id));
                match node {
                    Applicability::Context(_) => {}
                    Applicability::Prefix(_, child) | Applicability::Either(child, _) => {
                        pending.push(Traversal::Visit(child))
                    }
                }
                continue;
            }
            let guards = match node {
                Applicability::Context(guards) => guards,
                Applicability::Prefix(guards, child) => graph.append(guards, self.first[&child])?,
                Applicability::Either(child, _) => self.first[&child],
            };
            self.first.insert(id, guards);
        }
        Ok(self.first[&root])
    }

    pub fn inputs(
        &mut self,
        graph: &mut Graph<'g>,
        root: ApplicabilityId<'g>,
        usage: InputUse,
    ) -> Result<Inputs<'g>, CapacityError> {
        enum Work<'g> {
            Visit(ApplicabilityId<'g>),
            Prefix(ApplicabilityId<'g>, Inputs<'g>, ApplicabilityId<'g>),
            Left(
                ApplicabilityId<'g>,
                ApplicabilityId<'g>,
                ApplicabilityId<'g>,
            ),
            Right(ApplicabilityId<'g>, Inputs<'g>, ApplicabilityId<'g>),
        }
        if let Some(inputs) = self.inputs.get(&(usage, root)) {
            return Ok(*inputs);
        }
        let mut pending = vec![Work::Visit(root)];
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(id) => {
                    if self.inputs.contains_key(&(usage, id)) {
                        continue;
                    }
                    match self[id] {
                        Applicability::Context(guards) => {
                            let inputs = graph
                                .sequence_input_summary(InputSequence::Conditions(guards), usage)?;
                            self.inputs.insert((usage, id), inputs);
                        }
                        Applicability::Prefix(guards, child) => {
                            match graph
                                .sequence_input_summary(InputSequence::Conditions(guards), usage)?
                            {
                                Inputs::Unknown => {
                                    self.inputs.insert((usage, id), Inputs::Unknown);
                                }
                                inputs @ Inputs::Known(_) => {
                                    pending.push(Work::Prefix(id, inputs, child));
                                    pending.push(Work::Visit(child));
                                }
                            }
                        }
                        Applicability::Either(left, right) => {
                            pending.push(Work::Left(id, left, right));
                            pending.push(Work::Visit(left));
                        }
                    }
                }
                Work::Prefix(id, own, child) => {
                    let inputs = graph.combine_inputs(own, self.inputs[&(usage, child)])?;
                    self.inputs.insert((usage, id), inputs);
                }
                Work::Left(id, left, right) => match self.inputs[&(usage, left)] {
                    Inputs::Unknown => {
                        self.inputs.insert((usage, id), Inputs::Unknown);
                    }
                    inputs @ Inputs::Known(_) => {
                        pending.push(Work::Right(id, inputs, right));
                        pending.push(Work::Visit(right));
                    }
                },
                Work::Right(id, left, right) => {
                    let inputs = graph.combine_inputs(left, self.inputs[&(usage, right)])?;
                    self.inputs.insert((usage, id), inputs);
                }
            }
        }
        Ok(self.inputs[&(usage, root)])
    }
}

impl<'g> std::ops::Index<ApplicabilityId<'g>> for Applicabilities<'g> {
    type Output = Applicability<'g>;

    fn index(&self, id: ApplicabilityId<'g>) -> &Self::Output {
        &self.nodes[id.0 as usize]
    }
}
