use std::hash::{Hash, Hasher};
use std::marker::PhantomData;
use std::sync::Arc;

use parking_lot::Mutex;

use rustc_data_structures::fx::{FxHashMap, FxHasher};

use crate::arena::{ArenaId, Intern};
use crate::contracts::graph::sets::{Combination, SetId, Sets};
use crate::contracts::graph::{CapacityError, ExprId, ExprNode, Graph, NodeId};
use crate::sequence::{Fold, Part, Sequence, Sequences};

fn hash<T: Hash>(value: &T) -> u64 {
    let mut hasher = FxHasher::default();
    value.hash(&mut hasher);
    hasher.finish()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ChoiceId<'g> {
    pub(crate) index: u32,
    pub(crate) brand: PhantomData<fn(&'g ()) -> &'g ()>,
}

impl<'g> ArenaId for ChoiceId<'g> {
    fn from_index(index: u32) -> Self {
        Self {
            index,
            brand: PhantomData,
        }
    }

    fn index(self) -> u32 {
        self.index
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ChoiceNode<'g> {
    Value(ExprId<'g>),
    Branch(ChoiceId<'g>, ChoiceId<'g>),
}

/// Keeps ordered members and their set identity behind the same graph-owned root.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Choice<'g> {
    pub node: ChoiceNode<'g>,
    pub values: Sequence<'g, ExprId<'g>>,
    pub(crate) members: SetId<'g, ExprId<'g>>,
}

pub(crate) struct Choices<'g> {
    nodes: Intern<ChoiceId<'g>, Choice<'g>>,
    members: Sets<'g, ExprId<'g>>,
    indexed: Fold<'g, ExprId<'g>, ChoiceId<'g>>,
    joined: Arc<Mutex<FxHashMap<(ChoiceId<'g>, ChoiceId<'g>), ChoiceId<'g>>>>,
    filtered: Arc<Mutex<FxHashMap<(ChoiceId<'g>, SetId<'g, ExprId<'g>>), Option<ChoiceId<'g>>>>>,
}

impl Default for Choices<'_> {
    fn default() -> Self {
        Self {
            nodes: Intern::new(),
            members: Sets::new(),
            indexed: Fold::default(),
            joined: Arc::new(Mutex::new(FxHashMap::default())),
            filtered: Arc::new(Mutex::new(FxHashMap::default())),
        }
    }
}

impl<'g> Choices<'g> {}

impl<'g> Choices<'g> {
    fn index(
        &mut self,
        sequences: &mut Sequences<'g, ExprId<'g>>,
        values: Sequence<'g, ExprId<'g>>,
    ) -> Result<Option<ChoiceId<'g>>, CapacityError> {
        let Self {
            nodes,
            members,
            indexed,
            joined: _,
            filtered: _,
        } = self;
        indexed
            .fold(
                &mut &mut *sequences,
                |arena| &**arena,
                values,
                |sequences, part| {
                    let node = match part {
                        Part::Leaf(value) => ChoiceNode::Value(*value),
                        Part::Branch(left, right) => ChoiceNode::Branch(*left, *right),
                    };
                    let hash = hash(&node);
                    if let Some(id) =
                        nodes.find_by(hash, |choice| (choice.node == node).then_some(()))
                    {
                        return Ok(id);
                    }
                    let (values, set) = match node {
                        ChoiceNode::Value(value) => (
                            sequences.push(Sequence::EMPTY, value)?,
                            members.insert(SetId::EMPTY, value)?,
                        ),
                        ChoiceNode::Branch(left, right) => {
                            let left = &nodes[left];
                            let right = &nodes[right];
                            let values = sequences.append(left.values, right.values)?;
                            let set =
                                members.combine(Combination::Union, left.members, right.members)?;
                            (values, set)
                        }
                    };
                    let choice = Choice {
                        node,
                        values,
                        members: set,
                    };
                    nodes.intern_by(
                        choice,
                        hash,
                        CapacityError::Choices,
                        |existing, candidate| (existing.node == candidate.node).then_some(()),
                    )
                },
            )
            .map(|root| root)
    }

    pub(crate) fn value(
        &mut self,
        sequences: &mut Sequences<'g, ExprId<'g>>,
        value: ExprId<'g>,
    ) -> Result<ChoiceId<'g>, CapacityError> {
        let node = ChoiceNode::Value(value);
        if let Some(id) = self
            .nodes
            .find_by(hash(&node), |choice| (choice.node == node).then_some(()))
        {
            return Ok(id);
        }
        let values = sequences.push(Sequence::EMPTY, value)?;
        self.index(sequences, values)
            .map(|root| root.expect("a value has one choice"))
    }

    fn concatenate(
        &mut self,
        sequences: &mut Sequences<'g, ExprId<'g>>,
        left: ChoiceId<'g>,
        right: ChoiceId<'g>,
    ) -> Result<ChoiceId<'g>, CapacityError> {
        let values = sequences.append(self.nodes[left].values, self.nodes[right].values)?;
        self.index(sequences, values)
            .map(|root| root.expect("concatenating nonempty choices retains members"))
    }

    /// Retains left order and appends only new right members. Immutable fragments
    /// and membership-pair results survive across all roots in the graph.
    pub(crate) fn join(
        &mut self,
        sequences: &mut Sequences<'g, ExprId<'g>>,
        left: ChoiceId<'g>,
        right: ChoiceId<'g>,
    ) -> Result<ChoiceId<'g>, CapacityError> {
        if let Some(result) = self.joined.lock().get(&(left, right)).copied() {
            return Ok(result);
        }
        let excluded = self.nodes[left].members;
        enum Work<'g> {
            Visit(ChoiceId<'g>),
            Build(ChoiceId<'g>, ChoiceId<'g>, ChoiceId<'g>),
        }
        let mut pending = vec![Work::Visit(right)];
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(id) => {
                    if self.filtered.lock().contains_key(&(id, excluded)) {
                        continue;
                    }
                    let own = self.nodes[id].members;
                    if let Some(()) = self.members.subset(own, excluded) {
                        self.filtered.lock().insert((id, excluded), None);
                        continue;
                    }
                    if self
                        .members
                        .combine(Combination::Intersection, own, excluded)?
                        == SetId::EMPTY
                    {
                        self.filtered.lock().insert((id, excluded), Some(id));
                        continue;
                    }
                    let ChoiceNode::Branch(a, b) = self.nodes[id].node else {
                        unreachable!("an intersecting non-subset choice has multiple members");
                    };
                    pending.push(Work::Build(id, a, b));
                    pending.push(Work::Visit(b));
                    pending.push(Work::Visit(a));
                }
                Work::Build(id, a, b) => {
                    let (a, b) = {
                        let filtered = self.filtered.lock();
                        (filtered[&(a, excluded)], filtered[&(b, excluded)])
                    };
                    let result = match (a, b) {
                        (Some(left), Some(right)) => {
                            Some(self.concatenate(sequences, left, right)?)
                        }
                        (None, other) | (other, None) => other,
                    };
                    self.filtered.lock().insert((id, excluded), result);
                }
            }
        }
        let filtered = self.filtered.lock()[&(right, excluded)];
        let result = match filtered {
            Some(right) => self.concatenate(sequences, left, right)?,
            None => left,
        };
        self.joined.lock().insert((left, right), result);
        Ok(result)
    }
}

impl<'g> Graph<'g> {
    /// Flattens nested alternatives, preserving first occurrence order. Equal
    /// member sets retain the order chosen by their first interned expression.
    pub fn alternatives(
        &mut self,
        values: impl IntoIterator<Item = ExprId<'g>>,
    ) -> Result<ExprId<'g>, CapacityError> {
        let mut root = None;
        for value in values {
            let next = match self[value] {
                ExprNode::Alternatives(root) => root,
                _ => Some(self.choices.value(&mut self.expression_sequences, value)?),
            };
            root = match (root, next) {
                (Some(left), Some(right)) => Some(self.choices.join(
                    &mut self.expression_sequences,
                    left,
                    right,
                )?),
                (None, other) | (other, None) => other,
            };
        }
        self.intern_expr(ExprNode::Alternatives(root))
    }

    pub fn intern_choice(
        &mut self,
        node: ChoiceNode<'g>,
    ) -> Result<Option<ChoiceId<'g>>, CapacityError> {
        match node {
            ChoiceNode::Value(value) => match self[value] {
                ExprNode::Alternatives(root) => Ok(root),
                _ => self
                    .choices
                    .value(&mut self.expression_sequences, value)
                    .map(Some),
            },
            ChoiceNode::Branch(left, right) => self
                .choices
                .join(&mut self.expression_sequences, left, right)
                .map(Some),
        }
    }

    pub fn visit_children(&self, node: NodeId<'g>, mut visit: impl FnMut(NodeId<'g>)) {
        match node {
            NodeId::Expr(id) => self[id].visit_children(&self.expression_sequences, visit),
            NodeId::Condition(id) => self[id].visit_children(&self.expression_sequences, visit),
            NodeId::Choice(id) => match self[id].node {
                ChoiceNode::Value(value) => visit(NodeId::Expr(value)),
                ChoiceNode::Branch(left, right) => {
                    visit(NodeId::Choice(left));
                    visit(NodeId::Choice(right));
                }
            },
        }
    }

    pub(crate) fn widen_choices(
        &mut self,
        root: ChoiceId<'g>,
    ) -> Result<Option<ChoiceId<'g>>, CapacityError> {
        use crate::contracts::graph::{BinaryNode, fold_binary};
        fold_binary(
            self,
            root,
            |graph, id| {
                if let Some(result) = graph.widened_choices.get(&id) {
                    return Ok(BinaryNode::Ready(result));
                }
                match graph[id].node {
                    ChoiceNode::Value(value) => {
                        let value = match graph[value].clone() {
                            ExprNode::Closure(def, captures) => {
                                let unknown = graph.intern_expr(ExprNode::Unknown)?;
                                let len = graph.expression_sequences.len(captures);
                                let captures = graph
                                    .expression_sequences
                                    .from_iter(std::iter::repeat_n(unknown, len))?;
                                graph.intern_expr(ExprNode::Closure(def, captures))?
                            }
                            ExprNode::Typed(ty, _) => {
                                let unknown = graph.intern_expr(ExprNode::Unknown)?;
                                graph.intern_expr(ExprNode::Typed(ty, unknown))?
                            }
                            _ => value,
                        };
                        let result = graph.intern_choice(ChoiceNode::Value(value))?;
                        graph.widened_choices.insert(id, result);
                        Ok(BinaryNode::Ready(result))
                    }
                    ChoiceNode::Branch(left, right) => Ok(BinaryNode::Children(left, right)),
                }
            },
            |graph, id, left, right| {
                let result = match (left, right) {
                    (Some(left), Some(right)) => Some(graph.choices.join(
                        &mut graph.expression_sequences,
                        left,
                        right,
                    )?),
                    (None, other) | (other, None) => other,
                };
                graph.widened_choices.insert(id, result);
                Ok(result)
            },
        )
    }
}

impl<'g> std::ops::Index<ChoiceId<'g>> for Graph<'g> {
    type Output = Choice<'g>;
    fn index(&self, id: ChoiceId<'g>) -> &Self::Output {
        &self.choices[id]
    }
}

impl<'g> std::ops::Index<ChoiceId<'g>> for Choices<'g> {
    type Output = Choice<'g>;
    fn index(&self, id: ChoiceId<'g>) -> &Self::Output {
        &self.nodes[id]
    }
}

impl<'a, 'g> IntoIterator for &'a Choices<'g> {
    type Item = &'a Choice<'g>;
    type IntoIter = crate::arena::Iter<'a, Choice<'g>>;

    fn into_iter(self) -> Self::IntoIter {
        self.nodes.iter()
    }
}

impl<'g> Graph<'g> {
    // shapelint: allow(shallow-helper) Read-only iteration keeps the canonical choice store private.
    pub fn choices(&self) -> impl Iterator<Item = &Choice<'g>> + '_ {
        (&self.choices).into_iter()
    }
}
