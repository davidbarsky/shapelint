use crate::contracts::graph::comparisons::Vertex;
use crate::contracts::graph::evidence::{Evidence, Proof};
use crate::memo::{Demand, Memo};
use crate::persistent::Neighbor;
use crate::sequence::Sequence;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Local;

use crate::contracts::graph::sets::{Combination, SetId};
use crate::contracts::graph::{
    ArgumentContextId, CapacityError, ChoiceId, ChoiceNode, ConditionId, ConditionNode, ExprId,
    ExprNode, Graph, GuardContextId, NodeId, RewriteId, TargetNode, TextMatchNode,
};
use crate::contracts::{
    Arithmetic, Interval, Invocation, Join, Order, ProofGap, Relocation, Truth,
};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum GraphInvalidation<'g> {
    Local(Local),
    Memory(ExprId<'g>),
    Replace {
        target: ExprId<'g>,
        value: ExprId<'g>,
    },
}

pub type Affected<'g> = SetId<'g, NodeId<'g>>;

#[derive(Clone, Copy)]
enum Binding {
    Value,
    Independent,
    Dependent,
}

#[derive(Clone, Copy)]
enum Captures {
    None,
    Present,
}

#[derive(Clone, Copy)]
pub(crate) struct Parameter {
    binding: Binding,
    captures: Captures,
}

#[derive(Clone, Copy)]
enum ParameterNode<'g> {
    Expr(ExprId<'g>),
    Choice(ChoiceId<'g>),
}

#[derive(Clone, Copy)]
struct Bound<'g, K> {
    id: K,
    supplied: ExprId<'g>,
    class: Parameter,
}

impl<'g, K: Copy> Bound<'g, K> {
    fn key(self) -> (K, Option<ExprId<'g>>) {
        let binding = match self.class.binding {
            Binding::Independent => None,
            Binding::Value | Binding::Dependent => Some(self.supplied),
        };
        (self.id, binding)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Inputs<'g> {
    Unknown,
    Known(SetId<'g, usize>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum InputUse {
    Value,
    /// Tracks argument reads by substitution, even when the value is opaque.
    /// Invocation identity remains a separate part of the substitution key.
    Substitution,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum InputSequence<'g> {
    Conditions(Sequence<'g, ConditionId<'g>>),
    Expressions(Sequence<'g, ExprId<'g>>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum ArgumentProjection<'g> {
    Full(ArgumentContextId<'g>),
    Relevant(Sequence<'g, (usize, Option<ExprId<'g>>)>),
}

#[derive(Clone, Copy, Default)]
pub struct SubstitutionWork {
    /// Counts input-summary work frames, including cached traversal frames.
    pub input_visits: usize,
    /// Counts cache misses for known-input projections.
    pub argument_projections: usize,
    /// Counts sparse argument positions read on projection cache misses.
    pub argument_projection_positions: usize,
    /// Counts completed rewrite build frames for every rewrite operation.
    pub rewritten_nodes: usize,
}

#[derive(Clone, Copy)]
enum Frame<'g> {
    Visit(NodeId<'g>),
    Build(NodeId<'g>),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum GuardSegment<'g> {
    Common(Sequence<'g, ConditionId<'g>>),
    Relevant(ConditionId<'g>, NodeId<'g>),
}

#[derive(Clone)]
pub(crate) enum GuardClassification<'g> {
    Common(Sequence<'g, ConditionId<'g>>),
    Mixed {
        segments: Sequence<'g, GuardSegment<'g>>,
        targets: SetId<'g, NodeId<'g>>,
    },
}

#[derive(Clone, Copy)]
pub(crate) enum PreparedGuards<'g> {
    Common(GuardContextId<'g>),
    Mixed {
        segments: Sequence<'g, GuardSegment<'g>>,
        targets: SetId<'g, NodeId<'g>>,
        shared: SetId<'g, NodeId<'g>>,
    },
}

#[derive(Clone, Copy)]
pub(crate) struct GuardProjectionSummary<'g> {
    targets: SetId<'g, NodeId<'g>>,
    common: Option<()>,
}

#[derive(Clone)]
pub(crate) struct GuardEndpoints<'g> {
    seen: SetId<'g, NodeId<'g>>,
    shared: SetId<'g, NodeId<'g>>,
}

#[derive(Clone, Copy)]
enum Rewrite<'a, 'g> {
    Substitute(&'a Sequence<'g, ExprId<'g>>, &'a Invocation<'g>),
    Invalidate(GraphInvalidation<'g>, Affected<'g>),
    Provenance,
}

struct PreparedRewrite<'a, 'g> {
    context: RewriteId<'g>,
    operation: Rewrite<'a, 'g>,
}

#[derive(PartialEq, Eq, Hash)]
pub(crate) enum RewriteKey<'g> {
    Substitute {
        arguments: ArgumentProjection<'g>,
        scope: Invocation<'g>,
    },
    Invalidate(
        GraphInvalidation<'g>,
        crate::contracts::graph::sets::SetId<'g, NodeId<'g>>,
    ),
    Provenance,
}

impl<'g> Graph<'g> {
    fn rewritten_expr(
        &self,
        rewrite: &PreparedRewrite<'_, 'g>,
        id: ExprId<'g>,
    ) -> Result<ExprId<'g>, Demand<NodeId<'g>>> {
        let key = NodeId::Expr(id);
        match rewrite.operation {
            Rewrite::Invalidate(_, affected)
                if let None = self.reference_sets.contains(affected, key) =>
            {
                Ok(id)
            }
            _ => self
                .rewritten_expressions
                .get(&(rewrite.context, id))
                .ok_or(Demand::Child(key)),
        }
    }
    fn rewritten_condition(
        &self,
        rewrite: &PreparedRewrite<'_, 'g>,
        id: ConditionId<'g>,
    ) -> Result<ConditionId<'g>, Demand<NodeId<'g>>> {
        let key = NodeId::Condition(id);
        match rewrite.operation {
            Rewrite::Invalidate(_, affected)
                if let None = self.reference_sets.contains(affected, key) =>
            {
                Ok(id)
            }
            _ => self
                .rewritten_conditions
                .get(&(rewrite.context, id))
                .ok_or(Demand::Child(key)),
        }
    }
    fn rewritten_choice(
        &self,
        rewrite: &PreparedRewrite<'_, 'g>,
        id: ChoiceId<'g>,
    ) -> Result<Option<ChoiceId<'g>>, Demand<NodeId<'g>>> {
        let key = NodeId::Choice(id);
        match rewrite.operation {
            Rewrite::Invalidate(_, affected)
                if let None = self.reference_sets.contains(affected, key) =>
            {
                Ok(Some(id))
            }
            _ => self
                .rewritten_choices
                .get(&(rewrite.context, id))
                .ok_or(Demand::Child(key)),
        }
    }
    fn rewritten_target(
        &self,
        rewrite: &PreparedRewrite<'_, 'g>,
        target: TargetNode<'g>,
    ) -> Result<TargetNode<'g>, Demand<NodeId<'g>>> {
        match target {
            TargetNode::Direct(instance) => Ok(TargetNode::Direct(instance)),
            TargetNode::Indirect(value) => {
                Ok(TargetNode::Indirect(self.rewritten_expr(rewrite, value)?))
            }
        }
    }
    fn rewritten_arguments(
        &mut self,
        rewrite: &PreparedRewrite<'_, 'g>,
        sequence: Sequence<'g, ExprId<'g>>,
    ) -> Result<Sequence<'g, ExprId<'g>>, Demand<NodeId<'g>>> {
        let mut mapped = self.rewritten_argument_sequences.share();
        mapped.apply(
            self,
            |graph| &mut graph.expression_sequences,
            sequence,
            rewrite.context,
            |graph, value| graph.rewritten_expr(rewrite, *value),
        )
    }
    fn rewrite_expr_node(
        &mut self,
        rewrite: &PreparedRewrite<'_, 'g>,
        node: ExprNode<'g>,
    ) -> Result<ExprNode<'g>, Demand<NodeId<'g>>> {
        Ok(match node {
            ExprNode::Serialized {
                value,
                def,
                span,
                encoding,
                ty,
            } => ExprNode::Serialized {
                value: self.rewritten_expr(rewrite, value)?,
                def,
                span,
                encoding,
                ty,
            },
            ExprNode::Typed(ty, value) => ExprNode::Typed(ty, self.rewritten_expr(rewrite, value)?),
            ExprNode::Alternatives(root) => ExprNode::Alternatives(
                root.map(|id| self.rewritten_choice(rewrite, id))
                    .transpose()?
                    .flatten(),
            ),
            ExprNode::Select(test, yes, no) => ExprNode::Select(
                self.rewritten_condition(rewrite, test)?,
                self.rewritten_expr(rewrite, yes)?,
                self.rewritten_expr(rewrite, no)?,
            ),
            ExprNode::Field(value, index) => {
                ExprNode::Field(self.rewritten_expr(rewrite, value)?, index)
            }
            ExprNode::Element(value, index) => ExprNode::Element(
                self.rewritten_expr(rewrite, value)?,
                self.rewritten_expr(rewrite, index)?,
            ),
            ExprNode::Closure(def, values) => {
                ExprNode::Closure(def, self.rewritten_arguments(rewrite, values)?)
            }
            ExprNode::Aggregate(values) => {
                ExprNode::Aggregate(self.rewritten_arguments(rewrite, values)?)
            }
            ExprNode::Variant(def, variant, values) => {
                ExprNode::Variant(def, variant, self.rewritten_arguments(rewrite, values)?)
            }
            ExprNode::Length(value) => ExprNode::Length(self.rewritten_expr(rewrite, value)?),
            ExprNode::Trimmed(value) => ExprNode::Trimmed(self.rewritten_expr(rewrite, value)?),
            ExprNode::Found { text, pattern } => ExprNode::Found {
                text: self.rewritten_expr(rewrite, text)?,
                pattern: self.rewritten_expr(rewrite, pattern)?,
            },
            ExprNode::MatchIndex {
                text,
                pattern,
                occurrence,
            } => ExprNode::MatchIndex {
                text: self.rewritten_expr(rewrite, text)?,
                pattern: self.rewritten_expr(rewrite, pattern)?,
                occurrence: self.rewritten_expr(rewrite, occurrence)?,
            },
            ExprNode::Matches { text, pattern } => ExprNode::Matches {
                text: self.rewritten_expr(rewrite, text)?,
                pattern: self.rewritten_expr(rewrite, pattern)?,
            },
            ExprNode::MatchEntry(mut value) => {
                value.text = self.rewritten_expr(rewrite, value.text)?;
                value.pattern = self.rewritten_expr(rewrite, value.pattern)?;
                value.occurrence = self.rewritten_expr(rewrite, value.occurrence)?;
                ExprNode::MatchEntry(value)
            }
            ExprNode::Tokens { text, consumed } => ExprNode::Tokens {
                text: self.rewritten_expr(rewrite, text)?,
                consumed: self.rewritten_expr(rewrite, consumed)?,
            },
            ExprNode::Token(mut value) => {
                value.text = self.rewritten_expr(rewrite, value.text)?;
                value.start = self.rewritten_expr(rewrite, value.start)?;
                value.length = self.rewritten_expr(rewrite, value.length)?;
                ExprNode::Token(value)
            }
            ExprNode::NextToken(mut value) => {
                value.text = self.rewritten_expr(rewrite, value.text)?;
                value.start = self.rewritten_expr(rewrite, value.start)?;
                value.length = self.rewritten_expr(rewrite, value.length)?;
                ExprNode::NextToken(value)
            }
            ExprNode::Partition {
                sequence,
                predicate,
            } => ExprNode::Partition {
                sequence: self.rewritten_expr(rewrite, sequence)?,
                predicate: self.rewritten_expr(rewrite, predicate)?,
            },
            ExprNode::Slice { text, start, end } => ExprNode::Slice {
                text: self.rewritten_expr(rewrite, text)?,
                start: self.rewritten_expr(rewrite, start)?,
                end: self.rewritten_expr(rewrite, end)?,
            },
            ExprNode::Arithmetic(op, left, right) => ExprNode::Arithmetic(
                op,
                self.rewritten_expr(rewrite, left)?,
                self.rewritten_expr(rewrite, right)?,
            ),
            ExprNode::Call(target, arguments, origin) => ExprNode::Call(
                self.rewritten_target(rewrite, target)?,
                self.rewritten_arguments(rewrite, arguments)?,
                origin,
            ),
            ExprNode::Test(test) => ExprNode::Test(self.rewritten_condition(rewrite, test)?),
            node @ (ExprNode::Unknown
            | ExprNode::Function(_)
            | ExprNode::Opaque(_)
            | ExprNode::Global(_)
            | ExprNode::Argument(_)
            | ExprNode::Number(_)
            | ExprNode::Range(_)
            | ExprNode::Text(_)
            | ExprNode::Cursor { .. }) => node,
        })
    }

    fn rewrite_condition_node(
        &mut self,
        rewrite: &PreparedRewrite<'_, 'g>,
        node: ConditionNode<'g>,
    ) -> Result<ConditionNode<'g>, Demand<NodeId<'g>>> {
        Ok(match node {
            ConditionNode::Unknown => ConditionNode::Unknown,
            ConditionNode::Compare(order, left, right) => ConditionNode::Compare(
                order,
                self.rewritten_expr(rewrite, left)?,
                self.rewritten_expr(rewrite, right)?,
            ),
            ConditionNode::Boundary(text, index) => ConditionNode::Boundary(
                self.rewritten_expr(rewrite, text)?,
                self.rewritten_expr(rewrite, index)?,
            ),
            ConditionNode::NotBoundary(text, index) => ConditionNode::NotBoundary(
                self.rewritten_expr(rewrite, text)?,
                self.rewritten_expr(rewrite, index)?,
            ),
            ConditionNode::Variant(value, variant) => {
                ConditionNode::Variant(self.rewritten_expr(rewrite, value)?, variant)
            }
            ConditionNode::NotVariant(value, variant) => {
                ConditionNode::NotVariant(self.rewritten_expr(rewrite, value)?, variant)
            }
            ConditionNode::Returned(target, arguments) => ConditionNode::Returned(
                self.rewritten_target(rewrite, target)?,
                self.rewritten_arguments(rewrite, arguments)?,
            ),
        })
    }
}

/// Returns each completed child to its waiting parent, in traversal order.
fn fold_children<S, K: Copy, D, V>(
    state: &mut S,
    mut key: K,
    mut visit: impl FnMut(&mut S, K) -> Result<std::ops::ControlFlow<V, (D, Vec<K>)>, CapacityError>,
    mut finish: impl FnMut(&mut S, K, D, Vec<V>) -> Result<V, CapacityError>,
) -> Result<V, CapacityError> {
    let mut parents = Vec::new();
    loop {
        let mut value = match visit(state, key)? {
            std::ops::ControlFlow::Break(value) => value,
            std::ops::ControlFlow::Continue((data, children)) => {
                let results = Vec::with_capacity(children.len());
                let mut children = children.into_iter();
                match children.next() {
                    Some(child) => {
                        parents.push((key, data, children, results));
                        key = child;
                        continue;
                    }
                    None => finish(state, key, data, results)?,
                }
            }
        };
        loop {
            let Some((parent, data, mut children, mut results)) = parents.pop() else {
                return Ok(value);
            };
            results.push(value);
            match children.next() {
                Some(child) => {
                    parents.push((parent, data, children, results));
                    key = child;
                    break;
                }
                None => value = finish(state, parent, data, results)?,
            }
        }
    }
}

impl<'g> Graph<'g> {
    pub fn typed(
        &mut self,
        ty: crate::values::TypeId<'g>,
        value: ExprId<'g>,
    ) -> Result<ExprId<'g>, CapacityError> {
        match self.values[ty] {
            crate::values::TypeNode::Unknown => Ok(value),
            _ => self.intern_expr(ExprNode::Typed(ty, value)),
        }
    }

    pub fn negate(&mut self, condition: ConditionId<'g>) -> Result<ConditionId<'g>, CapacityError> {
        let node = match self[condition] {
            ConditionNode::Compare(order, left, right) => match order {
                Order::Less => ConditionNode::Compare(Order::LessEqual, right, left),
                Order::LessEqual => ConditionNode::Compare(Order::Less, right, left),
                Order::Equal => ConditionNode::Compare(Order::NotEqual, left, right),
                Order::NotEqual => ConditionNode::Compare(Order::Equal, left, right),
            },
            ConditionNode::Boundary(text, index) => ConditionNode::NotBoundary(text, index),
            ConditionNode::NotBoundary(text, index) => ConditionNode::Boundary(text, index),
            ConditionNode::Variant(value, variant) => ConditionNode::NotVariant(value, variant),
            ConditionNode::NotVariant(value, variant) => ConditionNode::Variant(value, variant),
            ConditionNode::Unknown | ConditionNode::Returned(..) => ConditionNode::Unknown,
        };
        self.intern_condition(node)
    }

    pub fn from_expr(
        &mut self,
        value: ExprId<'g>,
        expected: u128,
    ) -> Result<ConditionId<'g>, CapacityError> {
        match self[value] {
            ExprNode::Test(condition) => match expected {
                0 => self.negate(condition),
                1 => Ok(condition),
                _ => self.intern_condition(ConditionNode::Unknown),
            },
            ExprNode::Unknown => self.intern_condition(ConditionNode::Unknown),
            _ => {
                let number = self.intern_expr(ExprNode::Number(expected))?;
                self.intern_condition(ConditionNode::Compare(Order::Equal, value, number))
            }
        }
    }

    pub(crate) fn downcast(&self, value: ExprId<'g>, variant: usize) -> ExprId<'g> {
        if let ExprNode::Select(_, yes, no) = self[value]
            && let (ExprNode::Variant(_, yes_variant, _), ExprNode::Variant(_, no_variant, _)) =
                (&self[yes], &self[no])
        {
            match (*yes_variant == variant, *no_variant == variant) {
                (true, false) => return yes,
                (false, true) => return no,
                _ => {}
            }
        }
        value
    }

    pub fn field(&mut self, root: ExprId<'g>, index: usize) -> Result<ExprId<'g>, CapacityError> {
        use crate::memo::{Demand, resolve};
        #[derive(Clone, Copy)]
        enum Field<'g> {
            Expr(ExprId<'g>),
            Choice(ChoiceId<'g>),
        }
        resolve(
            self,
            |graph| graph.fields.get(&(root, index)).ok_or(Field::Expr(root)),
            |graph, request| {
                let field = |id| {
                    graph
                        .fields
                        .get(&(id, index))
                        .ok_or(Demand::Child(Field::Expr(id)))
                };
                let choices = |id| {
                    graph
                        .choice_fields
                        .get(&(id, index))
                        .ok_or(Demand::Child(Field::Choice(id)))
                };
                match request {
                    Field::Expr(id) => {
                        let key = (id, index);
                        if graph.fields.get(&key).is_some() {
                            return Ok(());
                        }
                        let value = match &graph[id] {
                            ExprNode::Typed(_, value) => field(*value)?,
                            ExprNode::Alternatives(root) => {
                                let root = root.map(choices).transpose()?.flatten();
                                graph.intern_expr(ExprNode::Alternatives(root))?
                            }
                            ExprNode::Select(condition, yes, no) => graph.intern_expr(
                                ExprNode::Select(*condition, field(*yes)?, field(*no)?),
                            )?,
                            ExprNode::Aggregate(fields)
                            | ExprNode::Variant(_, _, fields)
                            | ExprNode::Closure(_, fields) => {
                                match graph.expression_sequences.get(*fields, index) {
                                    Some(value) => *value,
                                    None => graph.intern_expr(ExprNode::Unknown)?,
                                }
                            }
                            ExprNode::NextToken(token) if index == 0 => {
                                graph.intern_expr(ExprNode::Token(token.clone()))?
                            }
                            ExprNode::Token(token) if index == 1 => token.length,
                            ExprNode::MatchEntry(value) if index == 0 => {
                                let TextMatchNode {
                                    text,
                                    pattern,
                                    occurrence,
                                } = *value;
                                let found = graph.intern_expr(ExprNode::MatchIndex {
                                    text,
                                    pattern,
                                    occurrence,
                                })?;
                                let values =
                                    graph.expression_sequences.from_iter([found, pattern])?;
                                graph.intern_expr(ExprNode::Aggregate(values))?
                            }
                            ExprNode::Found { text, pattern } if index == 0 => {
                                let (text, pattern) = (*text, *pattern);
                                let occurrence = graph.intern_expr(ExprNode::Number(0))?;
                                graph.intern_expr(ExprNode::MatchIndex {
                                    text,
                                    pattern,
                                    occurrence,
                                })?
                            }
                            ExprNode::Unknown => id,
                            _ => graph.intern_expr(ExprNode::Field(id, index))?,
                        };
                        graph.fields.insert(key, value);
                    }
                    Field::Choice(id) => {
                        let key = (id, index);
                        if graph.choice_fields.get(&key).is_some() {
                            return Ok(());
                        }
                        let result = match graph[id].node {
                            ChoiceNode::Value(value) => {
                                graph.intern_choice(ChoiceNode::Value(field(value)?))?
                            }
                            ChoiceNode::Branch(left, right) => {
                                match (choices(left)?, choices(right)?) {
                                    (Some(left), Some(right)) => Some(graph.choices.join(
                                        &mut graph.expression_sequences,
                                        left,
                                        right,
                                    )?),
                                    (None, other) | (other, None) => other,
                                }
                            }
                        };
                        graph.choice_fields.insert(key, result);
                    }
                }
                Ok(())
            },
        )
    }

    fn bounds(&self, value: ExprId<'g>) -> Option<(u128, u128)> {
        match &self[value] {
            ExprNode::Number(value) => Some((*value, *value)),
            ExprNode::Range(Interval { lower, upper }) => Some((*lower, *upper)),
            _ => None,
        }
    }

    pub fn join(
        &mut self,
        left: ExprId<'g>,
        right: ExprId<'g>,
        join: Join,
    ) -> Result<ExprId<'g>, CapacityError> {
        use crate::memo::{Demand, VisitOrder, collect, resolve};
        let root = (left, right);
        resolve(
            self,
            |graph| graph.joins.get(&(left, right, join)).ok_or(root),
            |graph, (left, right)| {
                let key = (left, right, join);
                if graph.joins.get(&key).is_some() {
                    return Ok(());
                }
                if left == right {
                    graph.joins.insert(key, left);
                    return Ok(());
                }
                let fields = |graph: &mut Self, left, right| -> Result<_, Demand<_>> {
                    let pairs = graph
                        .expression_sequences
                        .iter(left)
                        .copied()
                        .zip(graph.expression_sequences.iter(right).copied());
                    let mapped = collect(
                        pairs,
                        |(left, right)| graph.joins.get(&(left, right, join)),
                        |pair| pair,
                        VisitOrder::Forward,
                    )?;
                    Ok(graph.expression_sequences.from_iter(mapped)?)
                };
                let node = match (&graph[left], &graph[right]) {
                    (ExprNode::Closure(def, a), ExprNode::Closure(other, b))
                        if def == other
                            && graph.expression_sequences.len(*a)
                                == graph.expression_sequences.len(*b) =>
                    {
                        ExprNode::Closure(*def, fields(graph, *a, *b)?)
                    }
                    (ExprNode::Typed(ty, a), ExprNode::Typed(other, b)) if ty == other => {
                        let value = graph
                            .joins
                            .get(&(*a, *b, join))
                            .ok_or(Demand::Child((*a, *b)))?;
                        ExprNode::Typed(*ty, value)
                    }
                    (
                        ExprNode::Function(_)
                        | ExprNode::Closure(..)
                        | ExprNode::Typed(..)
                        | ExprNode::Alternatives(_),
                        _,
                    )
                    | (
                        _,
                        ExprNode::Function(_)
                        | ExprNode::Closure(..)
                        | ExprNode::Typed(..)
                        | ExprNode::Alternatives(_),
                    ) => {
                        let mut root = None;
                        for value in [left, right] {
                            let mut next = match graph[value] {
                                ExprNode::Alternatives(root) => root,
                                _ => Some(
                                    graph
                                        .choices
                                        .value(&mut graph.expression_sequences, value)?,
                                ),
                            };
                            if let (Join::Widen, Some(choice)) = (join, next) {
                                next = graph.widen_choices(choice)?;
                            }
                            root = match (root, next) {
                                (Some(left), Some(right)) => Some(graph.choices.join(
                                    &mut graph.expression_sequences,
                                    left,
                                    right,
                                )?),
                                (None, other) | (other, None) => other,
                            };
                        }
                        ExprNode::Alternatives(root)
                    }
                    (ExprNode::Variant(def, variant, a), ExprNode::Variant(other, tag, b))
                        if def == other
                            && variant == tag
                            && graph.expression_sequences.len(*a)
                                == graph.expression_sequences.len(*b) =>
                    {
                        ExprNode::Variant(*def, *variant, fields(graph, *a, *b)?)
                    }
                    (ExprNode::Aggregate(a), ExprNode::Aggregate(b))
                        if graph.expression_sequences.len(*a)
                            == graph.expression_sequences.len(*b) =>
                    {
                        ExprNode::Aggregate(fields(graph, *a, *b)?)
                    }
                    _ => match (graph.bounds(left), graph.bounds(right)) {
                        (Some((left_min, left_max)), Some((right_min, right_max))) => {
                            ExprNode::Range(Interval {
                                lower: match join {
                                    Join::Widen if right_min < left_min => 0,
                                    _ => left_min.min(right_min),
                                },
                                upper: match join {
                                    Join::Widen if right_max > left_max => u128::MAX,
                                    _ => left_max.max(right_max),
                                },
                            })
                        }
                        _ => ExprNode::Unknown,
                    },
                };
                let value = graph.intern_expr(node)?;
                graph.joins.insert(key, value);
                Ok(())
            },
        )
    }

    pub(crate) fn input_summary(
        &mut self,
        root: NodeId<'g>,
        usage: InputUse,
    ) -> Result<Inputs<'g>, CapacityError> {
        enum InputWork<'g> {
            Visit(NodeId<'g>),
            Next(NodeId<'g>, std::vec::IntoIter<NodeId<'g>>, Inputs<'g>),
        }
        if let Some(inputs) = self.input_summaries.get(&(usage, root)) {
            return Ok(inputs);
        }
        let mut parents = Vec::new();
        let mut frame = InputWork::Visit(root);
        loop {
            self.substitution_work.input_visits =
                self.substitution_work.input_visits.saturating_add(1);
            let mut result = match frame {
                InputWork::Visit(node) => {
                    if let Some(result) = self.input_summaries.get(&(usage, node)) {
                        result
                    } else {
                        let direct = match node {
                            NodeId::Expr(id) => match &self[id] {
                                ExprNode::Argument(index) => {
                                    let index = *index;
                                    let inputs = self.input_sets.insert(SetId::EMPTY, index)?;
                                    Some(Inputs::Known(inputs))
                                }
                                ExprNode::Number(_) | ExprNode::Text(_) | ExprNode::Function(_) => {
                                    Some(Inputs::Known(SetId::EMPTY))
                                }
                                ExprNode::Typed(..)
                                | ExprNode::Field(..)
                                | ExprNode::Length(_)
                                | ExprNode::Trimmed(_)
                                | ExprNode::Element(..)
                                | ExprNode::Arithmetic(..)
                                | ExprNode::Aggregate(_)
                                | ExprNode::Variant(..)
                                | ExprNode::Closure(..)
                                | ExprNode::Alternatives(_)
                                | ExprNode::Select(..)
                                | ExprNode::Test(_) => None,
                                ExprNode::Serialized { .. }
                                | ExprNode::Unknown
                                | ExprNode::Opaque(_)
                                | ExprNode::Global(_)
                                | ExprNode::Range(_)
                                | ExprNode::Found { .. }
                                | ExprNode::MatchIndex { .. }
                                | ExprNode::Matches { .. }
                                | ExprNode::MatchEntry(_)
                                | ExprNode::Tokens { .. }
                                | ExprNode::Token(_)
                                | ExprNode::NextToken(_)
                                | ExprNode::Cursor { .. }
                                | ExprNode::Partition { .. }
                                | ExprNode::Slice { .. }
                                | ExprNode::Call(..) => match usage {
                                    InputUse::Value => Some(Inputs::Unknown),
                                    InputUse::Substitution => None,
                                },
                            },
                            NodeId::Choice(_) => None,
                            NodeId::Condition(id) => match &self[id] {
                                ConditionNode::Unknown | ConditionNode::Returned(..) => match usage
                                {
                                    InputUse::Value => Some(Inputs::Unknown),
                                    InputUse::Substitution => None,
                                },
                                ConditionNode::Compare(..)
                                | ConditionNode::Boundary(..)
                                | ConditionNode::NotBoundary(..)
                                | ConditionNode::Variant(..)
                                | ConditionNode::NotVariant(..) => None,
                            },
                        };
                        match direct {
                            Some(result) => {
                                self.input_summaries.insert((usage, node), result);
                                result
                            }
                            None => {
                                let mut children = Vec::new();
                                self.visit_children(node, |child| children.push(child));
                                frame = InputWork::Next(
                                    node,
                                    children.into_iter(),
                                    Inputs::Known(SetId::EMPTY),
                                );
                                continue;
                            }
                        }
                    }
                }
                InputWork::Next(node, mut children, inputs) => match children.next() {
                    Some(child) => {
                        parents.push((node, children, inputs));
                        frame = InputWork::Visit(child);
                        continue;
                    }
                    None => {
                        self.input_summaries.insert((usage, node), inputs);
                        inputs
                    }
                },
            };
            loop {
                let Some((node, children, inputs)) = parents.pop() else {
                    return Ok(result);
                };
                self.substitution_work.input_visits =
                    self.substitution_work.input_visits.saturating_add(1);
                result = self.combine_inputs(inputs, result)?;
                match result {
                    Inputs::Unknown => {
                        self.input_summaries.insert((usage, node), result);
                    }
                    Inputs::Known(_) => {
                        frame = InputWork::Next(node, children, result);
                        break;
                    }
                }
            }
        }
    }

    pub fn inputs(&mut self, root: NodeId<'g>) -> Result<Option<FxHashSet<usize>>, CapacityError> {
        Ok(match self.input_summary(root, InputUse::Value)? {
            Inputs::Unknown => None,
            Inputs::Known(inputs) => Some(self.input_sets.iter(inputs).collect()),
        })
    }

    pub(crate) fn combine_inputs(
        &mut self,
        left: Inputs<'g>,
        right: Inputs<'g>,
    ) -> Result<Inputs<'g>, CapacityError> {
        Ok(match (left, right) {
            (Inputs::Known(left), Inputs::Known(right)) => {
                Inputs::Known(self.input_sets.combine(Combination::Union, left, right)?)
            }
            (Inputs::Unknown, _) | (_, Inputs::Unknown) => Inputs::Unknown,
        })
    }

    pub(crate) fn project_arguments(
        &mut self,
        inputs: Inputs<'g>,
        arguments: ArgumentContextId<'g>,
    ) -> Result<ArgumentProjection<'g>, CapacityError> {
        let Inputs::Known(inputs) = inputs else {
            return Ok(ArgumentProjection::Full(arguments));
        };
        if let Some(projection) = self.argument_projections.get(&(inputs, arguments)) {
            return Ok(projection);
        }
        self.substitution_work.argument_projections = self
            .substitution_work
            .argument_projections
            .saturating_add(1);
        let mut projection = Sequence::EMPTY;
        for index in self.input_sets.iter(inputs) {
            self.substitution_work.argument_projection_positions = self
                .substitution_work
                .argument_projection_positions
                .saturating_add(1);
            let value = self.expression_sequences.get(arguments.0, index).copied();
            projection = self
                .projected_argument_sequences
                .push(projection, (index, value))?;
        }
        let projection = ArgumentProjection::Relevant(projection);
        self.argument_projections
            .insert((inputs, arguments), projection);
        Ok(projection)
    }

    pub(crate) fn sequence_input_summary(
        &mut self,
        root: InputSequence<'g>,
        usage: InputUse,
    ) -> Result<Inputs<'g>, CapacityError> {
        enum Part<'g> {
            Empty,
            Leaf(NodeId<'g>),
            Branch(InputSequence<'g>, InputSequence<'g>),
        }
        enum Frame<'g> {
            Right(InputSequence<'g>, InputSequence<'g>),
            Join(InputSequence<'g>, Inputs<'g>),
        }
        if let Some(inputs) = self.sequence_input_summaries.get(&(usage, root)) {
            return Ok(inputs);
        }
        let mut parents = Vec::new();
        let mut sequence = root;
        loop {
            self.substitution_work.input_visits =
                self.substitution_work.input_visits.saturating_add(1);
            let mut result = match self.sequence_input_summaries.get(&(usage, sequence)) {
                Some(inputs) => inputs,
                None => {
                    let part = match sequence {
                        InputSequence::Conditions(sequence) => {
                            match self.condition_sequences.parts(sequence)? {
                                crate::sequence::Parts::Empty => Part::Empty,
                                crate::sequence::Parts::Leaf(condition) => {
                                    Part::Leaf(NodeId::Condition(condition))
                                }
                                crate::sequence::Parts::Branch(left, right) => Part::Branch(
                                    InputSequence::Conditions(left),
                                    InputSequence::Conditions(right),
                                ),
                            }
                        }
                        InputSequence::Expressions(sequence) => {
                            match self.expression_sequences.parts(sequence)? {
                                crate::sequence::Parts::Empty => Part::Empty,
                                crate::sequence::Parts::Leaf(expression) => {
                                    Part::Leaf(NodeId::Expr(expression))
                                }
                                crate::sequence::Parts::Branch(left, right) => Part::Branch(
                                    InputSequence::Expressions(left),
                                    InputSequence::Expressions(right),
                                ),
                            }
                        }
                    };
                    let inputs = match part {
                        Part::Empty => Inputs::Known(SetId::EMPTY),
                        Part::Leaf(node) => self.input_summary(node, usage)?,
                        Part::Branch(left, right) => {
                            parents.push(Frame::Right(sequence, right));
                            sequence = left;
                            continue;
                        }
                    };
                    self.sequence_input_summaries
                        .insert((usage, sequence), inputs);
                    inputs
                }
            };
            loop {
                let Some(parent) = parents.pop() else {
                    return Ok(result);
                };
                self.substitution_work.input_visits =
                    self.substitution_work.input_visits.saturating_add(1);
                let completed = match parent {
                    Frame::Right(parent, right) => match result {
                        Inputs::Known(_) => {
                            parents.push(Frame::Join(parent, result));
                            sequence = right;
                            break;
                        }
                        Inputs::Unknown => parent,
                    },
                    Frame::Join(parent, left) => {
                        result = self.combine_inputs(left, result)?;
                        parent
                    }
                };
                self.sequence_input_summaries
                    .insert((usage, completed), result);
            }
        }
    }

    pub fn functions(
        &mut self,
        root: ExprId<'g>,
        functions: &mut FxHashSet<DefId>,
    ) -> Result<(), CapacityError> {
        use std::ops::ControlFlow;
        let summary = fold_children(
            self,
            NodeId::Expr(root),
            |graph, id| {
                if let Some(summary) = graph.function_summaries.get(&id) {
                    return Ok(ControlFlow::Break(summary));
                }
                let mut children = Vec::new();
                let function = match id {
                    NodeId::Choice(_) => {
                        graph.visit_children(id, |child| children.push(child));
                        None
                    }
                    NodeId::Condition(_) => {
                        unreachable!("function provenance follows only values")
                    }
                    NodeId::Expr(value) => match &graph[value] {
                        ExprNode::Function(instance) => Some(graph.values[*instance].def),
                        ExprNode::Closure(def, fields) => {
                            children.extend(
                                graph
                                    .expression_sequences
                                    .iter(*fields)
                                    .copied()
                                    .map(NodeId::Expr),
                            );
                            Some(*def)
                        }
                        ExprNode::Typed(_, value)
                        | ExprNode::Field(value, _)
                        | ExprNode::Element(value, _) => {
                            children.push(NodeId::Expr(*value));
                            None
                        }
                        ExprNode::Aggregate(values) | ExprNode::Variant(_, _, values) => {
                            children.extend(
                                graph
                                    .expression_sequences
                                    .iter(*values)
                                    .copied()
                                    .map(NodeId::Expr),
                            );
                            None
                        }
                        ExprNode::Alternatives(root) => {
                            children.extend(root.map(NodeId::Choice));
                            None
                        }
                        ExprNode::Select(_, yes, no) => {
                            children.extend([NodeId::Expr(*yes), NodeId::Expr(*no)]);
                            None
                        }
                        ExprNode::Serialized { .. }
                        | ExprNode::Unknown
                        | ExprNode::Opaque(_)
                        | ExprNode::Global(_)
                        | ExprNode::Argument(_)
                        | ExprNode::Number(_)
                        | ExprNode::Range(_)
                        | ExprNode::Text(_)
                        | ExprNode::Length(_)
                        | ExprNode::Trimmed(_)
                        | ExprNode::Found { .. }
                        | ExprNode::MatchIndex { .. }
                        | ExprNode::Matches { .. }
                        | ExprNode::MatchEntry(_)
                        | ExprNode::Tokens { .. }
                        | ExprNode::Token(_)
                        | ExprNode::NextToken(_)
                        | ExprNode::Cursor { .. }
                        | ExprNode::Partition { .. }
                        | ExprNode::Slice { .. }
                        | ExprNode::Arithmetic(..)
                        | ExprNode::Call(..)
                        | ExprNode::Test(_) => None,
                    },
                };
                Ok(ControlFlow::Continue((function, children)))
            },
            |graph, id, function, children| {
                let mut summary = match function {
                    Some(function) => graph.function_sets.insert(SetId::EMPTY, function)?,
                    None => SetId::EMPTY,
                };
                for child in children {
                    summary = graph
                        .function_sets
                        .combine(Combination::Union, summary, child)?;
                }
                graph.function_summaries.insert(id, summary);
                Ok(summary)
            },
        )?;
        functions.extend(self.function_sets.iter(summary));
        Ok(())
    }

    pub fn serialization(&self, mut id: ExprId<'g>) -> Option<ExprId<'g>> {
        loop {
            match &self[id] {
                ExprNode::Serialized { .. } => return Some(id),
                ExprNode::Aggregate(fields) if self.expression_sequences.len(*fields) == 1 => {
                    let Some(field) = self.expression_sequences.get(*fields, 0) else {
                        unreachable!("a singleton has one value")
                    };
                    id = *field;
                }
                _ => return None,
            }
        }
    }

    pub fn location(&self, mut id: ExprId<'g>) -> Option<(ExprId<'g>, Vec<usize>)> {
        let mut fields = Vec::new();
        while let ExprNode::Field(parent, field) = &self[id] {
            fields.push(*field);
            id = *parent;
        }
        match &self[id] {
            ExprNode::Argument(_) => {
                fields.reverse();
                Some((id, fields))
            }
            ExprNode::Opaque(origin) if let Some(_) = self.values[*origin].identity => {
                fields.reverse();
                Some((id, fields))
            }
            _ => None,
        }
    }

    pub fn substitute_guards(
        &mut self,
        guards: &Sequence<'g, ConditionId<'g>>,
        arguments: &Sequence<'g, ExprId<'g>>,
        scope: &Invocation<'g>,
    ) -> Result<Sequence<'g, ConditionId<'g>>, CapacityError> {
        let inputs = self
            .sequence_input_summary(InputSequence::Conditions(*guards), InputUse::Substitution)?;
        let prepared = self.prepare_rewrite(Rewrite::Substitute(arguments, scope), inputs)?;
        let context = prepared.context;
        let mut mapped = self.rewritten_guard_sequences.share();
        mapped.apply(
            self,
            |graph| &mut graph.condition_sequences,
            *guards,
            context,
            |graph, guard| graph.rewrite_condition(*guard, &prepared),
        )
    }

    pub fn substitute_arguments(
        &mut self,
        values: &Sequence<'g, ExprId<'g>>,
        arguments: &Sequence<'g, ExprId<'g>>,
        scope: &Invocation<'g>,
    ) -> Result<Sequence<'g, ExprId<'g>>, CapacityError> {
        let inputs = self
            .sequence_input_summary(InputSequence::Expressions(*values), InputUse::Substitution)?;
        let prepared = self.prepare_rewrite(Rewrite::Substitute(arguments, scope), inputs)?;
        let context = prepared.context;
        let mut mapped = self.rewritten_argument_sequences.share();
        mapped.apply(
            self,
            |graph| &mut graph.expression_sequences,
            *values,
            context,
            |graph, value| graph.rewrite_expression(*value, &prepared),
        )
    }

    pub fn substitute_expr(
        &mut self,
        id: ExprId<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
        scope: &Invocation<'g>,
    ) -> Result<ExprId<'g>, CapacityError> {
        let inputs = self.input_summary(NodeId::Expr(id), InputUse::Substitution)?;
        let prepared = self.prepare_rewrite(Rewrite::Substitute(arguments, scope), inputs)?;
        self.rewrite_expression(id, &prepared)
    }

    pub fn substitute_condition(
        &mut self,
        id: ConditionId<'g>,
        arguments: &Sequence<'g, ExprId<'g>>,
        scope: &Invocation<'g>,
    ) -> Result<ConditionId<'g>, CapacityError> {
        let inputs = self.input_summary(NodeId::Condition(id), InputUse::Substitution)?;
        let prepared = self.prepare_rewrite(Rewrite::Substitute(arguments, scope), inputs)?;
        self.rewrite_condition(id, &prepared)
    }

    pub fn intern_affected(
        &mut self,
        nodes: impl IntoIterator<Item = NodeId<'g>>,
    ) -> Result<Affected<'g>, CapacityError> {
        let mut affected = SetId::EMPTY;
        for node in nodes {
            affected = self.reference_sets.insert(affected, node)?;
        }
        Ok(affected)
    }

    pub fn invalidate_expr(
        &mut self,
        id: ExprId<'g>,
        change: GraphInvalidation<'g>,
        affected: Affected<'g>,
    ) -> Result<ExprId<'g>, CapacityError> {
        let result = match self.prepare_invalidation(NodeId::Expr(id), change, affected)? {
            Some(prepared) => self.rewrite_expression(id, &prepared)?,
            None => id,
        };
        Ok(result)
    }

    pub fn invalidate_condition(
        &mut self,
        id: ConditionId<'g>,
        change: GraphInvalidation<'g>,
        affected: Affected<'g>,
    ) -> Result<ConditionId<'g>, CapacityError> {
        let result = match self.prepare_invalidation(NodeId::Condition(id), change, affected)? {
            Some(prepared) => self.rewrite_condition(id, &prepared)?,
            None => id,
        };
        Ok(result)
    }

    pub fn provenance(&mut self, id: ExprId<'g>) -> Result<ExprId<'g>, CapacityError> {
        let prepared = self.prepare_rewrite(Rewrite::Provenance, Inputs::Unknown)?;
        self.rewrite_expression(id, &prepared)
    }

    fn prepare_invalidation<'a>(
        &mut self,
        root: NodeId<'g>,
        change: GraphInvalidation<'g>,
        affected: Affected<'g>,
    ) -> Result<Option<PreparedRewrite<'a, 'g>>, CapacityError> {
        match self.reference_sets.contains(affected, root) {
            Some(()) => self
                .prepare_rewrite(Rewrite::Invalidate(change, affected), Inputs::Unknown)
                .map(Some),
            None => Ok(None),
        }
    }

    fn prepare_rewrite<'a>(
        &mut self,
        operation: Rewrite<'a, 'g>,
        inputs: Inputs<'g>,
    ) -> Result<PreparedRewrite<'a, 'g>, CapacityError> {
        let key = match &operation {
            Rewrite::Substitute(arguments, scope) => RewriteKey::Substitute {
                arguments: {
                    let arguments = ArgumentContextId::from(**arguments);
                    self.project_arguments(inputs, arguments)?
                },
                scope: (*scope).clone(),
            },
            Rewrite::Invalidate(change, affected) => RewriteKey::Invalidate(*change, *affected),
            Rewrite::Provenance => RewriteKey::Provenance,
        };
        let context = self.rewrites.intern(key, CapacityError::RewriteContexts)?;
        let prepared = PreparedRewrite { context, operation };
        Ok(prepared)
    }

    fn rewrite_expression(
        &mut self,
        id: ExprId<'g>,
        prepared: &PreparedRewrite<'_, 'g>,
    ) -> Result<ExprId<'g>, CapacityError> {
        self.rewrite(prepared, id, |graph| {
            graph
                .rewritten_expressions
                .get(&(prepared.context, id))
                .ok_or(NodeId::Expr(id))
        })
    }

    fn rewrite_condition(
        &mut self,
        id: ConditionId<'g>,
        prepared: &PreparedRewrite<'_, 'g>,
    ) -> Result<ConditionId<'g>, CapacityError> {
        self.rewrite(prepared, id, |graph| {
            graph
                .rewritten_conditions
                .get(&(prepared.context, id))
                .ok_or(NodeId::Condition(id))
        })
    }

    fn rewrite<R>(
        &mut self,
        prepared: &PreparedRewrite<'_, 'g>,
        unchanged: R,
        root: impl Fn(&Self) -> Result<R, NodeId<'g>>,
    ) -> Result<R, CapacityError> {
        let operation = prepared.operation;
        let mut pending = Vec::new();
        loop {
            let frame = match pending.pop() {
                Some(frame) => frame,
                None => match root(self) {
                    Ok(result) => return Ok(result),
                    Err(root) => Frame::Visit(root),
                },
            };
            if let Rewrite::Invalidate(_, affected) = operation {
                let node = match frame {
                    Frame::Visit(node) | Frame::Build(node) => node,
                };
                if let None = self.reference_sets.contains(affected, node) {
                    if pending.is_empty() {
                        return Ok(unchanged);
                    }
                    continue;
                }
            }
            match self.rewrite_step(frame, prepared, &mut pending) {
                Ok(()) => {}
                Err(Demand::Child(child)) => pending.extend([frame, Frame::Visit(child)]),
                Err(Demand::Children(children)) => {
                    pending.push(frame);
                    pending.extend(children.into_iter().rev().map(Frame::Visit));
                }
                Err(Demand::Capacity(error)) => return Err(error),
            }
        }
    }

    fn rewrite_step(
        &mut self,
        frame: Frame<'g>,
        prepared: &PreparedRewrite<'_, 'g>,
        pending: &mut Vec<Frame<'g>>,
    ) -> Result<(), Demand<NodeId<'g>>> {
        let PreparedRewrite { context, operation } = *prepared;
        match frame {
            Frame::Visit(NodeId::Expr(id)) => {
                if self.rewritten_expressions.get(&(context, id)).is_some() {
                    return Ok(());
                }
                if let Rewrite::Invalidate(change, _) = operation {
                    let replacement = match change {
                        GraphInvalidation::Local(_) => None,
                        GraphInvalidation::Memory(target) => Some((target, None)),
                        GraphInvalidation::Replace { target, value } => Some((target, Some(value))),
                    };
                    if let Some((target, value)) = replacement
                        && let (Some((base, fields)), Some((written, path))) =
                            (self.location(id), self.location(target))
                    {
                        let mut result = id;
                        if base == written
                            && fields.iter().zip(&path).all(|(left, right)| left == right)
                        {
                            result = match (value, fields.strip_prefix(path.as_slice())) {
                                (Some(mut value), Some(suffix)) => {
                                    for field in suffix {
                                        value = self.field(value, *field)?;
                                    }
                                    value
                                }
                                _ => self.intern_expr(ExprNode::Unknown)?,
                            };
                        }
                        self.rewritten_expressions.insert((context, id), result);
                        return Ok(());
                    }
                }
                pending.push(Frame::Build(NodeId::Expr(id)));
                let mut children = Vec::new();
                let mut conditions = Vec::new();
                self.visit_children(NodeId::Expr(id), |child| match child {
                    NodeId::Expr(_) | NodeId::Choice(_) => children.push(child),
                    NodeId::Condition(_) => conditions.push(child),
                });
                pending.extend(conditions.into_iter().rev().map(Frame::Visit));
                pending.extend(children.into_iter().rev().map(Frame::Visit));
            }
            Frame::Visit(NodeId::Condition(id)) => {
                if self.rewritten_conditions.get(&(context, id)).is_some() {
                    return Ok(());
                }
                pending.push(Frame::Build(NodeId::Condition(id)));
                let mut children = Vec::new();
                self.visit_children(NodeId::Condition(id), |child| children.push(child));
                pending.extend(children.into_iter().rev().map(Frame::Visit));
            }
            Frame::Visit(NodeId::Choice(id)) => {
                if self.rewritten_choices.get(&(context, id)).is_some() {
                    return Ok(());
                }
                pending.push(Frame::Build(NodeId::Choice(id)));
                let mut children = Vec::new();
                self.visit_children(NodeId::Choice(id), |child| children.push(child));
                pending.extend(children.into_iter().rev().map(Frame::Visit));
            }
            Frame::Build(NodeId::Choice(id)) => {
                self.substitution_work.rewritten_nodes =
                    self.substitution_work.rewritten_nodes.saturating_add(1);
                let result = match self[id].node {
                    ChoiceNode::Value(value) => {
                        let value = self.rewritten_expr(prepared, value)?;
                        self.intern_choice(ChoiceNode::Value(value))?
                    }
                    ChoiceNode::Branch(left, right) => {
                        match (
                            self.rewritten_choice(prepared, left)?,
                            self.rewritten_choice(prepared, right)?,
                        ) {
                            (Some(left), Some(right)) => Some(self.choices.join(
                                &mut self.expression_sequences,
                                left,
                                right,
                            )?),
                            (None, other) | (other, None) => other,
                        }
                    }
                };
                self.rewritten_choices.insert((context, id), result);
            }
            Frame::Build(NodeId::Expr(id)) => {
                self.substitution_work.rewritten_nodes =
                    self.substitution_work.rewritten_nodes.saturating_add(1);
                let node = self.rewrite_expr_node(prepared, self[id].clone())?;
                let result = match operation {
                    Rewrite::Substitute(arguments, scope) => match node {
                        ExprNode::Argument(index) => {
                            match self.expression_sequences.get(*arguments, index) {
                                Some(value) => *value,
                                None => self.intern_expr(ExprNode::Unknown)?,
                            }
                        }
                        ExprNode::Function(instance) => {
                            let instance =
                                self.values.substitute_instance(instance, scope.generics)?;
                            self.intern_expr(ExprNode::Function(instance))?
                        }
                        ExprNode::Global(instance) => {
                            let instance =
                                self.values.substitute_instance(instance, scope.generics)?;
                            self.intern_expr(ExprNode::Global(instance))?
                        }
                        ExprNode::Typed(ty, value) => {
                            let ty = self.values.substitute_type(ty, scope.generics)?;
                            self.typed(ty, value)?
                        }
                        node @ (ExprNode::Test(test) | ExprNode::Select(test, _, _)) => {
                            // Resolve concrete branch selectors before a surrounding
                            // return guard can request an unreachable recursive call.
                            let outcome = match self[test] {
                                ConditionNode::Variant(value, _)
                                | ConditionNode::NotVariant(value, _)
                                    if let ExprNode::Variant(_, _, fields) = self[value]
                                        && fields == Sequence::EMPTY =>
                                {
                                    self.truth(test, &Sequence::EMPTY)?
                                }
                                ConditionNode::Compare(_, left, right)
                                    if let (ExprNode::Number(_), ExprNode::Number(_)) =
                                        (&self[left], &self[right]) =>
                                {
                                    self.truth(test, &Sequence::EMPTY)?
                                }
                                _ => Truth::Unknown(ProofGap::Value),
                            };
                            match (node, outcome) {
                                (ExprNode::Test(_), Truth::Proven) => {
                                    self.intern_expr(ExprNode::Number(1))?
                                }
                                (ExprNode::Test(_), Truth::Refuted) => {
                                    self.intern_expr(ExprNode::Number(0))?
                                }
                                (ExprNode::Select(_, yes, _), Truth::Proven) => yes,
                                (ExprNode::Select(_, _, no), Truth::Refuted) => no,
                                (node, _) => self.intern_expr(node)?,
                            }
                        }
                        ExprNode::Field(value, index) => self.field(value, index)?,
                        ExprNode::Cursor { .. } => match scope.relocation {
                            Relocation::Preserve => id,
                            Relocation::Into(_) => self.intern_expr(ExprNode::Unknown)?,
                        },
                        ExprNode::Opaque(origin) => {
                            let origin = self.values.substitute_origin(origin, scope)?;
                            self.intern_expr(ExprNode::Opaque(origin))?
                        }
                        ExprNode::Call(target, arguments, origin) => {
                            let target = match target {
                                TargetNode::Direct(instance) => TargetNode::Direct(
                                    self.values.substitute_instance(instance, scope.generics)?,
                                ),
                                target @ TargetNode::Indirect(_) => target,
                            };
                            let origin = origin
                                .map(|origin| self.values.substitute_origin(origin, scope))
                                .transpose()?;
                            self.intern_expr(ExprNode::Call(target, arguments, origin))?
                        }
                        node => self.intern_expr(node)?,
                    },
                    Rewrite::Invalidate(change, _) => {
                        let mut node = node;
                        if let GraphInvalidation::Local(local) = change {
                            match &mut node {
                                ExprNode::Opaque(origin) | ExprNode::Call(_, _, Some(origin)) => {
                                    *origin =
                                        self.values.invalidate_origin_local(*origin, local)?;
                                }
                                ExprNode::Cursor { local: origin, .. } if *origin == local => {
                                    node = ExprNode::Unknown
                                }
                                _ => {}
                            }
                        }
                        self.intern_expr(node)?
                    }
                    Rewrite::Provenance => {
                        match node {
                            ExprNode::Function(_) => id,
                            ExprNode::Typed(ty, value) => self.typed(ty, value)?,
                            ExprNode::Closure(def, fields) => {
                                self.intern_expr(ExprNode::Closure(def, fields))?
                            }
                            node @ (ExprNode::Aggregate(_) | ExprNode::Variant(..)) => {
                                let fields = match &node {
                                    ExprNode::Aggregate(fields)
                                    | ExprNode::Variant(_, _, fields) => fields,
                                    _ => unreachable!("aggregate provenance"),
                                };
                                match self.expression_sequences.iter(*fields).find(|field| {
                                    match &self[**field] {
                                        ExprNode::Unknown => false,
                                        _ => true,
                                    }
                                }) {
                                    Some(_) => self.intern_expr(node)?,
                                    None => self.intern_expr(ExprNode::Unknown)?,
                                }
                            }
                            ExprNode::Alternatives(root) => match root {
                                None => self.intern_expr(ExprNode::Unknown)?,
                                Some(_) => self.intern_expr(ExprNode::Alternatives(root))?,
                            },
                            ExprNode::Select(_, yes, no) => {
                                let unknown = self.intern_condition(ConditionNode::Unknown)?;
                                self.intern_expr(ExprNode::Select(unknown, yes, no))?
                            }
                            ExprNode::Field(value, index) => self.field(value, index)?,
                            ExprNode::Element(value, _) => match &self[value] {
                                ExprNode::Unknown => value,
                                _ => {
                                    let unknown = self.intern_expr(ExprNode::Unknown)?;
                                    self.intern_expr(ExprNode::Element(value, unknown))?
                                }
                            },
                            _ => self.intern_expr(ExprNode::Unknown)?,
                        }
                    }
                };
                self.rewritten_expressions.insert((context, id), result);
            }
            Frame::Build(NodeId::Condition(id)) => {
                self.substitution_work.rewritten_nodes =
                    self.substitution_work.rewritten_nodes.saturating_add(1);
                let mut node = self.rewrite_condition_node(prepared, self[id].clone())?;
                if let Rewrite::Substitute(_, scope) = operation
                    && let ConditionNode::Returned(TargetNode::Direct(instance), _) = &mut node
                {
                    *instance = self.values.substitute_instance(*instance, scope.generics)?;
                }
                let result = self.intern_condition(node)?;
                self.rewritten_conditions.insert((context, id), result);
            }
        }
        Ok(())
    }

    fn parameter_class(
        &mut self,
        root: ParameterNode<'g>,
        provenance: &PreparedRewrite<'_, 'g>,
    ) -> Result<Parameter, CapacityError> {
        use std::ops::ControlFlow;
        fold_children(
            self,
            root,
            |graph, node| {
                let mut children = Vec::new();
                let mut captures = Captures::None;
                match node {
                    ParameterNode::Choice(id) => {
                        if let Some(class) = graph.choice_parameters.get(&id) {
                            return Ok(ControlFlow::Break(class));
                        }
                        match graph[id].node {
                            ChoiceNode::Value(value) => children.push(ParameterNode::Expr(value)),
                            ChoiceNode::Branch(left, right) => children.extend([
                                ParameterNode::Choice(left),
                                ParameterNode::Choice(right),
                            ]),
                        }
                    }
                    ParameterNode::Expr(id) => {
                        if let Some(class) = graph.parameters.get(&id) {
                            return Ok(ControlFlow::Break(class));
                        }
                        let origin = graph.rewrite_expression(id, provenance)?;
                        let binding = match (&graph[origin], &graph[id]) {
                            (ExprNode::Unknown, _) => Some(Binding::Value),
                            (_, ExprNode::Function(_)) => Some(Binding::Independent),
                            (_, ExprNode::Typed(_, value)) => {
                                children.push(ParameterNode::Expr(*value));
                                None
                            }
                            (
                                _,
                                ExprNode::Closure(_, fields)
                                | ExprNode::Aggregate(fields)
                                | ExprNode::Variant(_, _, fields),
                            ) => {
                                children.extend(
                                    graph
                                        .expression_sequences
                                        .iter(*fields)
                                        .copied()
                                        .map(ParameterNode::Expr),
                                );
                                None
                            }
                            (_, ExprNode::Alternatives(root)) => {
                                children.extend(root.map(ParameterNode::Choice));
                                None
                            }
                            (_, ExprNode::Select(_, yes, no)) => {
                                captures = Captures::Present;
                                children
                                    .extend([ParameterNode::Expr(*yes), ParameterNode::Expr(*no)]);
                                None
                            }
                            _ => Some(Binding::Value),
                        };
                        if let Some(binding) = binding {
                            let class = Parameter { binding, captures };
                            graph.parameters.insert(id, class);
                            return Ok(ControlFlow::Break(class));
                        }
                    }
                }
                Ok(ControlFlow::Continue((captures, children)))
            },
            |graph, node, mut captures, children| {
                let mut binding = Binding::Independent;
                for class in children {
                    match class.binding {
                        Binding::Value | Binding::Dependent => binding = Binding::Dependent,
                        Binding::Independent => {}
                    }
                    if let Captures::Present = class.captures {
                        captures = Captures::Present;
                    }
                }
                let class = Parameter { binding, captures };
                match node {
                    ParameterNode::Expr(id) => {
                        graph.parameters.insert(id, class);
                    }
                    ParameterNode::Choice(id) => {
                        graph.choice_parameters.insert(id, class);
                    }
                }
                Ok(class)
            },
        )
    }

    pub fn parameter(
        &mut self,
        root: ExprId<'g>,
        binding: ExprId<'g>,
        values: &mut Sequence<'g, ExprId<'g>>,
    ) -> Result<ExprId<'g>, CapacityError> {
        use crate::memo::{Demand, resolve};
        #[derive(Clone, Copy)]
        enum Task<'g> {
            Expr(Bound<'g, ExprId<'g>>),
            Choice(Bound<'g, ChoiceId<'g>>),
        }
        struct State<'g> {
            values: Sequence<'g, ExprId<'g>>,
            expressions: FxHashMap<(ExprId<'g>, Option<ExprId<'g>>), ExprId<'g>>,
            choices: FxHashMap<(ChoiceId<'g>, Option<ExprId<'g>>), Option<ChoiceId<'g>>>,
            // A select captures its test before visiting its arms, once per application.
            tests: FxHashMap<(ExprId<'g>, Option<ExprId<'g>>), ConditionId<'g>>,
        }
        impl<'g> State<'g> {
            fn expression(
                &self,
                input: Bound<'g, ExprId<'g>>,
                cached: &Memo<(ExprId<'g>, Option<ExprId<'g>>), ExprId<'g>>,
            ) -> Option<ExprId<'g>> {
                let key = input.key();
                self.expressions
                    .get(&key)
                    .copied()
                    .or_else(|| cached.get(&key))
            }
            fn choice(
                &self,
                input: Bound<'g, ChoiceId<'g>>,
                cached: &Memo<(ChoiceId<'g>, Option<ExprId<'g>>), Option<ChoiceId<'g>>>,
            ) -> Option<Option<ChoiceId<'g>>> {
                let key = input.key();
                self.choices.get(&key).copied().or_else(|| cached.get(&key))
            }
        }
        let provenance = self.prepare_rewrite(Rewrite::Provenance, Inputs::Unknown)?;
        let root = Bound {
            id: root,
            supplied: binding,
            class: self.parameter_class(ParameterNode::Expr(root), &provenance)?,
        };
        let mut state = State {
            values: *values,
            expressions: FxHashMap::default(),
            choices: FxHashMap::default(),
            tests: FxHashMap::default(),
        };
        let result = resolve(
            &mut (&mut *self, &mut state),
            |(graph, state)| {
                state
                    .expression(root, &graph.parameter_values)
                    .ok_or(Task::Expr(root))
            },
            |(graph, state), task| {
                let expr = |graph: &mut Graph<'g>, state: &State<'g>, id, supplied| {
                    let class = graph.parameter_class(ParameterNode::Expr(id), &provenance)?;
                    let input = Bound {
                        id,
                        supplied,
                        class,
                    };
                    state
                        .expression(input, &graph.parameter_values)
                        .ok_or(Demand::Child(Task::Expr(input)))
                };
                let choice = |graph: &mut Graph<'g>, state: &State<'g>, id, supplied| {
                    let class = graph.parameter_class(ParameterNode::Choice(id), &provenance)?;
                    let input = Bound {
                        id,
                        supplied,
                        class,
                    };
                    state
                        .choice(input, &graph.parameter_choice_values)
                        .ok_or(Demand::Child(Task::Choice(input)))
                };
                match task {
                    Task::Expr(input) => {
                        if state.expressions.contains_key(&input.key()) {
                            return Ok(());
                        }
                        if let Some(completed) = graph.parameter_values.get(&input.key()) {
                            state.expressions.insert(input.key(), completed);
                            return Ok(());
                        }
                        let key = input.key();
                        if let Binding::Value = input.class.binding {
                            state.expressions.insert(key, input.supplied);
                            return Ok(());
                        }
                        let result = match graph[input.id].clone() {
                            ExprNode::Function(_) => {
                                state.expressions.insert(key, input.id);
                                return Ok(());
                            }
                            ExprNode::Typed(ty, value) => {
                                let value = expr(graph, state, value, input.supplied)?;
                                graph.typed(ty, value)?
                            }
                            mut node @ (ExprNode::Closure(..)
                            | ExprNode::Aggregate(..)
                            | ExprNode::Variant(..)) => {
                                let fields = match &mut node {
                                    ExprNode::Closure(_, fields)
                                    | ExprNode::Aggregate(fields)
                                    | ExprNode::Variant(_, _, fields) => fields,
                                    _ => unreachable!("an aggregate owns fields"),
                                };
                                let reader = graph.expression_sequences.share();
                                let children = reader.iter(*fields).copied().enumerate();
                                let mut mapped = Vec::with_capacity(children.len());
                                let mut missing = Vec::new();
                                for (index, id) in children {
                                    let class = graph
                                        .parameter_class(ParameterNode::Expr(id), &provenance)?;
                                    let supplied = match class.binding {
                                        Binding::Independent => input.supplied,
                                        Binding::Value | Binding::Dependent => graph
                                            .intern_expr(ExprNode::Field(input.supplied, index))?,
                                    };
                                    let child = Bound {
                                        id,
                                        supplied,
                                        class,
                                    };
                                    match state.expression(child, &graph.parameter_values) {
                                        Some(value) => mapped.push(value),
                                        None => missing.push(Task::Expr(child)),
                                    }
                                }
                                if !missing.is_empty() {
                                    return Err(Demand::Children(missing));
                                }
                                *fields = graph.expression_sequences.from_iter(mapped)?;
                                graph.intern_expr(node)?
                            }
                            ExprNode::Alternatives(root) => {
                                let root = match root {
                                    Some(id) => choice(graph, state, id, input.supplied)?,
                                    None => None,
                                };
                                graph.intern_expr(ExprNode::Alternatives(root))?
                            }
                            ExprNode::Select(test, yes, no) => {
                                let test = match state.tests.entry(key) {
                                    std::collections::hash_map::Entry::Occupied(entry) => {
                                        *entry.get()
                                    }
                                    std::collections::hash_map::Entry::Vacant(entry) => {
                                        let index = graph.expression_sequences.len(state.values);
                                        let test = graph.intern_expr(ExprNode::Test(test))?;
                                        state.values =
                                            graph.expression_sequences.push(state.values, test)?;
                                        let argument =
                                            graph.intern_expr(ExprNode::Argument(index))?;
                                        *entry.insert(graph.from_expr(argument, 1)?)
                                    }
                                };
                                let yes = expr(graph, state, yes, input.supplied)?;
                                let no = expr(graph, state, no, input.supplied)?;
                                graph.intern_expr(ExprNode::Select(test, yes, no))?
                            }
                            _ => unreachable!(
                                "parameter classification retains only structural nodes"
                            ),
                        };
                        if let Captures::None = input.class.captures {
                            graph.parameter_values.insert(key, result);
                        }
                        state.expressions.insert(key, result);
                    }
                    Task::Choice(input) => {
                        if state.choices.contains_key(&input.key()) {
                            return Ok(());
                        }
                        if let Some(completed) = graph.parameter_choice_values.get(&input.key()) {
                            state.choices.insert(input.key(), completed);
                            return Ok(());
                        }
                        let result = match graph[input.id].node {
                            ChoiceNode::Value(value) => {
                                let value = expr(graph, state, value, input.supplied)?;
                                graph.intern_choice(ChoiceNode::Value(value))?
                            }
                            ChoiceNode::Branch(left, right) => {
                                match (
                                    choice(graph, state, left, input.supplied)?,
                                    choice(graph, state, right, input.supplied)?,
                                ) {
                                    (Some(left), Some(right)) => Some(graph.choices.join(
                                        &mut graph.expression_sequences,
                                        left,
                                        right,
                                    )?),
                                    (None, other) | (other, None) => other,
                                }
                            }
                        };
                        let key = input.key();
                        if let Captures::None = input.class.captures {
                            graph.parameter_choice_values.insert(key, result);
                        }
                        state.choices.insert(key, result);
                    }
                }
                Ok(())
            },
        )?;
        *values = state.values;
        Ok(result)
    }

    fn matched_text(&self, index: ExprId<'g>) -> Option<ExprId<'g>> {
        match &self[index] {
            ExprNode::MatchIndex { text, pattern, .. } => {
                self.known(NodeId::Expr(*text))?;
                self.known(NodeId::Expr(*pattern))?;
                Some(*text)
            }
            ExprNode::Arithmetic(Arithmetic::Add(rustc_middle::ty::UintTy::Usize), left, right) => {
                self.match_end_text(*left, *right)
            }
            _ => None,
        }
    }

    pub(crate) fn match_end_text(&self, left: ExprId<'g>, right: ExprId<'g>) -> Option<ExprId<'g>> {
        let (text, pattern, width_of) = match (&self[left], &self[right]) {
            (ExprNode::MatchIndex { text, pattern, .. }, ExprNode::Length(width_of))
            | (ExprNode::Length(width_of), ExprNode::MatchIndex { text, pattern, .. }) => {
                (text, pattern, width_of)
            }
            _ => return None,
        };
        if pattern != width_of {
            return None;
        }
        self.known(NodeId::Expr(*text))?;
        self.known(NodeId::Expr(*pattern))?;
        Some(*text)
    }

    fn references(
        &mut self,
        root: NodeId<'g>,
        targets: SetId<'g, NodeId<'g>>,
    ) -> Result<SetId<'g, NodeId<'g>>, CapacityError> {
        if targets == SetId::EMPTY {
            return Ok(SetId::EMPTY);
        }
        use std::ops::ControlFlow;
        let references = fold_children(
            self,
            root,
            |graph, node| {
                if let Some(summary) = graph.reference_summaries.get(&node) {
                    return Ok(ControlFlow::Break(summary));
                }
                let mut children = Vec::new();
                graph.visit_children(node, |child| children.push(child));
                children.reverse();
                Ok(ControlFlow::Continue(((), children)))
            },
            |graph, node, (), children| {
                graph.proof_work.reference_nodes =
                    graph.proof_work.reference_nodes.saturating_add(1);
                let mut result = graph.reference_sets.insert(SetId::EMPTY, node)?;
                let children = children.into_iter().rev();
                for child in children {
                    result = graph
                        .reference_sets
                        .combine(Combination::Union, result, child)?;
                }
                graph.reference_summaries.insert(node, result);
                Ok(result)
            },
        )?;
        self.reference_sets
            .combine(Combination::Intersection, references, targets)
    }

    /// Retains the first path's order and multiplicity for facts common to every path.
    pub fn common_guards(
        &mut self,
        paths: &[Sequence<'g, ConditionId<'g>>],
    ) -> Result<Sequence<'g, ConditionId<'g>>, CapacityError> {
        let Some((first, rest)) = paths.split_first() else {
            return Ok(Sequence::EMPTY);
        };
        let mut common = self.guard_membership(GuardContextId(*first))?;
        for path in rest {
            if common == SetId::EMPTY {
                return Ok(Sequence::EMPTY);
            }
            let other = self.guard_membership(GuardContextId(*path))?;
            common = self
                .guard_member_sets
                .combine(Combination::Intersection, common, other)?;
        }
        if common == SetId::EMPTY {
            return Ok(Sequence::EMPTY);
        }
        self.guard_members.edit(
            &mut self.condition_sequences,
            *first,
            &mut self.guard_intersections,
            common,
            &mut self.guard_member_sets,
            |sets, _, part| sets.members(part),
            |sets, _, members, common| {
                let retained = sets.combine(Combination::Intersection, *members, *common)?;
                Ok(if retained == SetId::EMPTY {
                    crate::sequence::Selection::Drop
                } else if retained == *members {
                    crate::sequence::Selection::Keep
                } else {
                    crate::sequence::Selection::Visit
                })
            },
            |sets, _, value, common| Ok(sets.contains(*common, *value).map(|()| *value)),
        )
    }

    fn shared_endpoints(
        &mut self,
        guards: GuardContextId<'g>,
    ) -> Result<SetId<'g, NodeId<'g>>, CapacityError> {
        let sequence = guards.0;
        let mut summaries = std::mem::take(&mut self.guard_endpoints);
        let result = summaries.fold(
            self,
            |graph| &graph.condition_sequences,
            sequence,
            |graph, part| match part {
                crate::sequence::Part::Leaf(guard) => {
                    let mut endpoints = Vec::new();
                    graph.visit_children(NodeId::Condition(*guard), |child| {
                        if let NodeId::Expr(expression) = child {
                            endpoints.push(NodeId::Expr(expression));
                        }
                    });
                    let mut seen = SetId::EMPTY;
                    let mut shared = SetId::EMPTY;
                    for endpoint in endpoints {
                        if let Some(()) = graph.reference_sets.contains(seen, endpoint) {
                            shared = graph.reference_sets.insert(shared, endpoint)?;
                        }
                        seen = graph.reference_sets.insert(seen, endpoint)?;
                    }
                    Ok(GuardEndpoints { seen, shared })
                }
                crate::sequence::Part::Branch(left, right) => {
                    let overlap = graph.reference_sets.combine(
                        Combination::Intersection,
                        left.seen,
                        right.seen,
                    )?;
                    let shared = graph.reference_sets.combine(
                        Combination::Union,
                        left.shared,
                        right.shared,
                    )?;
                    let shared =
                        graph
                            .reference_sets
                            .combine(Combination::Union, shared, overlap)?;
                    let seen =
                        graph
                            .reference_sets
                            .combine(Combination::Union, left.seen, right.seen)?;
                    Ok::<_, CapacityError>(GuardEndpoints { seen, shared })
                }
            },
        );
        self.guard_endpoints = summaries;
        Ok(result?.map(|summary| summary.shared).unwrap_or_default())
    }

    fn prepare_guards(
        &mut self,
        guards: GuardContextId<'g>,
    ) -> Result<PreparedGuards<'g>, CapacityError> {
        if let Some(prepared) = self.prepared_guards.get(&guards) {
            return Ok(prepared);
        }
        let sequence = guards.0;
        let mut classifications = std::mem::take(&mut self.guard_classifications);
        let classified = classifications.fold(
            self,
            |graph| &graph.condition_sequences,
            sequence,
            |graph, part| {
                use crate::sequence::Part;
                use GuardClassification::{Common, Mixed};
                Ok::<_, CapacityError>(match part {
                    Part::Leaf(guard) => {
                        if let None = graph.known(NodeId::Condition(*guard)) {
                            Common(Sequence::EMPTY)
                        } else {
                            let target = match graph[*guard] {
                                ConditionNode::Returned(..) => Some(NodeId::Condition(*guard)),
                                ConditionNode::Variant(value, _)
                                | ConditionNode::NotVariant(value, _) => Some(NodeId::Expr(value)),
                                ConditionNode::Boundary(text, _)
                                | ConditionNode::NotBoundary(text, _) => Some(NodeId::Expr(text)),
                                ConditionNode::Compare(
                                    Order::Equal | Order::NotEqual,
                                    left,
                                    right,
                                ) => match (&graph[left], &graph[right]) {
                                    (
                                        ExprNode::Select(..) | ExprNode::Test(_),
                                        ExprNode::Number(0 | 1),
                                    ) => Some(NodeId::Expr(left)),
                                    (
                                        ExprNode::Number(0 | 1),
                                        ExprNode::Select(..) | ExprNode::Test(_),
                                    ) => Some(NodeId::Expr(right)),
                                    _ => None,
                                },
                                _ => None,
                            };
                            match target {
                                Some(target) => Mixed {
                                    segments: graph.guard_segments.push(
                                        Sequence::EMPTY,
                                        GuardSegment::Relevant(*guard, target),
                                    )?,
                                    targets: graph.reference_sets.insert(SetId::EMPTY, target)?,
                                },
                                None => {
                                    Common(graph.condition_sequences.push(Sequence::EMPTY, *guard)?)
                                }
                            }
                        }
                    }
                    Part::Branch(Common(left), Common(right)) => {
                        Common(graph.condition_sequences.append(*left, *right)?)
                    }
                    Part::Branch(left, right) => {
                        let mut segments =
                            |part: &GuardClassification<'g>| -> Result<_, CapacityError> {
                                match part {
                                    Common(values) => {
                                        match graph.condition_sequences.iter(*values).next() {
                                            None => Ok(Sequence::EMPTY),
                                            Some(_) => graph.guard_segments.push(
                                                Sequence::EMPTY,
                                                GuardSegment::Common(*values),
                                            ),
                                        }
                                    }
                                    Mixed {
                                        segments,
                                        targets: _,
                                    } => Ok(*segments),
                                }
                            };
                        let left_segments = segments(left)?;
                        let right_segments = segments(right)?;
                        let joined = graph.guard_segments.append(left_segments, right_segments)?;
                        let targets = |part: &GuardClassification<'g>| match part {
                            Common(_) => SetId::EMPTY,
                            Mixed {
                                segments: _,
                                targets,
                            } => *targets,
                        };
                        let targets = graph.reference_sets.combine(
                            Combination::Union,
                            targets(left),
                            targets(right),
                        )?;
                        Mixed {
                            segments: joined,
                            targets,
                        }
                    }
                })
            },
        );
        self.guard_classifications = classifications;
        let classified = classified?;
        let prepared = match classified.as_ref() {
            None => PreparedGuards::Common(GuardContextId::from(Sequence::EMPTY)),
            Some(GuardClassification::Common(common)) => {
                PreparedGuards::Common(GuardContextId::from(*common))
            }
            Some(GuardClassification::Mixed { segments, targets }) => {
                let shared = self.shared_endpoints(guards)?;
                let shared =
                    self.reference_sets
                        .combine(Combination::Intersection, shared, *targets)?;
                PreparedGuards::Mixed {
                    segments: *segments,
                    targets: *targets,
                    shared,
                }
            }
        };
        self.prepared_guards.insert(guards, prepared);
        Ok(prepared)
    }

    fn query(
        &mut self,
        condition: ConditionId<'g>,
        guards: GuardContextId<'g>,
    ) -> Result<Query<'g>, CapacityError> {
        let guards = match self[condition] {
            ConditionNode::Unknown => GuardContextId::from(Sequence::EMPTY),
            _ => guards,
        };
        let prepared = self.prepare_guards(guards)?;
        let projected = match prepared {
            PreparedGuards::Common(projected) => projected,
            PreparedGuards::Mixed {
                segments,
                targets,
                shared,
            } => {
                if let Some(projected) = self.projected_guards.get(&(condition, guards)) {
                    let query = Query {
                        condition,
                        guards: projected,
                    };
                    return Ok(query);
                }
                let reached = self.references(NodeId::Condition(condition), targets)?;
                let reached = self
                    .reference_sets
                    .combine(Combination::Union, reached, shared)?;
                let projected = if let Some(projected) =
                    self.guard_projections.get(&(guards, reached))
                {
                    projected
                } else {
                    let retained = self.guard_projection_filters.apply(
                        &mut self.guard_segments,
                        segments,
                        &mut self.guard_projection_summaries,
                        reached,
                        &mut (&mut self.reference_sets, &mut self.proof_work),
                        |(sets, work), _, part| {
                            let summary = match part {
                                crate::sequence::Part::Leaf(segment) => {
                                    work.guard_segments = work.guard_segments.saturating_add(1);
                                    match segment {
                                        GuardSegment::Common(_) => GuardProjectionSummary {
                                            targets: SetId::EMPTY,
                                            common: Some(()),
                                        },
                                        GuardSegment::Relevant(_, target) => {
                                            GuardProjectionSummary {
                                                targets: sets.insert(SetId::EMPTY, *target)?,
                                                common: None,
                                            }
                                        }
                                    }
                                }
                                crate::sequence::Part::Branch(left, right) => {
                                    GuardProjectionSummary {
                                        targets: sets.combine(
                                            Combination::Union,
                                            left.targets,
                                            right.targets,
                                        )?,
                                        common: left.common.or(right.common),
                                    }
                                }
                            };
                            Ok::<_, CapacityError>(summary)
                        },
                        |(sets, _), _, summary, reached| {
                            sets.combine(Combination::Intersection, summary.targets, *reached)
                        },
                        |(_, work), _, summary, reached| {
                            work.guard_projection_fragments =
                                work.guard_projection_fragments.saturating_add(1);
                            Ok(if summary.targets == *reached {
                                crate::sequence::Selection::Keep
                            } else if *reached == SetId::EMPTY && summary.common == None {
                                crate::sequence::Selection::Drop
                            } else {
                                crate::sequence::Selection::Visit
                            })
                        },
                        |_, _, _, _| {
                            unreachable!("a guard segment is kept or dropped by its target summary")
                        },
                    )?;
                    let retained = self
                        .guard_projection_conditions
                        .fold(
                            &mut (
                                &self.guard_segments,
                                &mut self.condition_sequences,
                                &mut self.proof_work,
                            ),
                            |context| context.0,
                            retained,
                            |context, part| match part {
                                crate::sequence::Part::Leaf(segment) => {
                                    context.2.guard_segments =
                                        context.2.guard_segments.saturating_add(1);
                                    match segment {
                                        GuardSegment::Common(conditions) => Ok(*conditions),
                                        GuardSegment::Relevant(guard, _) => {
                                            context.1.push(Sequence::EMPTY, *guard)
                                        }
                                    }
                                }
                                crate::sequence::Part::Branch(left, right) => {
                                    context.1.append(*left, *right)
                                }
                            },
                        )?
                        .unwrap_or_default();
                    let projected = GuardContextId::from(retained);
                    self.guard_projections.insert((guards, reached), projected);
                    projected
                };
                self.projected_guards.insert((condition, guards), projected);
                projected
            }
        };
        let query = Query {
            condition,
            guards: projected,
        };
        Ok(query)
    }

    pub fn truth(
        &mut self,
        condition: ConditionId<'g>,
        guards: &Sequence<'g, ConditionId<'g>>,
    ) -> Result<Truth, CapacityError> {
        let guards = GuardContextId::from(*guards);
        self.prove_in_context(condition, guards).map(Truth::from)
    }

    pub fn prove(
        &mut self,
        condition: ConditionId<'g>,
        guards: &Sequence<'g, ConditionId<'g>>,
    ) -> Result<Proof<'g>, CapacityError> {
        let guards = GuardContextId::from(*guards);
        self.prove_in_context(condition, guards)
    }

    pub(crate) fn prove_in_context(
        &mut self,
        condition: ConditionId<'g>,
        guards: GuardContextId<'g>,
    ) -> Result<Proof<'g>, CapacityError> {
        let root = self.query(condition, guards)?;
        crate::memo::resolve(
            self,
            |graph| graph.truths.get(&root).ok_or(root),
            |graph, query| {
                if graph.truths.get(&query).is_some() {
                    return Ok(());
                }
                match graph.truth_step(&query)? {
                    Deduction::Done(proof) => {
                        graph.truths.insert(query, proof);
                        Ok(())
                    }
                    Deduction::Needs(dependency) => Err(Demand::Child(dependency)),
                }
            },
        )
    }

    fn truth_step(&mut self, query: &Query<'g>) -> Result<Deduction<'g>, CapacityError> {
        let mut evidence = Evidence::default();
        macro_rules! done {
            ($truth:expr) => {{
                let truth = $truth;
                let evidence = self.discharge(evidence, query.guards)?;
                Deduction::Done(match truth {
                    Truth::Proven => Proof::Proven(evidence),
                    Truth::Refuted => Proof::Refuted(evidence),
                    Truth::Unknown(gap) => Proof::Unknown(gap),
                })
            }};
        }
        macro_rules! ask {
            ($condition:expr, $guards:expr) => {{
                let query = self.query($condition, $guards)?;
                match self.truths.get(&query) {
                    Some(proof) => {
                        match proof {
                            Proof::Proven(support) | Proof::Refuted(support) => {
                                evidence = Evidence(self.guard_member_sets.combine(
                                    Combination::Union,
                                    evidence.0,
                                    support.0,
                                )?)
                            }
                            Proof::Unknown(_) => {}
                        }
                        Truth::from(proof)
                    }
                    None => return Ok(Deduction::Needs(query)),
                }
            }};
        }
        let Query { condition, guards } = query;
        let node = self[*condition].clone();
        let branches = match node {
            ConditionNode::Compare(order, left, right) => {
                match (self[left].clone(), self[right].clone()) {
                    (ExprNode::Select(choice, yes, no), _) => Some((
                        choice,
                        ConditionNode::Compare(order, yes, right),
                        ConditionNode::Compare(order, no, right),
                    )),
                    (_, ExprNode::Select(choice, yes, no)) => Some((
                        choice,
                        ConditionNode::Compare(order, left, yes),
                        ConditionNode::Compare(order, left, no),
                    )),
                    (ExprNode::Test(choice), _) => {
                        let yes = self.intern_expr(ExprNode::Number(1))?;
                        let no = self.intern_expr(ExprNode::Number(0))?;
                        Some((
                            choice,
                            ConditionNode::Compare(order, yes, right),
                            ConditionNode::Compare(order, no, right),
                        ))
                    }
                    (_, ExprNode::Test(choice)) => {
                        let yes = self.intern_expr(ExprNode::Number(1))?;
                        let no = self.intern_expr(ExprNode::Number(0))?;
                        Some((
                            choice,
                            ConditionNode::Compare(order, left, yes),
                            ConditionNode::Compare(order, left, no),
                        ))
                    }
                    _ => None,
                }
            }
            ConditionNode::Variant(value, variant) => match self[value] {
                ExprNode::Select(choice, yes, no) => Some((
                    choice,
                    ConditionNode::Variant(yes, variant),
                    ConditionNode::Variant(no, variant),
                )),
                _ => None,
            },
            ConditionNode::NotVariant(value, variant) => match self[value] {
                ExprNode::Select(choice, yes, no) => Some((
                    choice,
                    ConditionNode::NotVariant(yes, variant),
                    ConditionNode::NotVariant(no, variant),
                )),
                _ => None,
            },
            _ => None,
        };
        if let Some((choice, yes, no)) = branches {
            if let Some(()) = self.known(NodeId::Condition(*condition)) {
                if let Some(origin) = self.guard(*guards, *condition)? {
                    evidence = Evidence(self.guard_member_sets.insert(evidence.0, origin)?);
                    return Ok(done!(Truth::Proven));
                }
                let negated = self.negate(*condition)?;
                let found = self.guard(*guards, negated)?;
                match (&self[negated], found) {
                    (ConditionNode::Unknown, _) | (_, None) => {}
                    (_, Some(origin)) => {
                        evidence = Evidence(self.guard_member_sets.insert(evidence.0, origin)?);
                        return Ok(done!(Truth::Refuted));
                    }
                }
            }
            let yes = self.intern_condition(yes)?;
            let no = self.intern_condition(no)?;
            let truth = match ask!(choice, *guards) {
                Truth::Proven => ask!(yes, *guards),
                Truth::Refuted => ask!(no, *guards),
                Truth::Unknown(_) => {
                    let unconditional = GuardContextId::from(Sequence::EMPTY);
                    match ask!(yes, unconditional) {
                        Truth::Proven if ask!(no, unconditional) == Truth::Proven => {
                            return Ok(done!(Truth::Proven));
                        }
                        Truth::Refuted if ask!(no, unconditional) == Truth::Refuted => {
                            return Ok(done!(Truth::Refuted));
                        }
                        _ => {}
                    }
                    let branch = GuardContextId(self.condition_sequences.push(guards.0, choice)?);
                    let yes = ask!(yes, branch);
                    if let Truth::Unknown(_) = yes {
                        return Ok(done!(Truth::Unknown(ProofGap::Comparison)));
                    }
                    let negated = self.negate(choice)?;
                    let branch = GuardContextId(self.condition_sequences.push(guards.0, negated)?);
                    let no = ask!(no, branch);
                    match (yes, no) {
                        (Truth::Proven, Truth::Proven) => Truth::Proven,
                        (Truth::Refuted, Truth::Refuted) => Truth::Refuted,
                        _ => Truth::Unknown(ProofGap::Comparison),
                    }
                }
            };
            return Ok(done!(truth));
        }
        match node {
            ConditionNode::Compare(Order::LessEqual, left, _)
                if let ExprNode::Number(0) = &self[left] =>
            {
                return Ok(done!(Truth::Proven));
            }
            ConditionNode::Compare(Order::Less, _, right)
                if let ExprNode::Number(0) = &self[right] =>
            {
                return Ok(done!(Truth::Refuted));
            }
            ConditionNode::Boundary(_, index) if let ExprNode::Number(0) = &self[index] => {
                return Ok(done!(Truth::Proven));
            }
            _ => {}
        }
        if let ConditionNode::Compare(order, left, right) = node {
            let left_node = self[left].clone();
            let right_node = self[right].clone();
            if let Order::LessEqual = order {
                match (&left_node, &right_node) {
                    (ExprNode::Length(left), ExprNode::Length(right)) => {
                        let base = match &self[*left] {
                            ExprNode::Trimmed(base) | ExprNode::Slice { text: base, .. } => {
                                Some(*base)
                            }
                            _ => None,
                        };
                        if let Some(base) = base
                            && base == *right
                            && let Some(()) = self.known(NodeId::Expr(base))
                        {
                            return Ok(done!(Truth::Proven));
                        }
                    }
                    (_, ExprNode::Arithmetic(Arithmetic::Add(_), index, _)) => {
                        if left == *index
                            && let Some(()) = self.known(NodeId::Expr(*index))
                            && let Some(_) = self.matched_text(right)
                        {
                            return Ok(done!(Truth::Proven));
                        }
                    }
                    _ => {}
                }
                if let (ExprNode::Partition { sequence, .. }, ExprNode::Length(base)) =
                    (&left_node, &right_node)
                    && sequence == base
                    && let Some(()) = self.known(NodeId::Expr(*sequence))
                {
                    return Ok(done!(Truth::Proven));
                }
            }
            if let (
                Order::Less,
                ExprNode::Arithmetic(Arithmetic::Subtract(_), partition, amount),
                ExprNode::Length(base),
            ) = (order, &left_node, &right_node)
                && let ExprNode::Number(1) = &self[*amount]
                && let ExprNode::Partition { sequence, .. } = &self[*partition]
                && sequence == base
            {
                let one = self.intern_expr(ExprNode::Number(1))?;
                let required = self.intern_condition(ConditionNode::Compare(
                    Order::LessEqual,
                    one,
                    *partition,
                ))?;
                if ask!(required, *guards) == Truth::Proven {
                    return Ok(done!(Truth::Proven));
                }
            }
            if let (Order::LessEqual, ExprNode::Length(base)) = (order, &right_node)
                && let Some(text) = self.matched_text(left)
                && text == *base
            {
                return Ok(done!(Truth::Proven));
            }
            if let ExprNode::Range(Interval { lower, upper }) = left_node {
                let order = match order {
                    Order::Less | Order::LessEqual => order,
                    Order::Equal | Order::NotEqual => {
                        return Ok(done!(Truth::Unknown(ProofGap::Comparison)));
                    }
                };
                let upper = self.intern_expr(ExprNode::Number(upper))?;
                let required =
                    self.intern_condition(ConditionNode::Compare(order, upper, right))?;
                if ask!(required, *guards) == Truth::Proven {
                    return Ok(done!(Truth::Proven));
                }
                if let Order::Less = order {
                    let lower = self.intern_expr(ExprNode::Number(lower))?;
                    let impossible = self.intern_condition(ConditionNode::Compare(
                        Order::LessEqual,
                        right,
                        lower,
                    ))?;
                    if ask!(impossible, *guards) == Truth::Proven {
                        return Ok(done!(Truth::Refuted));
                    }
                }
                return Ok(done!(Truth::Unknown(ProofGap::Comparison)));
            }
            if let ExprNode::Range(Interval { lower, upper }) = right_node {
                if let Order::Less | Order::LessEqual = order {
                    let lower = self.intern_expr(ExprNode::Number(lower))?;
                    let required =
                        self.intern_condition(ConditionNode::Compare(order, left, lower))?;
                    if ask!(required, *guards) == Truth::Proven {
                        return Ok(done!(Truth::Proven));
                    }
                    let opposite = match order {
                        Order::Less => Order::LessEqual,
                        _ => Order::Less,
                    };
                    let upper = self.intern_expr(ExprNode::Number(upper))?;
                    let impossible =
                        self.intern_condition(ConditionNode::Compare(opposite, upper, left))?;
                    if ask!(impossible, *guards) == Truth::Proven {
                        return Ok(done!(Truth::Refuted));
                    }
                }
                return Ok(done!(Truth::Unknown(ProofGap::Comparison)));
            }
            if let ExprNode::Arithmetic(
                Arithmetic::Subtract(_) | Arithmetic::WrappingSubtract(_),
                value,
                amount,
            ) = left_node
                && let ExprNode::Number(amount) = self[amount]
                && amount > 0
                && let Order::Less | Order::LessEqual = order
            {
                let amount = self.intern_expr(ExprNode::Number(amount))?;
                let nonnegative =
                    self.intern_condition(ConditionNode::Compare(Order::LessEqual, amount, value))?;
                if ask!(nonnegative, *guards) == Truth::Proven {
                    let bounded = self.intern_condition(ConditionNode::Compare(
                        Order::LessEqual,
                        value,
                        right,
                    ))?;
                    if ask!(bounded, *guards) == Truth::Proven {
                        return Ok(done!(Truth::Proven));
                    }
                }
            }
        }
        if let ConditionNode::Boundary(base, index) = node
            && let Some(text) = self.matched_text(index)
            && text == base
        {
            return Ok(done!(Truth::Proven));
        }
        if let None = self.known(NodeId::Condition(*condition)) {
            return Ok(done!(Truth::Unknown(ProofGap::Value)));
        }
        if let ConditionNode::Compare(Order::LessEqual, one, value) = node
            && let ExprNode::Number(1) = &self[one]
        {
            let zero = self.intern_expr(ExprNode::Number(0))?;
            let nonzero =
                self.intern_condition(ConditionNode::Compare(Order::NotEqual, value, zero))?;
            let reversed =
                self.intern_condition(ConditionNode::Compare(Order::NotEqual, zero, value))?;
            if let Some(origin) = self
                .guard(*guards, nonzero)?
                .or(self.guard(*guards, reversed)?)
            {
                evidence = Evidence(self.guard_member_sets.insert(evidence.0, origin)?);
                return Ok(done!(Truth::Proven));
            }
        }
        let direct = match node {
            ConditionNode::Compare(order, left, right) => match (&self[left], &self[right]) {
                (ExprNode::Number(left), ExprNode::Number(right)) => Some(match order {
                    Order::Less if left < right => Truth::Proven,
                    Order::LessEqual if left <= right => Truth::Proven,
                    Order::Equal if left == right => Truth::Proven,
                    Order::NotEqual if left != right => Truth::Proven,
                    _ => Truth::Refuted,
                }),
                _ if left == right => Some(match order {
                    Order::Less | Order::NotEqual => Truth::Refuted,
                    Order::LessEqual | Order::Equal => Truth::Proven,
                }),
                _ => None,
            },
            ConditionNode::Boundary(text, index) => match (&self[text], &self[index]) {
                (ExprNode::Text(text), ExprNode::Number(index)) => {
                    Some(match usize::try_from(*index) {
                        Ok(index) if self.values[*text].is_char_boundary(index) => Truth::Proven,
                        _ => Truth::Refuted,
                    })
                }
                (_, ExprNode::Number(0)) => Some(Truth::Proven),
                (_, ExprNode::Length(base)) if text == *base => Some(Truth::Proven),
                _ => None,
            },
            ConditionNode::NotBoundary(text, index) => {
                let boundary = self.intern_condition(ConditionNode::Boundary(text, index))?;
                Some(match ask!(boundary, *guards) {
                    Truth::Proven => Truth::Refuted,
                    Truth::Refuted => Truth::Proven,
                    unknown @ Truth::Unknown(_) => unknown,
                })
            }
            ConditionNode::Variant(value, required) => match &self[value] {
                ExprNode::Variant(_, actual, _) => Some(if *actual == required {
                    Truth::Proven
                } else {
                    Truth::Refuted
                }),
                _ => None,
            },
            ConditionNode::NotVariant(value, excluded) => match &self[value] {
                ExprNode::Variant(_, actual, _) => Some(if *actual != excluded {
                    Truth::Proven
                } else {
                    Truth::Refuted
                }),
                _ => None,
            },
            ConditionNode::Unknown | ConditionNode::Returned(..) => None,
        };
        if let Some(truth) = direct {
            return Ok(done!(truth));
        }
        let comparison = self.comparison(*guards)?;
        let comparison = self.comparisons[comparison];
        if let ConditionNode::Variant(value, required) = node
            && let Some(actual) = self
                .comparisons
                .variant_maps
                .get(comparison.variants, &value)
                .copied()
        {
            evidence = Evidence(self.guard_member_sets.insert(evidence.0, actual.origin)?);
            return Ok(done!(if actual.variant == required {
                Truth::Proven
            } else {
                Truth::Refuted
            }));
        }
        if let ConditionNode::NotVariant(value, excluded) = node
            && let Some(actual) = self
                .comparisons
                .variant_maps
                .get(comparison.variants, &value)
                .copied()
        {
            evidence = Evidence(self.guard_member_sets.insert(evidence.0, actual.origin)?);
            return Ok(done!(if actual.variant != excluded {
                Truth::Proven
            } else {
                Truth::Refuted
            }));
        }
        if let Some(origin) = self.guard(*guards, *condition)? {
            evidence = Evidence(self.guard_member_sets.insert(evidence.0, origin)?);
            return Ok(done!(Truth::Proven));
        }
        let negated = self.negate(*condition)?;
        let found = self.guard(*guards, negated)?;
        match (&self[negated], found) {
            (ConditionNode::Unknown, _) | (_, None) => {}
            (_, Some(origin)) => {
                evidence = Evidence(self.guard_member_sets.insert(evidence.0, origin)?);
                return Ok(done!(Truth::Refuted));
            }
        }
        let (order, left, right) = match node {
            ConditionNode::Compare(order, left, right) => (order, left, right),
            ConditionNode::Boundary(..) | ConditionNode::NotBoundary(..) => {
                return Ok(done!(Truth::Unknown(ProofGap::Boundary)));
            }
            ConditionNode::Variant(..) | ConditionNode::NotVariant(..) => {
                return Ok(done!(Truth::Unknown(ProofGap::Variant)));
            }
            ConditionNode::Returned(..) => {
                return Ok(done!(Truth::Unknown(ProofGap::Return)));
            }
            ConditionNode::Unknown => return Ok(done!(Truth::Unknown(ProofGap::Value))),
        };
        let equality = match order {
            Order::Equal | Order::NotEqual => Some((left, right)),
            Order::Less | Order::LessEqual => None,
        };
        let left = Vertex::from((&self[left], left));
        let right = Vertex::from((&self[right], right));
        let endpoints = [left, right].map(|value| match value {
            Vertex::Number(number) => Some(number),
            Vertex::Expression(_) => None,
        });
        let comparison_id = self.comparison(*guards)?;
        let comparison = self.comparisons[comparison_id];
        // Base numeric edges remain valid shortcuts through inserted query endpoints.
        let mut endpoint_edges = Vec::new();
        let numbers = endpoints.into_iter().flatten();
        for number in numbers {
            if let Some(()) = self
                .comparisons
                .constant_maps
                .get(comparison.constants, &number)
            {
                continue;
            }
            if let Some((successor, ())) = self.comparisons.constant_maps.neighbor(
                comparison.constants,
                number,
                Neighbor::After,
            ) {
                endpoint_edges.push((Vertex::Number(number), Vertex::Number(*successor)));
            }
            if let Some((previous, ())) = self.comparisons.constant_maps.neighbor(
                comparison.constants,
                number,
                Neighbor::Before,
            ) {
                endpoint_edges.push((Vertex::Number(*previous), Vertex::Number(number)));
            }
        }
        if let [Some(a), Some(b)] = endpoints {
            match a.cmp(&b) {
                std::cmp::Ordering::Less => endpoint_edges.push((left, right)),
                std::cmp::Ordering::Greater => endpoint_edges.push((right, left)),
                std::cmp::Ordering::Equal => {}
            }
        }
        if let Some((outcome, origins)) =
            self.comparison_path(comparison_id, left, right, order, endpoint_edges)
        {
            for origin in origins {
                evidence = Evidence(self.guard_member_sets.insert(evidence.0, origin)?);
            }
            return Ok(done!(outcome));
        }
        if let Some((left, right)) = equality {
            let forward =
                self.intern_condition(ConditionNode::Compare(Order::LessEqual, left, right))?;
            let backward =
                self.intern_condition(ConditionNode::Compare(Order::LessEqual, right, left))?;
            let equal = match ask!(forward, *guards) {
                Truth::Refuted => Truth::Refuted,
                Truth::Proven => ask!(backward, *guards),
                Truth::Unknown(_) => match ask!(backward, *guards) {
                    Truth::Refuted => Truth::Refuted,
                    Truth::Proven | Truth::Unknown(_) => Truth::Unknown(ProofGap::Comparison),
                },
            };
            let equal = match equal {
                Truth::Unknown(gap) => {
                    let reverse =
                        self.intern_condition(ConditionNode::Compare(Order::Less, right, left))?;
                    match ask!(reverse, *guards) {
                        Truth::Proven => Truth::Refuted,
                        Truth::Refuted | Truth::Unknown(_) => Truth::Unknown(gap),
                    }
                }
                Truth::Proven | Truth::Refuted => equal,
            };
            let truth = match (order, equal) {
                (Order::Equal, truth) => truth,
                (Order::NotEqual, Truth::Proven) => Truth::Refuted,
                (Order::NotEqual, Truth::Refuted) => Truth::Proven,
                (Order::NotEqual, unknown @ Truth::Unknown(_)) => unknown,
                (Order::Less | Order::LessEqual, _) => {
                    unreachable!("equality retains both operand identities")
                }
            };
            return Ok(done!(truth));
        }
        Ok(done!(Truth::Unknown(ProofGap::Comparison)))
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Query<'g> {
    condition: ConditionId<'g>,
    guards: GuardContextId<'g>,
}

enum Deduction<'g> {
    Done(Proof<'g>),
    Needs(Query<'g>),
}
