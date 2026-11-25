use rustc_data_structures::fx::{FxHashMap, FxIndexMap};
use std::marker::PhantomData;
use std::sync::Arc;

use parking_lot::Mutex;

use crate::arena::{ArenaId, Intern};
use crate::contracts::graph::sets::SetId;
use crate::contracts::graph::{
    CapacityError, ConditionId, ConditionNode, ExprId, ExprNode, Expression, Graph, GuardContextId,
    KnownCondition,
};
use crate::contracts::{Order, Truth};
use crate::memo::Memo;
use crate::persistent::{Composition, Identical, Map, Maps, Ordered};
use crate::sequence::{Fold, Part, Sequence, Sequences};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Vertex<'g> {
    Expression(ExprId<'g>),
    Number(u128),
}
impl<'g> From<(&ExprNode<'g>, ExprId<'g>)> for Vertex<'g> {
    fn from((node, id): (&ExprNode<'g>, ExprId<'g>)) -> Self {
        match node {
            ExprNode::Number(number) => Self::Number(*number),
            _ => Self::Expression(id),
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Edge<'g> {
    pub target: Vertex<'g>,
    pub order: Order,
    pub origin: ConditionId<'g>,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Variant<'g> {
    pub variant: usize,
    pub origin: ConditionId<'g>,
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Comparison<'g> {
    pub edges: Map<'g, Vertex<'g>, Sequence<'g, Edge<'g>>>,
    pub constants: Map<'g, u128, (), Ordered>,
    pub variants: Map<'g, ExprId<'g>, Variant<'g>>,
}
impl Default for Comparison<'_> {
    fn default() -> Self {
        Self {
            edges: Map::EMPTY,
            constants: Map::EMPTY,
            variants: Map::EMPTY,
        }
    }
}
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ComparisonId<'g>(u32, PhantomData<fn(&'g ()) -> &'g ()>);

impl ArenaId for ComparisonId<'_> {
    fn from_index(index: u32) -> Self {
        Self(index, PhantomData)
    }

    fn index(self) -> u32 {
        self.0
    }
}
type Merge<V, C> = fn(&mut C, &V, &V) -> Result<V, CapacityError>;

#[derive(PartialEq, Eq, Hash)]
struct SearchKey<'g> {
    comparison: ComparisonId<'g>,
    source: Vertex<'g>,
    // Query-only numeric endpoints change adjacency even under the same guards.
    endpoints: Vec<(Vertex<'g>, Vertex<'g>)>,
}

struct Witness<'g> {
    origin: ConditionId<'g>,
    previous: Option<Arc<Witness<'g>>>,
}

impl Drop for Witness<'_> {
    fn drop(&mut self) {
        let mut previous = self.previous.take();
        while let Some(mut step) = previous.and_then(Arc::into_inner) {
            previous = step.previous.take();
        }
    }
}

struct Search<'g> {
    // Insertion order is both the expansion queue and the witness tie-breaker.
    paths: FxIndexMap<(Vertex<'g>, Order), Option<Arc<Witness<'g>>>>,
    pending: std::ops::RangeFrom<usize>,
}

pub(crate) struct Comparisons<'g> {
    searches: Arc<Mutex<FxHashMap<SearchKey<'g>, Arc<Mutex<Search<'g>>>>>>,
    contexts: Memo<GuardContextId<'g>, ComparisonId<'g>>,
    fragments: Fold<'g, ConditionId<'g>, ComparisonId<'g>>,
    nodes: Intern<ComparisonId<'g>, Comparison<'g>>,
    pub edge_maps: Maps<'g, Vertex<'g>, Sequence<'g, Edge<'g>>>,
    pub constant_maps: Maps<'g, u128, (), Ordered>,
    pub variant_maps: Maps<'g, ExprId<'g>, Variant<'g>>,
    edges: Composition<
        'g,
        Vertex<'g>,
        Sequence<'g, Edge<'g>>,
        Merge<Sequence<'g, Edge<'g>>, Sequences<'g, Edge<'g>>>,
    >,
    constants: Composition<'g, u128, (), Merge<(), ()>, Ordered>,
    variants: Composition<'g, ExprId<'g>, Variant<'g>, Merge<Variant<'g>, ()>>,
}
impl Default for Comparisons<'_> {
    fn default() -> Self {
        Self {
            searches: Arc::default(),
            contexts: Memo::new(),
            fragments: Fold::default(),
            nodes: Intern::new(),
            edge_maps: Maps::new(),
            constant_maps: Maps::new(),
            variant_maps: Maps::new(),
            edges: Composition::new(Identical::Combine, |arena, left, right| {
                arena.append(*left, *right)
            }),
            constants: Composition::new(Identical::Reuse, |_, _, _| Ok(())),
            variants: Composition::new(Identical::Reuse, |_, left, _| Ok(*left)),
        }
    }
}
impl<'g> Comparisons<'g> {}

impl<'g> std::ops::Index<ComparisonId<'g>> for Comparisons<'g> {
    type Output = Comparison<'g>;

    fn index(&self, id: ComparisonId<'g>) -> &Self::Output {
        self.nodes.get(id)
    }
}
struct Build<'a, 'g> {
    sequences: &'a mut Sequences<'g, ConditionId<'g>>,
    edge_sequences: &'a mut Sequences<'g, Edge<'g>>,
    expressions: &'a crate::arena::Intern<ExprId<'g>, Expression<'g>>,
    conditions: &'a crate::arena::Intern<ConditionId<'g>, KnownCondition<'g>>,
    nodes: &'a Intern<ComparisonId<'g>, Comparison<'g>>,
    edge_maps: &'a mut Maps<'g, Vertex<'g>, Sequence<'g, Edge<'g>>>,
    constants: &'a mut Maps<'g, u128, (), Ordered>,
    variants: &'a mut Maps<'g, ExprId<'g>, Variant<'g>>,
    merge_edges: &'a mut Composition<
        'g,
        Vertex<'g>,
        Sequence<'g, Edge<'g>>,
        Merge<Sequence<'g, Edge<'g>>, Sequences<'g, Edge<'g>>>,
    >,
    merge_constants: &'a mut Composition<'g, u128, (), Merge<(), ()>, Ordered>,
    merge_variants: &'a mut Composition<'g, ExprId<'g>, Variant<'g>, Merge<Variant<'g>, ()>>,
}
impl<'g> Build<'_, 'g> {
    fn add(
        &mut self,
        facts: &mut Comparison<'g>,
        source: Vertex<'g>,
        target: Vertex<'g>,
        order: Order,
        origin: ConditionId<'g>,
    ) -> Result<(), CapacityError> {
        let outgoing = self
            .edge_maps
            .get(facts.edges, &source)
            .copied()
            .unwrap_or(Sequence::EMPTY);
        let outgoing = self.edge_sequences.push(
            outgoing,
            Edge {
                target,
                order,
                origin,
            },
        )?;
        self.edge_maps.insert(&mut facts.edges, source, outgoing)?;
        for vertex in [source, target] {
            if let Vertex::Number(number) = vertex {
                self.constants.insert(&mut facts.constants, number, ())?;
            }
        }
        Ok(())
    }
}
impl<'g> Graph<'g> {
    pub(crate) fn comparison_path(
        &mut self,
        comparison: ComparisonId<'g>,
        source: Vertex<'g>,
        target: Vertex<'g>,
        order: Order,
        endpoints: Vec<(Vertex<'g>, Vertex<'g>)>,
    ) -> Option<(Truth, Vec<ConditionId<'g>>)> {
        let key = SearchKey {
            comparison,
            source,
            endpoints: endpoints.clone(),
        };
        let search = {
            let mut searches = self.comparisons.searches.lock();
            Arc::clone(searches.entry(key).or_insert_with(|| {
                let initial = (source, Order::LessEqual);
                Arc::new(Mutex::new(Search {
                    paths: FxIndexMap::from_iter([(initial, None)]),
                    pending: 0..,
                }))
            }))
        };
        let mut search = search.lock();
        let comparison = self.comparisons[comparison];
        loop {
            // Discovery order is FIFO order, so the earliest compatible path remains the witness.
            let strict = search.paths.get_full(&(target, Order::Less));
            let reached = match order {
                Order::Less | Order::Equal | Order::NotEqual => strict,
                Order::LessEqual => {
                    match (strict, search.paths.get_full(&(target, Order::LessEqual))) {
                        (Some(left), Some(right)) => {
                            Some(if left.0 < right.0 { left } else { right })
                        }
                        (some @ Some(_), None) | (None, some @ Some(_)) => some,
                        (None, None) => None,
                    }
                }
            };
            if let Some((_, _, witness)) = reached {
                let mut evidence = Vec::new();
                let mut cursor = witness.as_deref();
                while let Some(step) = cursor {
                    evidence.push(step.origin);
                    cursor = step.previous.as_deref();
                }
                let truth = match order {
                    Order::Equal => Truth::Refuted,
                    Order::Less | Order::LessEqual | Order::NotEqual => Truth::Proven,
                };
                return Some((truth, evidence));
            }
            let (&(value, path), witness) = search.paths.get_index(search.pending.start)?;
            let witness = witness.clone();
            search.pending.next();
            self.proof_work.comparison_states = self.proof_work.comparison_states.saturating_add(1);
            let mut visit = |target, order, origin| {
                let path = match (path, order) {
                    (Order::Less, _) | (_, Order::Less) => Order::Less,
                    _ => Order::LessEqual,
                };
                let next = (target, path);
                search.paths.entry(next).or_insert_with(|| match origin {
                    Some(origin) => Some(Arc::new(Witness {
                        origin,
                        previous: witness.clone(),
                    })),
                    None => witness.clone(),
                });
            };
            if let Some(next) = self.comparisons.edge_maps.get(comparison.edges, &value) {
                for edge in self.comparison_edges.iter(*next) {
                    self.proof_work.comparison_edges =
                        self.proof_work.comparison_edges.saturating_add(1);
                    visit(edge.target, edge.order, Some(edge.origin));
                }
            }
            if let Vertex::Number(number) = value
                && let Some(()) = self
                    .comparisons
                    .constant_maps
                    .get(comparison.constants, &number)
                && let Some((next, ())) = self.comparisons.constant_maps.neighbor(
                    comparison.constants,
                    number,
                    crate::persistent::Neighbor::After,
                )
            {
                visit(Vertex::Number(*next), Order::Less, None);
            }
            for &(from, to) in &endpoints {
                if from == value {
                    visit(to, Order::Less, None);
                }
            }
        }
    }

    pub(crate) fn comparison(
        &mut self,
        guards: GuardContextId<'g>,
    ) -> Result<ComparisonId<'g>, CapacityError> {
        if let Some(id) = self.comparisons.contexts.get(&guards) {
            return Ok(id);
        }
        let Comparisons {
            searches: _,
            contexts,
            fragments,
            nodes,
            edge_maps,
            constant_maps,
            variant_maps,
            edges,
            constants,
            variants,
        } = &mut self.comparisons;
        let mut build = Build {
            sequences: &mut self.condition_sequences,
            edge_sequences: &mut self.comparison_edges,
            expressions: &self.expressions,
            conditions: &self.conditions,
            nodes,
            edge_maps,
            constants: constant_maps,
            variants: variant_maps,
            merge_edges: edges,
            merge_constants: constants,
            merge_variants: variants,
        };
        let result = fragments.fold(
            &mut build,
            |build| &*build.sequences,
            guards.0,
            |build, part| {
                let facts = match part {
                    Part::Leaf(guard) => {
                        let mut facts = Comparison::default();
                        if let ConditionNode::Variant(value, variant) =
                            build.conditions.get(*guard).node
                        {
                            build.variants.insert(
                                &mut facts.variants,
                                value,
                                Variant {
                                    variant,
                                    origin: *guard,
                                },
                            )?;
                        }
                        if let Some(()) = build.conditions.get(*guard).known {
                            if let ConditionNode::Compare(order, left, right) =
                                build.conditions.get(*guard).node
                            {
                                let left = Vertex::from((&build.expressions.get(left).node, left));
                                let right =
                                    Vertex::from((&build.expressions.get(right).node, right));
                                match order {
                                    Order::Less => {
                                        build.add(&mut facts, left, right, Order::Less, *guard)?;
                                        if let Vertex::Number(number) = left
                                            && let Some(next) = number.checked_add(1)
                                        {
                                            build.add(
                                                &mut facts,
                                                Vertex::Number(next),
                                                right,
                                                Order::LessEqual,
                                                *guard,
                                            )?;
                                        }
                                        if let Vertex::Number(number) = right
                                            && let Some(previous) = number.checked_sub(1)
                                        {
                                            build.add(
                                                &mut facts,
                                                left,
                                                Vertex::Number(previous),
                                                Order::LessEqual,
                                                *guard,
                                            )?;
                                        }
                                    }
                                    Order::LessEqual => build.add(
                                        &mut facts,
                                        left,
                                        right,
                                        Order::LessEqual,
                                        *guard,
                                    )?,
                                    Order::Equal => {
                                        build.add(
                                            &mut facts,
                                            left,
                                            right,
                                            Order::LessEqual,
                                            *guard,
                                        )?;
                                        build.add(
                                            &mut facts,
                                            right,
                                            left,
                                            Order::LessEqual,
                                            *guard,
                                        )?;
                                    }
                                    Order::NotEqual => {}
                                }
                            }
                        }
                        facts
                    }
                    Part::Branch(left, right) => {
                        let left = *build.nodes.get(*left);
                        let right = *build.nodes.get(*right);
                        Comparison {
                            edges: build.merge_edges.compose(
                                build.edge_maps,
                                build.edge_sequences,
                                left.edges,
                                right.edges,
                            )?,
                            constants: build.merge_constants.compose(
                                build.constants,
                                &mut (),
                                left.constants,
                                right.constants,
                            )?,
                            variants: build.merge_variants.compose(
                                build.variants,
                                &mut (),
                                left.variants,
                                right.variants,
                            )?,
                        }
                    }
                };
                build.nodes.intern(facts, CapacityError::Values)
            },
        )?;
        let result = match result {
            Some(result) => result,
            None => build
                .nodes
                .intern(Comparison::default(), CapacityError::Values)?,
        };
        contexts.insert(guards, result);
        Ok(result)
    }

    pub(crate) fn guard_membership(
        &mut self,
        context: GuardContextId<'g>,
    ) -> Result<SetId<'g, ConditionId<'g>>, CapacityError> {
        let Graph {
            condition_sequences,
            guard_members,
            guard_member_sets,
            ..
        } = self;
        Ok(guard_members
            .fold(
                &mut (&mut *condition_sequences, &mut *guard_member_sets),
                |context| &*context.0,
                context.0,
                |context, part| context.1.members(part),
            )?
            .unwrap_or_default())
    }

    pub(crate) fn guard(
        &mut self,
        context: GuardContextId<'g>,
        condition: ConditionId<'g>,
    ) -> Result<Option<ConditionId<'g>>, CapacityError> {
        let members = self.guard_membership(context)?;
        Ok(self
            .guard_member_sets
            .contains(members, condition)
            .map(|()| condition))
    }
}
