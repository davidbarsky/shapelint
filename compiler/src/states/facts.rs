use std::hash::Hash;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::{Body, Local, Place};
use rustc_middle::ty::{self, TyCtxt};

use crate::contracts::graph::sets::{Combination, SetId, Sets};
use crate::contracts::graph::{
    CapacityError, ConditionId, ConditionNode, ExprId, ExprNode, Graph, NodeId,
};
use crate::contracts::operations::{Affected, GraphInvalidation};
use crate::contracts::{Order, Truth};
use crate::persistent::{Difference, Differences, Map, Maps, Set};
use crate::sequence::{Fold, Scan, Selection, Sequence, Sequences, TransformCache};
use crate::states::Invalidated;
use crate::states::places::{Overlap, Paths, Places};

type Conjunction<'g> = fn(
    &mut (&mut Graph<'g>, ExprId<'g>),
    ExprId<'g>,
    &ConditionId<'g>,
) -> Result<ExprId<'g>, CapacityError>;

pub struct Context<'tcx, 's, 'g> {
    pub(crate) captures: crate::values::Captures<'tcx, 'g>,
    pub(crate) paths: Paths<'tcx, 's>,
    pub(crate) symbols: Maps<'s, Place<'tcx>, ExprId<'g>>,
    pub(crate) escaped: crate::persistent::Sets<'s, rustc_span::Span>,
    condition_counts: Maps<'s, ConditionId<'g>, usize>,
    lost_counts: Maps<'s, Invalidated<'g>, usize>,
    dependencies: DependencyStores<'s, 'g, Root<'tcx, 'g>>,
    pub(crate) protocols: crate::protocols::Stores<'tcx, 'g, 's>,
    pub(crate) names: crate::states::names::Names<'tcx, 's, 'g>,
    pub(crate) frozen: FxHashMap<ty::Ty<'tcx>, Option<()>>,
    pub(crate) droppable: FxHashMap<ty::Ty<'tcx>, Option<()>>,
    sequences: FactSequences<'s, 'g>,
}

struct FactSequences<'s, 'g> {
    condition_replacements: Maps<'s, ConditionId<'g>, ConditionId<'g>>,
    condition_rewrites:
        TransformCache<'g, ConditionId<'g>, Map<'s, ConditionId<'g>, ConditionId<'g>>>,
    lost_replacements: Maps<'s, Invalidated<'g>, Option<Invalidated<'g>>>,
    lost_rewrites:
        TransformCache<'g, Invalidated<'g>, Map<'s, Invalidated<'g>, Option<Invalidated<'g>>>>,
    conditions: Fold<'g, ConditionId<'g>, SetId<'s, ConditionId<'g>>>,
    condition_sets: Sets<'s, ConditionId<'g>>,
    selections: TransformCache<'g, ConditionId<'g>, (SetId<'s, ConditionId<'g>>, Retain)>,
    conjunctions: Scan<'g, ConditionId<'g>, ExprId<'g>, ExprId<'g>, Conjunction<'g>>,
    lost: Fold<'g, Invalidated<'g>, SetId<'s, Invalidated<'g>>>,
    lost_sets: Sets<'s, Invalidated<'g>>,
}

impl<'tcx, 's, 'g> Context<'tcx, 's, 'g> {
    fn try_new(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        sources: &crate::diagnostics::Sources,
        values: crate::values::Values<'g>,
    ) -> Result<Self, CapacityError> {
        let mut paths = Paths::default();
        let names = crate::states::names::Names::try_new(tcx, body, sources, &mut paths)?;
        let context = Self {
            captures: crate::values::Captures::new(tcx, values),
            paths,
            names,
            frozen: FxHashMap::default(),
            droppable: FxHashMap::default(),
            symbols: Maps::new(),
            escaped: Maps::new(),
            condition_counts: Maps::new(),
            lost_counts: Maps::new(),
            dependencies: DependencyStores::new(),
            protocols: crate::protocols::Stores::new(),
            sequences: FactSequences {
                condition_replacements: Maps::new(),
                condition_rewrites: TransformCache::default(),
                lost_replacements: Maps::new(),
                lost_rewrites: TransformCache::default(),
                conditions: Fold::default(),
                condition_sets: Sets::new(),
                selections: TransformCache::default(),
                conjunctions: Scan::new(|(graph, zero), prefix, condition| {
                    graph.intern_expr(ExprNode::Select(*condition, prefix, *zero))
                }),
                lost: Fold::default(),
                lost_sets: Sets::new(),
            },
        };
        Ok(context)
    }
}

pub fn with_context<'tcx, 'g, T>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    sources: &crate::diagnostics::Sources,
    values: crate::values::Values<'g>,
    f: impl for<'s> FnOnce(Context<'tcx, 's, 'g>) -> T,
) -> Result<T, CapacityError> {
    Ok(f(Context::try_new(tcx, body, sources, values)?))
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Retain {
    Selected,
    Others,
}
pub(crate) enum Scope {
    All,
    Live,
    Lost,
}

pub(crate) fn complementary<'g>(
    graph: &Graph<'g>,
    left: Sequence<'g, ConditionId<'g>>,
    right: Sequence<'g, ConditionId<'g>>,
) -> Option<ConditionId<'g>> {
    let guards: &Sequences<'g, ConditionId<'g>> = graph.as_ref();
    if guards.len(left) != 1 || guards.len(right) != 1 {
        return None;
    }
    let left = *guards.get(left, 0)?;
    let right = *guards.get(right, 0)?;
    let ConditionNode::Compare(a, lhs, rhs) = graph[left] else {
        return None;
    };
    let ConditionNode::Compare(b, other_lhs, other_rhs) = graph[right] else {
        return None;
    };
    if lhs != other_lhs || rhs != other_rhs {
        return None;
    }
    match (a, b) {
        (Order::Equal, Order::NotEqual) | (Order::NotEqual, Order::Equal) => {
            match (&graph[lhs], &graph[rhs]) {
                (ExprNode::Argument(_), ExprNode::Number(_))
                | (ExprNode::Number(_), ExprNode::Argument(_)) => Some(left),
                _ => None,
            }
        }
        _ => None,
    }
}

impl<'tcx, 's, 'g> Context<'tcx, 's, 'g> {
    /// Preserves each path's guard order and shares completed conjunction fragments.
    /// Empty paths and a proved unconditional union contribute no additional condition.
    pub fn join_conditions(
        &mut self,
        left: &Sequence<'g, ConditionId<'g>>,
        right: &Sequence<'g, ConditionId<'g>>,
        graph: &mut Graph<'g>,
    ) -> Result<Option<ConditionId<'g>>, CapacityError> {
        if *left == Sequence::EMPTY || *right == Sequence::EMPTY {
            return Ok(None);
        }
        if let Some(_) = complementary(graph, *left, *right) {
            return Ok(None);
        }
        let zero = graph.intern_expr(ExprNode::Number(0))?;
        let one = graph.intern_expr(ExprNode::Number(1))?;
        let left = self.sequences.conjunction(graph, *left, zero, one)?;
        let right = self.sequences.conjunction(graph, *right, zero, one)?;
        let condition = graph.from_expr(left, 1)?;
        let predicate = graph.intern_expr(ExprNode::Select(condition, one, right))?;
        let condition = graph.from_expr(predicate, 1)?;
        Ok(match graph.truth(condition, &Sequence::default())? {
            Truth::Proven => None,
            Truth::Refuted | Truth::Unknown(_) => Some(condition),
        })
    }
}

impl<'s, 'g> FactSequences<'s, 'g> {
    fn conjunction(
        &mut self,
        graph: &mut Graph<'g>,
        guards: Sequence<'g, ConditionId<'g>>,
        zero: ExprId<'g>,
        one: ExprId<'g>,
    ) -> Result<ExprId<'g>, CapacityError> {
        let mut context = (graph, zero);
        self.conjunctions.apply(
            &mut context,
            |context| context.0.as_ref(),
            guards,
            one,
            zero,
        )
    }

    fn select_conditions(
        &mut self,
        sequence: &Sequence<'g, ConditionId<'g>>,
        graph: &mut Graph<'g>,
        selected: impl IntoIterator<Item = ConditionId<'g>>,
        retain: Retain,
    ) -> Result<Sequence<'g, ConditionId<'g>>, CapacityError> {
        let mut members = SetId::EMPTY;
        for condition in selected {
            members = self.condition_sets.insert(members, condition)?;
        }
        self.select_members(sequence, graph, members, retain)
    }

    fn select_members(
        &mut self,
        sequence: &Sequence<'g, ConditionId<'g>>,
        graph: &mut Graph<'g>,
        selected: SetId<'s, ConditionId<'g>>,
        retain: Retain,
    ) -> Result<Sequence<'g, ConditionId<'g>>, CapacityError> {
        let mut context = (&mut self.condition_sets, selected, retain);
        self.conditions.edit(
            graph.as_mut(),
            *sequence,
            &mut self.selections,
            (selected, retain),
            &mut context,
            |(sets, _, _), _, part| sets.members(part),
            |(sets, selected, retain), _, members, _| {
                let common = sets.combine(Combination::Intersection, *members, *selected)?;
                Ok(match retain {
                    Retain::Selected if common == SetId::EMPTY => Selection::Drop,
                    Retain::Others if common == *members => Selection::Drop,
                    Retain::Others if common == SetId::EMPTY => Selection::Keep,
                    Retain::Selected if common == *members => Selection::Keep,
                    _ => Selection::Visit,
                })
            },
            |(sets, selected, retain), _, value, _| {
                let member = sets.contains(*selected, *value);
                Ok(match (member, retain) {
                    (Some(()), Retain::Selected) | (None, Retain::Others) => Some(*value),
                    _ => None,
                })
            },
        )
    }

    fn differences(
        &mut self,
        left: &Sequence<'g, ConditionId<'g>>,
        right: &Sequence<'g, ConditionId<'g>>,
        counts: Differences<'_, 's, ConditionId<'g>, usize>,
        graph: &mut Graph<'g>,
    ) -> Result<(Sequence<'g, ConditionId<'g>>, Sequence<'g, ConditionId<'g>>), CapacityError> {
        let mut left_members = SetId::EMPTY;
        let mut right_members = SetId::EMPTY;
        for (condition, change) in counts {
            match change {
                Difference::Left(_) => {
                    left_members = self.condition_sets.insert(left_members, *condition)?
                }
                Difference::Right(_) => {
                    right_members = self.condition_sets.insert(right_members, *condition)?
                }
                Difference::Both(..) => {}
            }
        }
        let left_only = self.select_members(left, graph, left_members, Retain::Selected)?;
        let right_only = self.select_members(right, graph, right_members, Retain::Selected)?;
        Ok((left_only, right_only))
    }

    fn map_conditions(
        &mut self,
        sequence: &mut Sequence<'g, ConditionId<'g>>,
        graph: &mut Graph<'g>,
        replacements: &FxHashMap<ConditionId<'g>, ConditionId<'g>>,
    ) -> Result<(), CapacityError> {
        if replacements.is_empty() {
            return Ok(());
        }
        let mut selected = SetId::EMPTY;
        let mut key = Map::EMPTY;
        for (condition, replacement) in replacements {
            selected = self.condition_sets.insert(selected, *condition)?;
            self.condition_replacements
                .insert(&mut key, *condition, *replacement)?;
        }
        let mut context = (&mut self.condition_sets, selected, replacements);
        *sequence = self.conditions.edit(
            graph.as_mut(),
            *sequence,
            &mut self.condition_rewrites,
            key,
            &mut context,
            |(sets, _, _), _, part| sets.members(part),
            |(sets, selected, _), _, members, _| {
                Ok(
                    match sets.combine(Combination::Intersection, *members, *selected)? {
                        common if common == SetId::EMPTY => Selection::Keep,
                        _ => Selection::Visit,
                    },
                )
            },
            |(_, _, replacements), _, value, _| {
                Ok(Some(replacements.get(value).copied().unwrap_or(*value)))
            },
        )?;
        Ok(())
    }

    fn edit_lost(
        &mut self,
        sequence: &mut Sequence<'g, Invalidated<'g>>,
        graph: &mut Graph<'g>,
        replacements: &FxHashMap<Invalidated<'g>, Option<Invalidated<'g>>>,
    ) -> Result<(), CapacityError> {
        if replacements.is_empty() {
            return Ok(());
        }
        let mut selected = SetId::EMPTY;
        let mut dropped = SetId::EMPTY;
        let mut key = Map::EMPTY;
        for (fact, replacement) in replacements {
            self.lost_replacements
                .insert(&mut key, *fact, *replacement)?;
            selected = self.lost_sets.insert(selected, *fact)?;
            if let None = replacement {
                dropped = self.lost_sets.insert(dropped, *fact)?;
            }
        }
        let mut context = (&mut self.lost_sets, selected, dropped, replacements);
        *sequence = self.lost.edit(
            graph.as_mut(),
            *sequence,
            &mut self.lost_rewrites,
            key,
            &mut context,
            |(sets, _, _, _), _, part| sets.members(part),
            |(sets, selected, dropped, _), _, members, _| {
                Ok(
                    match sets.combine(Combination::Intersection, *members, *selected)? {
                        common if common == SetId::EMPTY => Selection::Keep,
                        _ if sets.combine(Combination::Intersection, *members, *dropped)?
                            == *members =>
                        {
                            Selection::Drop
                        }
                        _ => Selection::Visit,
                    },
                )
            },
            |(_, _, _, replacements), _, value, _| {
                Ok(replacements
                    .get(value)
                    .cloned()
                    .unwrap_or_else(|| Some(value.clone())))
            },
        )?;
        Ok(())
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum Root<'tcx, 'g> {
    Symbol(Place<'tcx>),
    Condition(ConditionId<'g>),
    Lost(Invalidated<'g>),
    Transient,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct FactsData<'tcx, 's, 'g> {
    pub(crate) symbols: Map<'s, Place<'tcx>, ExprId<'g>>,
    pub conditions: Sequence<'g, ConditionId<'g>>,
    pub lost: Sequence<'g, Invalidated<'g>>,
}

impl Default for FactsData<'_, '_, '_> {
    fn default() -> Self {
        Self {
            symbols: Map::EMPTY,
            conditions: Sequence::EMPTY,
            lost: Sequence::EMPTY,
        }
    }
}

#[derive(Clone, Copy)]
pub struct Facts<'tcx, 's, 'g> {
    data: FactsData<'tcx, 's, 'g>,
    places: Places<'tcx, 's>,
    condition_counts: Map<'s, ConditionId<'g>, usize>,
    lost_counts: Map<'s, Invalidated<'g>, usize>,
    dependencies: Dependencies<'s, 'g, Root<'tcx, 'g>>,
}

impl Default for Facts<'_, '_, '_> {
    fn default() -> Self {
        Self {
            data: FactsData::default(),
            places: Places::default(),
            condition_counts: Map::EMPTY,
            lost_counts: Map::EMPTY,
            dependencies: Dependencies::default(),
        }
    }
}

impl PartialEq for Facts<'_, '_, '_> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}
impl Eq for Facts<'_, '_, '_> {}
impl Hash for Facts<'_, '_, '_> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.data.hash(state);
    }
}

impl<'tcx, 's, 'g> std::ops::Deref for Facts<'tcx, 's, 'g> {
    type Target = FactsData<'tcx, 's, 'g>;

    fn deref(&self) -> &Self::Target {
        &self.data
    }
}

impl<'tcx, 's, 'g> Facts<'tcx, 's, 'g> {
    pub(crate) fn tracked(
        &self,
        place: Place<'tcx>,
        context: &Context<'tcx, 's, 'g>,
    ) -> Option<(Place<'tcx>, ExprId<'g>)> {
        let key = context
            .paths
            .ancestors(&self.places, place)
            .into_iter()
            .max_by_key(|key| key.projection.len())?;
        Some((
            key,
            *context
                .symbols
                .get(self.data.symbols, &key)
                .expect("tracked symbol exists"),
        ))
    }

    pub(crate) fn insert(
        &mut self,
        place: Place<'tcx>,
        value: ExprId<'g>,
        graph: &Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<(), CapacityError> {
        self.dependencies.insert(
            &mut context.dependencies,
            Root::Symbol(place),
            NodeId::Expr(value),
            graph,
        )?;
        context.paths.insert(&mut self.places, place, place)?;
        context
            .symbols
            .insert(&mut self.data.symbols, place, value)?;
        Ok(())
    }

    pub(crate) fn remove(
        &mut self,
        place: &Place<'tcx>,
        graph: &Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<(), CapacityError> {
        self.dependencies
            .remove(&mut context.dependencies, &Root::Symbol(*place), graph)?;
        context.paths.remove(&mut self.places, place)?;
        context.symbols.remove(&mut self.data.symbols, place)?;
        Ok(())
    }

    pub fn condition(
        &mut self,
        condition: ConditionId<'g>,
        graph: &mut Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<(), CapacityError> {
        let mut next = *self;
        next.data.conditions = graph.push(next.data.conditions, condition)?;
        let count = context
            .condition_counts
            .get(next.condition_counts, &condition)
            .copied()
            .unwrap_or(0);
        context.condition_counts.insert(
            &mut next.condition_counts,
            condition,
            count.checked_add(1).ok_or(CapacityError::Sequences)?,
        )?;
        next.dependencies.insert(
            &mut context.dependencies,
            Root::Condition(condition),
            NodeId::Condition(condition),
            graph,
        )?;
        *self = next;
        Ok(())
    }

    pub fn lose(
        &mut self,
        fact: Invalidated<'g>,
        graph: &mut Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<(), CapacityError> {
        if let Some(_) = context.lost_counts.get(self.lost_counts, &fact) {
            return Ok(());
        }
        self.data.lost = graph.push(self.data.lost, fact.clone())?;
        context
            .lost_counts
            .insert(&mut self.lost_counts, fact.clone(), 1)?;
        self.dependencies.insert(
            &mut context.dependencies,
            Root::Lost(fact.clone()),
            NodeId::Condition(fact.condition),
            graph,
        )?;
        Ok(())
    }

    pub(crate) fn clear_symbols(
        &mut self,
        graph: &Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<(), CapacityError> {
        let places: Vec<_> = context
            .symbols
            .iter(self.data.symbols)
            .map(|(place, _)| *place)
            .collect();
        for place in places {
            self.dependencies
                .remove(&mut context.dependencies, &Root::Symbol(place), graph)?;
        }
        self.places = Places::default();
        self.data.symbols = Map::EMPTY;
        Ok(())
    }

    pub(crate) fn clear_conditions(
        &mut self,
        graph: &Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<(), CapacityError> {
        let conditions: Vec<_> = context
            .condition_counts
            .iter(self.condition_counts)
            .map(|(condition, _)| *condition)
            .collect();
        for condition in conditions {
            self.dependencies.remove(
                &mut context.dependencies,
                &Root::Condition(condition),
                graph,
            )?;
        }
        self.data.conditions = Sequence::default();
        self.condition_counts = Map::EMPTY;
        Ok(())
    }

    pub(crate) fn forget_places(
        &mut self,
        place: Place<'tcx>,
        graph: &Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<(), CapacityError> {
        for key in context
            .paths
            .overlapping(&self.places, place, Overlap::Prefixes)
        {
            self.remove(&key, graph, context)?;
        }
        Ok(())
    }

    pub(crate) fn replace_symbols(
        &mut self,
        value: ExprId<'g>,
        replacement: ExprId<'g>,
        graph: &Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<FxHashSet<Place<'tcx>>, CapacityError> {
        let keys: FxHashSet<_> = match context
            .dependencies
            .nodes
            .get(self.dependencies.nodes, &NodeId::Expr(value))
        {
            Some(active) => context
                .dependencies
                .root_sets
                .iter(active.roots)
                .filter_map(|(root, ())| match root {
                    Root::Symbol(place) => Some(*place),
                    _ => None,
                })
                .collect(),
            None => FxHashSet::default(),
        };
        for key in &keys {
            self.insert(*key, replacement, graph, context)?;
        }
        Ok(keys)
    }

    pub(crate) fn lost_conditions(
        &self,
        target: ExprId<'g>,
        value: ExprId<'g>,
        graph: &mut Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<Vec<ConditionId<'g>>, CapacityError> {
        let change = GraphInvalidation::Memory(target);
        let affected = self
            .dependencies
            .affected(&mut context.dependencies, change, graph)?;
        let roots = self
            .dependencies
            .roots(&context.dependencies, graph, affected);
        let selected = roots.into_keys().filter_map(|root| match root {
            Root::Condition(condition) => Some(condition),
            Root::Symbol(_) | Root::Lost(_) | Root::Transient => None,
        });
        let conditions = context.sequences.select_conditions(
            &self.data.conditions,
            graph,
            selected,
            Retain::Selected,
        )?;
        let mut result = Vec::new();
        let conditions: Vec<_> = graph.items(conditions).copied().collect();
        for condition in &conditions {
            if graph.invalidate_condition(*condition, change, affected)? != *condition {
                result.push(graph.invalidate_condition(
                    *condition,
                    GraphInvalidation::Replace { target, value },
                    affected,
                )?);
            }
        }
        Ok(result)
    }

    pub(crate) fn invalidate_expression(
        &mut self,
        value: ExprId<'g>,
        change: GraphInvalidation<'g>,
        graph: &mut Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<ExprId<'g>, CapacityError> {
        self.dependencies.insert(
            &mut context.dependencies,
            Root::Transient,
            NodeId::Expr(value),
            graph,
        )?;
        let affected = self
            .dependencies
            .affected(&mut context.dependencies, change, graph)?;
        let result = graph.invalidate_expr(value, change, affected);
        self.dependencies
            .remove(&mut context.dependencies, &Root::Transient, graph)?;
        result
    }

    pub(crate) fn condition_differences(
        &self,
        other: &Self,
        graph: &mut Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<(Sequence<'g, ConditionId<'g>>, Sequence<'g, ConditionId<'g>>), CapacityError> {
        let counts = Differences::from((
            &context.condition_counts,
            self.condition_counts,
            other.condition_counts,
        ));
        context
            .sequences
            .differences(&self.data.conditions, &other.conditions, counts, graph)
    }

    /// Keeps common facts and appends the optional condition without retiring shared dependencies.
    /// Returns the number of graph nodes newly attached to the active dependency index.
    /// Errors leave the facts unchanged; reusable edit summaries may still be cached.
    pub fn merge(
        &mut self,
        other: &Self,
        additional: Option<ConditionId<'g>>,
        graph: &mut Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<usize, CapacityError> {
        let mut next = self.clone();
        let attached = next.merge_inner(other, additional, graph, context)?;
        *self = next;
        Ok(attached)
    }

    fn merge_inner(
        &mut self,
        other: &Self,
        additional: Option<ConditionId<'g>>,
        graph: &mut Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
    ) -> Result<usize, CapacityError> {
        let removed_conditions: Vec<_> = Differences::from((
            &context.condition_counts,
            self.condition_counts,
            other.condition_counts,
        ))
        .filter_map(|(condition, difference)| match difference {
            Difference::Left(_) => Some(*condition),
            Difference::Right(_) | Difference::Both(..) => None,
        })
        .collect();
        let mut conditions = context.sequences.select_conditions(
            &self.data.conditions,
            graph,
            removed_conditions.iter().copied(),
            Retain::Others,
        )?;
        if let Some(condition) = additional {
            conditions = graph.push(conditions, condition)?;
        }
        let removed_lost: FxHashMap<_, _> =
            Differences::from((&context.lost_counts, self.lost_counts, other.lost_counts))
                .filter_map(|(fact, difference)| match difference {
                    Difference::Left(_) => Some((fact.clone(), None)),
                    Difference::Right(_) | Difference::Both(..) => None,
                })
                .collect();
        let mut lost = self.data.lost.clone();
        context
            .sequences
            .edit_lost(&mut lost, graph, &removed_lost)?;
        let attached = match additional {
            Some(condition) => self.dependencies.insert(
                &mut context.dependencies,
                Root::Condition(condition),
                NodeId::Condition(condition),
                graph,
            )?,
            None => 0,
        };
        for condition in removed_conditions {
            context
                .condition_counts
                .remove(&mut self.condition_counts, &condition)?;
            if Some(condition) != additional {
                self.dependencies.remove(
                    &mut context.dependencies,
                    &Root::Condition(condition),
                    graph,
                )?;
            }
        }
        if let Some(condition) = additional {
            let count = context
                .condition_counts
                .get(self.condition_counts, &condition)
                .copied()
                .unwrap_or(0);
            context.condition_counts.insert(
                &mut self.condition_counts,
                condition,
                count.checked_add(1).ok_or(CapacityError::Sequences)?,
            )?;
        }
        for fact in removed_lost.keys() {
            context.lost_counts.remove(&mut self.lost_counts, fact)?;
            self.dependencies.remove(
                &mut context.dependencies,
                &Root::Lost(fact.clone()),
                graph,
            )?;
        }
        self.data.conditions = conditions;
        self.data.lost = lost;
        Ok(attached)
    }

    pub(crate) fn invalidate(
        &mut self,
        change: GraphInvalidation<'g>,
        graph: &mut Graph<'g>,
        context: &mut Context<'tcx, 's, 'g>,
        scope: Scope,
        mut preserve: impl FnMut(Place<'tcx>) -> Option<()>,
    ) -> Result<(), CapacityError> {
        let affected = self
            .dependencies
            .affected(&mut context.dependencies, change, graph)?;
        let roots = self
            .dependencies
            .roots(&context.dependencies, graph, affected);
        let mut conditions = FxHashMap::default();
        let mut lost = FxHashMap::default();
        let mut symbols = Vec::new();
        for (root, node) in roots {
            match (&scope, &root) {
                (Scope::Live, Root::Lost(_))
                | (Scope::Lost, Root::Symbol(_) | Root::Condition(_)) => continue,
                _ => {}
            }
            match root {
                Root::Symbol(place) => {
                    if let Some(()) = preserve(place) {
                        continue;
                    }
                    let NodeId::Expr(value) = node else {
                        unreachable!("symbol roots hold expressions");
                    };
                    symbols.push((place, graph.invalidate_expr(value, change, affected)?));
                }
                Root::Condition(condition) => {
                    conditions.insert(
                        condition,
                        graph.invalidate_condition(condition, change, affected)?,
                    );
                }
                Root::Lost(fact) => {
                    let condition = graph.invalidate_condition(fact.condition, change, affected)?;
                    lost.insert(fact.clone(), Some(Invalidated { condition, ..fact }));
                }
                Root::Transient => unreachable!("transient roots are detached before state edits"),
            }
        }
        let mut next_conditions = self.data.conditions.clone();
        let mut next_lost = self.data.lost.clone();
        context
            .sequences
            .map_conditions(&mut next_conditions, graph, &conditions)?;
        context.sequences.edit_lost(&mut next_lost, graph, &lost)?;
        let mut condition_counts = self.condition_counts.clone();
        let mut counts = Vec::new();
        for (condition, replacement) in conditions {
            let count = context
                .condition_counts
                .remove(&mut condition_counts, &condition)?
                .expect("affected condition is a fact");
            counts.push((replacement, count));
        }
        for (condition, count) in counts {
            let previous = context
                .condition_counts
                .get(condition_counts, &condition)
                .copied()
                .unwrap_or(0);
            context
                .condition_counts
                .insert(&mut condition_counts, condition, previous + count)?;
        }
        let mut lost_counts = self.lost_counts.clone();
        let mut counts = Vec::new();
        for (fact, replacement) in lost {
            let count = context
                .lost_counts
                .remove(&mut lost_counts, &fact)?
                .expect("affected lost condition is a fact");
            if let Some(fact) = replacement {
                counts.push((fact, count));
            }
        }
        for (fact, count) in counts {
            let previous = context
                .lost_counts
                .get(lost_counts, &fact)
                .copied()
                .unwrap_or(0);
            context
                .lost_counts
                .insert(&mut lost_counts, fact, previous + count)?;
        }
        // Attach replacement roots before retiring any old roots they may share.
        for (condition, difference) in Differences::from((
            &context.condition_counts,
            self.condition_counts,
            condition_counts,
        )) {
            if let Difference::Right(_) = difference {
                self.dependencies.insert(
                    &mut context.dependencies,
                    Root::Condition(*condition),
                    NodeId::Condition(*condition),
                    graph,
                )?;
            }
        }
        for (fact, difference) in
            Differences::from((&context.lost_counts, self.lost_counts, lost_counts))
        {
            if let Difference::Right(_) = difference {
                self.dependencies.insert(
                    &mut context.dependencies,
                    Root::Lost(fact.clone()),
                    NodeId::Condition(fact.condition),
                    graph,
                )?;
            }
        }
        for (place, value) in &symbols {
            self.dependencies.insert(
                &mut context.dependencies,
                Root::Symbol(*place),
                NodeId::Expr(*value),
                graph,
            )?;
        }
        for (condition, difference) in Differences::from((
            &context.condition_counts,
            self.condition_counts,
            condition_counts,
        )) {
            if let Difference::Left(_) = difference {
                self.dependencies.remove(
                    &mut context.dependencies,
                    &Root::Condition(*condition),
                    graph,
                )?;
            }
        }
        for (fact, difference) in
            Differences::from((&context.lost_counts, self.lost_counts, lost_counts))
        {
            if let Difference::Left(_) = difference {
                self.dependencies.remove(
                    &mut context.dependencies,
                    &Root::Lost(fact.clone()),
                    graph,
                )?;
            }
        }
        self.condition_counts = condition_counts;
        self.lost_counts = lost_counts;
        self.data.conditions = next_conditions;
        self.data.lost = next_lost;
        for (place, value) in symbols {
            self.insert(place, value, graph, context)?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Active<'s, 'g, R> {
    transparent_parents: Set<'s, NodeId<'g>>,
    location_fields: Set<'s, ExprId<'g>>,
    roots: Set<'s, R>,
    location: Option<ExprId<'g>>,
}

pub struct DependencyStores<'s, 'g, R> {
    nodes: Maps<'s, NodeId<'g>, Active<'s, 'g, R>>,
    roots: Maps<'s, R, NodeId<'g>>,
    locals: Maps<'s, Local, Set<'s, NodeId<'g>>>,
    node_sets: Maps<'s, NodeId<'g>, ()>,
    expr_sets: Maps<'s, ExprId<'g>, ()>,
    root_sets: Maps<'s, R, ()>,
    affected: FxHashMap<
        (
            Map<'s, NodeId<'g>, Active<'s, 'g, R>>,
            Map<'s, Local, Set<'s, NodeId<'g>>>,
            GraphInvalidation<'g>,
        ),
        Affected<'g>,
    >,
}
impl<'s, 'g, R> DependencyStores<'s, 'g, R> {
    fn new() -> Self {
        Self {
            nodes: Maps::new(),
            roots: Maps::new(),
            locals: Maps::new(),
            node_sets: Maps::new(),
            expr_sets: Maps::new(),
            root_sets: Maps::new(),
            affected: FxHashMap::default(),
        }
    }
}
pub fn with_dependencies<'g, R, T>(
    f: impl for<'s> FnOnce(&mut DependencyStores<'s, 'g, R>) -> T,
) -> T {
    let mut stores = DependencyStores::new();
    f(&mut stores)
}

/// Retains only direct edges reachable from the current facts.
pub struct Dependencies<'s, 'g, R> {
    nodes: Map<'s, NodeId<'g>, Active<'s, 'g, R>>,
    roots: Map<'s, R, NodeId<'g>>,
    locals: Map<'s, Local, Set<'s, NodeId<'g>>>,
}
impl<R> Default for Dependencies<'_, '_, R> {
    fn default() -> Self {
        Self {
            nodes: Map::EMPTY,
            roots: Map::EMPTY,
            locals: Map::EMPTY,
        }
    }
}
impl<R> Copy for Dependencies<'_, '_, R> {}
impl<R> Clone for Dependencies<'_, '_, R> {
    fn clone(&self) -> Self {
        *self
    }
}

fn local<'g>(graph: &Graph<'g>, node: NodeId<'g>) -> Option<Local> {
    let NodeId::Expr(id) = node else {
        return None;
    };
    match &graph[id] {
        ExprNode::Opaque(origin) | ExprNode::Call(_, _, Some(origin)) => {
            graph.origin_local(*origin)
        }
        ExprNode::Cursor { local, .. } => Some(*local),
        _ => None,
    }
}

fn children<'g>(graph: &Graph<'g>, node: NodeId<'g>) -> FxHashSet<NodeId<'g>> {
    let mut children = FxHashSet::default();
    graph.visit_children(node, |child| {
        children.insert(child);
    });
    children
}

impl<'s, 'g, R: Clone + Eq + Hash> Dependencies<'s, 'g, R> {
    pub fn insert(
        &mut self,
        stores: &mut DependencyStores<'s, 'g, R>,
        root: R,
        node: NodeId<'g>,
        graph: &Graph<'g>,
    ) -> Result<usize, CapacityError> {
        if stores.roots.get(self.roots, &root) == Some(&node) {
            return Ok(0);
        }
        enum Work<'g> {
            Visit(NodeId<'g>),
            Build(NodeId<'g>, FxHashSet<NodeId<'g>>),
        }
        let mut next = *self;
        let before = stores.nodes.len(next.nodes);
        let mut pending = Vec::new();
        match stores.nodes.get(next.nodes, &node) {
            Some(active) => {
                let mut active = active.clone();
                stores
                    .root_sets
                    .insert(&mut active.roots, root.clone(), ())?;
                stores.nodes.insert(&mut next.nodes, node, active)?;
            }
            None => pending.push(Work::Visit(node)),
        }
        let root_node = node;
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(node) => {
                    if let Some(_) = stores.nodes.get(next.nodes, &node) {
                        continue;
                    }
                    let children = children(graph, node);
                    let position = pending.len();
                    pending.extend(children.iter().copied().map(Work::Visit));
                    pending.insert(position, Work::Build(node, children));
                }
                Work::Build(node, children) => {
                    if let Some(_) = stores.nodes.get(next.nodes, &node) {
                        continue;
                    }
                    let mut location = match node {
                        NodeId::Expr(id) => match &graph[id] {
                            ExprNode::Argument(_) => Some(id),
                            ExprNode::Opaque(origin) => graph[*origin].identity.map(|_| id),
                            _ => None,
                        },
                        NodeId::Condition(_) | NodeId::Choice(_) => None,
                    };
                    for child in children {
                        let mut active = stores
                            .nodes
                            .get(next.nodes, &child)
                            .expect("child is active")
                            .clone();
                        if let NodeId::Expr(id) = node
                            && let ExprNode::Field(parent, _) = graph[id]
                            && child == NodeId::Expr(parent)
                        {
                            location = active.location;
                        }
                        match (location, node) {
                            (Some(_), NodeId::Expr(id)) => {
                                stores
                                    .expr_sets
                                    .insert(&mut active.location_fields, id, ())?;
                            }
                            _ => {
                                stores.node_sets.insert(
                                    &mut active.transparent_parents,
                                    node,
                                    (),
                                )?;
                            }
                        }
                        stores.nodes.insert(&mut next.nodes, child, active)?;
                    }
                    let mut roots = Set::EMPTY;
                    if node == root_node {
                        stores.root_sets.insert(&mut roots, root.clone(), ())?;
                    }
                    stores.nodes.insert(
                        &mut next.nodes,
                        node,
                        Active {
                            transparent_parents: Set::EMPTY,
                            location_fields: Set::EMPTY,
                            roots,
                            location,
                        },
                    )?;
                    if let Some(local) = local(graph, node) {
                        let mut nodes = stores
                            .locals
                            .get(next.locals, &local)
                            .copied()
                            .unwrap_or(Set::EMPTY);
                        stores.node_sets.insert(&mut nodes, node, ())?;
                        stores.locals.insert(&mut next.locals, local, nodes)?;
                    }
                }
            }
        }
        let attached = stores.nodes.len(next.nodes) - before;
        if let Some(previous) = stores.roots.insert(&mut next.roots, root.clone(), node)? {
            next.detach(stores, previous, &root, graph)?;
        }
        *self = next;
        Ok(attached)
    }
    pub fn remove(
        &mut self,
        stores: &mut DependencyStores<'s, 'g, R>,
        root: &R,
        graph: &Graph<'g>,
    ) -> Result<(), CapacityError> {
        let mut next = *self;
        if let Some(node) = stores.roots.remove(&mut next.roots, root)? {
            next.detach(stores, node, root, graph)?;
            *self = next;
        }
        Ok(())
    }
    fn detach(
        &mut self,
        stores: &mut DependencyStores<'s, 'g, R>,
        node: NodeId<'g>,
        root: &R,
        graph: &Graph<'g>,
    ) -> Result<(), CapacityError> {
        let mut active = stores
            .nodes
            .get(self.nodes, &node)
            .expect("node is active")
            .clone();
        stores.root_sets.remove(&mut active.roots, root)?;
        stores.nodes.insert(&mut self.nodes, node, active)?;
        let mut pending = vec![node];
        while let Some(node) = pending.pop() {
            let Some(active) = stores.nodes.get(self.nodes, &node) else {
                continue;
            };
            if stores.node_sets.len(active.transparent_parents) != 0
                || stores.expr_sets.len(active.location_fields) != 0
                || stores.root_sets.len(active.roots) != 0
            {
                continue;
            }
            let location = active.location;
            stores.nodes.remove(&mut self.nodes, &node)?;
            if let Some(local) = local(graph, node) {
                let mut nodes = *stores
                    .locals
                    .get(self.locals, &local)
                    .expect("local nodes exist");
                stores.node_sets.remove(&mut nodes, &node)?;
                if stores.node_sets.len(nodes) == 0 {
                    stores.locals.remove(&mut self.locals, &local)?;
                } else {
                    stores.locals.insert(&mut self.locals, local, nodes)?;
                }
            }
            for child in children(graph, node) {
                let mut active = stores
                    .nodes
                    .get(self.nodes, &child)
                    .expect("child is active")
                    .clone();
                match (location, node) {
                    (Some(_), NodeId::Expr(id)) => {
                        stores.expr_sets.remove(&mut active.location_fields, &id)?;
                    }
                    _ => {
                        stores
                            .node_sets
                            .remove(&mut active.transparent_parents, &node)?;
                    }
                }
                stores.nodes.insert(&mut self.nodes, child, active)?;
                pending.push(child);
            }
        }
        Ok(())
    }
    pub fn affected(
        &self,
        stores: &mut DependencyStores<'s, 'g, R>,
        change: GraphInvalidation<'g>,
        graph: &mut Graph<'g>,
    ) -> Result<Affected<'g>, CapacityError> {
        let key = (self.nodes, self.locals, change);
        if let Some(affected) = stores.affected.get(&key) {
            return Ok(*affected);
        }
        let mut pending = Vec::new();
        match change {
            GraphInvalidation::Local(local) => {
                if let Some(nodes) = stores.locals.get(self.locals, &local) {
                    pending.extend(stores.node_sets.iter(*nodes).map(|(node, ())| *node));
                }
            }
            GraphInvalidation::Memory(target) | GraphInvalidation::Replace { target, .. } => {
                let mut ancestors = Vec::new();
                let mut current = target;
                loop {
                    ancestors.push(current);
                    match &graph[current] {
                        ExprNode::Field(parent, _) => current = *parent,
                        ExprNode::Argument(_) => break,
                        ExprNode::Opaque(origin) => match graph[*origin].identity {
                            Some(_) => break,
                            None => {
                                stores.affected.insert(key, Affected::EMPTY);
                                return Ok(Affected::EMPTY);
                            }
                        },
                        _ => {
                            stores.affected.insert(key, Affected::EMPTY);
                            return Ok(Affected::EMPTY);
                        }
                    }
                }
                pending.extend(ancestors.into_iter().map(NodeId::Expr).filter(|node| {
                    match stores.nodes.get(self.nodes, node) {
                        Some(_) => true,
                        None => false,
                    }
                }));
                let mut descendants = vec![target];
                while let Some(node) = descendants.pop() {
                    let Some(active) = stores.nodes.get(self.nodes, &NodeId::Expr(node)) else {
                        continue;
                    };
                    for (field, ()) in stores.expr_sets.iter(active.location_fields) {
                        pending.push(NodeId::Expr(*field));
                        descendants.push(*field);
                    }
                }
            }
        }
        let mut affected = FxHashSet::default();
        while let Some(node) = pending.pop() {
            if !affected.insert(node) {
                continue;
            }
            let Some(active) = stores.nodes.get(self.nodes, &node) else {
                continue;
            };
            pending.extend(
                stores
                    .node_sets
                    .iter(active.transparent_parents)
                    .map(|(node, ())| *node),
            );
            match change {
                GraphInvalidation::Local(_) => pending.extend(
                    stores
                        .expr_sets
                        .iter(active.location_fields)
                        .map(|(node, ())| NodeId::Expr(*node)),
                ),
                GraphInvalidation::Memory(_) | GraphInvalidation::Replace { .. } => {}
            }
        }
        let affected = graph.intern_affected(affected)?;
        stores.affected.insert(key, affected);
        Ok(affected)
    }
    pub fn roots(
        &self,
        stores: &DependencyStores<'s, 'g, R>,
        graph: &Graph<'g>,
        affected: Affected<'g>,
    ) -> FxHashMap<R, NodeId<'g>> {
        let mut roots = FxHashMap::default();
        for node in graph.members(affected) {
            if let Some(active) = stores.nodes.get(self.nodes, &node) {
                roots.extend(
                    stores
                        .root_sets
                        .iter(active.roots)
                        .map(|(root, ())| (root.clone(), node)),
                );
            }
        }
        roots
    }
}
