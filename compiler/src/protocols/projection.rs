use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexSet};
use rustc_data_structures::union_find::UnionFind;
use rustc_index::IndexVec;

use crate::contracts::Order;
use crate::contracts::graph::sets::{Combination, SetId, Sets};
use crate::contracts::graph::{
    CapacityError, ConditionId, ConditionNode, ExprId, ExprNode, Graph, GuardContextId, NodeId,
};
use crate::persistent::{self, Composition, Identical, Map};
use crate::sequence::{Fold, Part, Rewrite, Selection, Sequence, Sequences, Transform};

use crate::protocols::{Flow, Subject};

rustc_index::newtype_index! {
    #[max = 0xffff_ffff]
    struct Component {}
}

type Members<'p> = SetId<'p, Component>;
type Groups<'p, 'g> = Map<'p, Component, Sequence<'g, ConditionId<'g>>>;
type Merge<'g> = fn(
    &mut Sequences<'g, ConditionId<'g>>,
    &Sequence<'g, ConditionId<'g>>,
    &Sequence<'g, ConditionId<'g>>,
) -> Result<Sequence<'g, ConditionId<'g>>, CapacityError>;

#[derive(Clone, Copy)]
enum Endpoints<'g> {
    Empty,
    One(ExprId<'g>),
    Many,
}

#[derive(Clone, Copy)]
enum Numeric<'g> {
    Unanchored(Endpoints<'g>),
    Anchored(Endpoints<'g>),
}

impl<'g> Numeric<'g> {
    fn endpoint(self, endpoint: ExprId<'g>) -> Self {
        let merge = |previous| match previous {
            Endpoints::Empty => Endpoints::One(endpoint),
            Endpoints::One(previous) if previous == endpoint => Endpoints::One(endpoint),
            Endpoints::One(_) | Endpoints::Many => Endpoints::Many,
        };
        match self {
            Self::Unanchored(previous) => Self::Unanchored(merge(previous)),
            Self::Anchored(previous) => Self::Anchored(merge(previous)),
        }
    }
}

#[derive(Clone, Copy)]
enum Certificate {
    Unanchored,
    Scalar,
    Retain,
}

#[derive(Clone, Copy)]
enum Bounds {
    Interval { lower: u128, upper: u128 },
    Contradictory,
}

impl Bounds {
    fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Interval { lower: a, upper: b }, Self::Interval { lower: c, upper: d }) => {
                let (lower, upper) = (a.max(c), b.min(d));
                match lower <= upper {
                    true => Self::Interval { lower, upper },
                    false => Self::Contradictory,
                }
            }
            _ => Self::Contradictory,
        }
    }
}

#[derive(Clone, Copy)]
struct Guard {
    component: Component,
    bounds: Bounds,
}

#[derive(Clone)]
struct Summary<'p, 'g> {
    members: Members<'p>,
    groups: Groups<'p, 'g>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Context<'p> {
    Requested(Members<'p>),
    Retained(Members<'p>),
}

struct Operation<'p, 'g> {
    sets: Sets<'p, Component>,
    guards: FxHashMap<ConditionId<'g>, Guard>,
    certificates: IndexVec<Component, Certificate>,
    maps: persistent::Maps<'p, Component, Sequence<'g, ConditionId<'g>>>,
    groups: Composition<'p, Component, Sequence<'g, ConditionId<'g>>, Merge<'g>>,
    hazards: persistent::Fold<'p, Component, Sequence<'g, ConditionId<'g>>, Members<'p>>,
    bounds: Fold<'g, ConditionId<'g>, Bounds>,
}

impl<'p, 'g> Rewrite<'g, ConditionId<'g>> for Operation<'p, 'g> {
    type Summary = Summary<'p, 'g>;
    type Context = Context<'p>;
    type Error = CapacityError;

    fn summarize(
        &mut self,
        arena: &mut Sequences<'g, ConditionId<'g>>,
        part: Part<'_, ConditionId<'g>, Summary<'p, 'g>>,
    ) -> Result<Summary<'p, 'g>, CapacityError> {
        match part {
            Part::Leaf(guard) => {
                let component = self.guards[guard].component;
                let mut groups = Map::EMPTY;
                let group = arena.from_iter([*guard])?;
                self.maps.insert(&mut groups, component, group)?;
                Ok(Summary {
                    members: self.sets.insert(SetId::EMPTY, component)?,
                    groups,
                })
            }
            Part::Branch(left, right) => Ok(Summary {
                members: self
                    .sets
                    .combine(Combination::Union, left.members, right.members)?,
                groups: self
                    .groups
                    .compose(&mut self.maps, arena, left.groups, right.groups)?,
            }),
        }
    }

    fn normalize(
        &mut self,
        arena: &mut Sequences<'g, ConditionId<'g>>,
        summary: &Summary<'p, 'g>,
        context: &Context<'p>,
    ) -> Result<Context<'p>, CapacityError> {
        let requested = match *context {
            Context::Retained(keep) => {
                return Ok(Context::Retained(self.sets.combine(
                    Combination::Intersection,
                    keep,
                    summary.members,
                )?));
            }
            Context::Requested(requested) if requested == SetId::EMPTY => {
                return Ok(Context::Retained(SetId::EMPTY));
            }
            Context::Requested(requested) => requested,
        };
        let Operation {
            sets,
            guards,
            certificates,
            maps,
            groups: _,
            hazards,
            bounds,
        } = self;
        let hazards = hazards
            .fold(maps, summary.groups, |part| match part {
                persistent::Part::Leaf(component, group) => {
                    let certificate = match certificates[*component] {
                        Certificate::Unanchored => return Ok(SetId::EMPTY),
                        Certificate::Retain => Bounds::Contradictory,
                        Certificate::Scalar => bounds
                            .fold(
                                arena,
                                |arena| arena,
                                *group,
                                |_, part| {
                                    Ok::<_, CapacityError>(match part {
                                        Part::Leaf(guard) => guards[guard].bounds,
                                        Part::Branch(left, right) => left.meet(*right),
                                    })
                                },
                            )?
                            .expect("a component has at least one guard"),
                    };
                    match certificate {
                        Bounds::Contradictory => sets.insert(SetId::EMPTY, *component),
                        _ => Ok(SetId::EMPTY),
                    }
                }
                persistent::Part::Branch(left, right) => {
                    sets.combine(Combination::Union, *left, *right)
                }
            })?
            .map(|value| *value)
            .unwrap_or(SetId::EMPTY);
        let keep = sets.combine(Combination::Union, requested, hazards)?;
        Ok(Context::Retained(sets.combine(
            Combination::Intersection,
            keep,
            summary.members,
        )?))
    }

    fn select(
        &mut self,
        _: &mut Sequences<'g, ConditionId<'g>>,
        summary: &Summary<'p, 'g>,
        context: &Context<'p>,
    ) -> Result<Selection, CapacityError> {
        Ok(match context {
            Context::Retained(keep) if *keep == SetId::EMPTY => Selection::Drop,
            Context::Retained(keep) if *keep == summary.members => Selection::Keep,
            Context::Retained(_) => Selection::Visit,
            Context::Requested(_) => {
                unreachable!("selection follows fragment context normalization")
            }
        })
    }

    fn value(
        &mut self,
        _: &mut Sequences<'g, ConditionId<'g>>,
        _: &ConditionId<'g>,
        _: &Context<'p>,
    ) -> Result<Option<ConditionId<'g>>, CapacityError> {
        unreachable!("a single-component guard fragment is kept or dropped as a whole")
    }
}

pub(crate) struct Projection<'p, 'g> {
    support: FxHashMap<Subject<'g>, Members<'p>>,
    contexts: FxHashMap<(Subject<'g>, GuardContextId<'g>), GuardContextId<'g>>,
    transform: Transform<'g, ConditionId<'g>, Operation<'p, 'g>>,
}

impl<'p, 'g> Projection<'p, 'g> {
    pub(crate) fn try_new(
        graph: &mut Graph<'g>,
        roots: impl IntoIterator<Item = Subject<'g>>,
        guards: impl IntoIterator<Item = Sequence<'g, ConditionId<'g>>>,
    ) -> Result<Self, CapacityError> {
        let mut conditions = FxHashSet::default();
        let mut guard_nodes = Fold::<ConditionId<'g>, ()>::default();
        for guards in guards {
            guard_nodes.fold(
                graph,
                |graph| graph.as_ref(),
                guards,
                |_, part| {
                    if let Part::Leaf(condition) = part {
                        conditions.insert(*condition);
                    }
                    Ok::<_, CapacityError>(())
                },
            )?;
        }
        let mut children = FxHashMap::default();
        let mut selects = FxHashMap::default();
        let mut pending = roots.into_iter().collect::<Vec<_>>();
        while let Some(subject) = pending.pop() {
            if children.contains_key(&subject) {
                continue;
            }
            let next = match subject {
                Subject::Prefix(prefix) => graph[prefix]
                    .previous
                    .into_iter()
                    .map(Subject::Prefix)
                    .chain(std::iter::once(Subject::Flow(graph[prefix].value)))
                    .collect::<Vec<_>>(),
                Subject::Flow(flow) => match graph[flow] {
                    Flow::Incoming
                    | Flow::Unknown
                    | Flow::Ready
                    | Flow::Dirty { .. }
                    | Flow::Alternatives(None) => Vec::new(),
                    Flow::Alternatives(Some(prefix)) => vec![Subject::Prefix(prefix)],
                    Flow::Call { input, .. } => vec![Subject::Flow(input)],
                    Flow::Select(condition, yes, no) => {
                        selects.insert(subject, condition);
                        conditions.insert(condition);
                        conditions.insert(graph.negate(condition)?);
                        vec![Subject::Flow(yes), Subject::Flow(no)]
                    }
                },
            };
            pending.extend(next.iter().copied());
            children.insert(subject, next);
        }

        let mut nodes: FxIndexSet<_> = conditions.iter().copied().map(NodeId::Condition).collect();
        let mut pending: Vec<_> = nodes.iter().copied().collect();
        while let Some(node) = pending.pop() {
            graph.visit_children(node, |child| {
                if let NodeId::Expr(expression) = child
                    && let ExprNode::Number(_) = graph[expression]
                {
                    return;
                }
                if nodes.insert(child) {
                    pending.push(child);
                }
            });
        }
        // Union the subgraph on the retained nodes without buffering its edges.
        let mut incidence = UnionFind::new(nodes.len());
        let indexed_nodes = nodes.iter().enumerate();
        for (parent, &node) in indexed_nodes {
            graph.visit_children(node, |child| {
                if let Some(index) = nodes.get_index_of(&child) {
                    incidence.unify(parent, index);
                }
            });
        }
        let mut components = FxHashMap::default();
        let mut roots = FxHashMap::default();
        let mut numeric: IndexVec<Component, Numeric<'g>> = IndexVec::new();
        let indexed_nodes = nodes.into_iter().enumerate();
        for (index, node) in indexed_nodes {
            let root = incidence.find(index);
            let component = match roots.entry(root) {
                std::collections::hash_map::Entry::Occupied(entry) => *entry.get(),
                std::collections::hash_map::Entry::Vacant(entry) => {
                    u32::try_from(numeric.len()).map_err(|_| CapacityError::Sets)?;
                    *entry.insert(numeric.push(Numeric::Unanchored(Endpoints::Empty)))
                }
            };
            components.insert(node, component);
        }
        for condition in &conditions {
            if let ConditionNode::Compare(_, left, right) = graph[*condition] {
                let component = components[&NodeId::Condition(*condition)];
                for expression in [left, right] {
                    numeric[component] = match graph[expression] {
                        ExprNode::Number(_) => match numeric[component] {
                            Numeric::Unanchored(endpoints) | Numeric::Anchored(endpoints) => {
                                Numeric::Anchored(endpoints)
                            }
                        },
                        _ => numeric[component].endpoint(expression),
                    };
                }
            }
        }
        let certificates = numeric
            .into_iter()
            .map(|numeric| match numeric {
                Numeric::Unanchored(_) => Certificate::Unanchored,
                Numeric::Anchored(Endpoints::One(_)) => Certificate::Scalar,
                Numeric::Anchored(Endpoints::Empty | Endpoints::Many) => Certificate::Retain,
            })
            .collect::<IndexVec<_, _>>();
        let mut classified = FxHashMap::default();
        for condition in conditions {
            let component = components[&NodeId::Condition(condition)];
            let free = Bounds::Interval {
                lower: 0,
                upper: u128::MAX,
            };
            let bounds = match graph[condition] {
                ConditionNode::Compare(order, left, right) => {
                    match (&graph[left], &graph[right], order) {
                        (ExprNode::Number(left), ExprNode::Number(right), order) => match order {
                            Order::Less if left < right => free,
                            Order::LessEqual if left <= right => free,
                            Order::Equal if left == right => free,
                            Order::NotEqual if left != right => free,
                            _ => Bounds::Contradictory,
                        },
                        (_, ExprNode::Number(value), Order::Less) => match value.checked_sub(1) {
                            Some(upper) => Bounds::Interval { lower: 0, upper },
                            None => Bounds::Contradictory,
                        },
                        (_, ExprNode::Number(upper), Order::LessEqual) => Bounds::Interval {
                            lower: 0,
                            upper: *upper,
                        },
                        (ExprNode::Number(value), _, Order::Less) => match value.checked_add(1) {
                            Some(lower) => Bounds::Interval {
                                lower,
                                upper: u128::MAX,
                            },
                            None => Bounds::Contradictory,
                        },
                        (ExprNode::Number(lower), _, Order::LessEqual) => Bounds::Interval {
                            lower: *lower,
                            upper: u128::MAX,
                        },
                        (_, ExprNode::Number(value), Order::Equal)
                        | (ExprNode::Number(value), _, Order::Equal) => Bounds::Interval {
                            lower: *value,
                            upper: *value,
                        },
                        (_, _, Order::Less) if left == right => Bounds::Contradictory,
                        _ => free,
                    }
                }
                _ => free,
            };
            classified.insert(condition, Guard { component, bounds });
        }
        let mut sets = Sets::new();
        let mut support = FxHashMap::default();
        enum Work<'g> {
            Visit(Subject<'g>),
            Build(Subject<'g>),
        }
        let mut pending = children
            .keys()
            .copied()
            .map(Work::Visit)
            .collect::<Vec<_>>();
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(subject) => {
                    if support.contains_key(&subject) {
                        continue;
                    }
                    pending.push(Work::Build(subject));
                    pending.extend(children[&subject].iter().copied().map(Work::Visit));
                }
                Work::Build(subject) => {
                    let mut members = SetId::EMPTY;
                    if let Some(condition) = selects.get(&subject) {
                        members =
                            sets.insert(members, components[&NodeId::Condition(*condition)])?;
                    }
                    for child in &children[&subject] {
                        members = sets.combine(Combination::Union, members, support[child])?;
                    }
                    support.insert(subject, members);
                }
            }
        }
        let operation = Operation {
            sets,
            guards: classified,
            certificates,
            maps: persistent::Maps::new(),
            groups: Composition::new(Identical::Combine, |arena, left, right| {
                arena.append(*left, *right)
            }),
            hazards: persistent::Fold::default(),
            bounds: Fold::default(),
        };
        Ok(Self {
            support,
            contexts: FxHashMap::default(),
            transform: Transform::new(operation),
        })
    }

    pub(crate) fn project(
        &mut self,
        graph: &mut Graph<'g>,
        subject: Subject<'g>,
        context: GuardContextId<'g>,
    ) -> Result<GuardContextId<'g>, CapacityError> {
        if let Some(projected) = self.contexts.get(&(subject, context)) {
            return Ok(*projected);
        }
        let sequence = context.0;
        let sequence = self.transform.apply(
            graph.as_mut(),
            sequence,
            Context::Requested(self.support[&subject]),
        )?;
        let projected = GuardContextId::from(sequence);
        self.contexts.insert((subject, context), projected);
        Ok(projected)
    }
}
