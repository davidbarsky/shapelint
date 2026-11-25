use std::collections::VecDeque;
use std::ops::ControlFlow;

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::{FxHashMap, FxIndexMap};
use rustc_index::IndexVec;

use crate::contracts::graph::CapacityError;
use crate::contracts::schedule::{self, Engine, Finished, Lookup, Session};
use crate::persistent::{Map, Maps};
use crate::regions::matching::{
    Binding, BodyKey, ComponentId, Entry, Frozen, Phase, Point, Query, Registered, Selector,
    Summaries, TypedLocal,
};
use crate::sequence::{Sequence, Sequences};

pub type PathId = Sequence<'static, usize>;

#[derive(Clone, Copy)]
enum Part {
    Step(usize),
    Concat(PathId, PathId),
}

pub struct Paths {
    sequences: Sequences<'static, usize>,
    parts: FxHashMap<PathId, Part>,
    joined: FxHashMap<(PathId, PathId), PathId>,
}

impl Default for Paths {
    fn default() -> Self {
        Self {
            sequences: Sequences::new(),
            parts: FxHashMap::default(),
            joined: FxHashMap::default(),
        }
    }
}

impl Paths {
    fn step(&mut self, port: usize) -> Result<PathId, CapacityError> {
        let id = self.sequences.push(Sequence::EMPTY, port)?;
        self.parts.entry(id).or_insert(Part::Step(port));
        Ok(id)
    }

    fn join(&mut self, left: PathId, right: PathId) -> Result<PathId, CapacityError> {
        if let Some(id) = self.joined.get(&(left, right)) {
            return Ok(*id);
        }
        let id = self.sequences.append(left, right)?;
        self.parts.entry(id).or_insert(Part::Concat(left, right));
        self.joined.insert((left, right), id);
        Ok(id)
    }

    fn follow<'g>(
        &self,
        context: Context,
        path: PathId,
        bodies: &IndexVec<BodyKey, Registered<'g>>,
        frozen: &Frozen<'g>,
    ) -> ControlFlow<Option<Context>, (PathId, PathId)> {
        let port = match self.parts[&path] {
            Part::Concat(left, right) => return ControlFlow::Continue((left, right)),
            Part::Step(port) => port,
        };
        if Some(context.point.block) == context.boundary {
            return ControlFlow::Break(None);
        }
        let body = &bodies[context.point.body];
        let current = &frozen[(body.blocks, context.point.block.index())];
        let Some(&block) = frozen.successors.get(current.successors, port) else {
            return ControlFlow::Break(None);
        };
        let entry = context.entry.filter(|entry| {
            frozen[(body.blocks, entry.block.index())].component
                == frozen[(body.blocks, block.index())].component
        });
        let start = Entry::start_in(entry, block);
        ControlFlow::Break(Some(Context {
            point: Point {
                body: context.point.body,
                block,
                start,
            },
            boundary: context.boundary,
            entry,
        }))
    }
}

#[derive(Clone, Copy)]
struct Group {
    to_hub: Map<'static, Query, Option<PathId>>,
    from_hub: Map<'static, Query, Option<PathId>>,
    exits: Sequence<'static, (ComponentId, PathId)>,
}

pub struct Routes {
    groups: IndexVec<ComponentId, Group>,
    maps: Maps<'static, Query, Option<PathId>>,
    exits: Sequences<'static, (ComponentId, PathId)>,
    completed: FxHashMap<(ComponentId, ComponentId), Option<Option<PathId>>>,
}
impl Default for Routes {
    fn default() -> Self {
        Self {
            groups: IndexVec::new(),
            maps: Maps::new(),
            exits: Sequences::new(),
            completed: FxHashMap::default(),
        }
    }
}

impl Routes {
    fn prepare<V>(
        &mut self,
        summaries: &Summaries<Query, V>,
        paths: &mut Paths,
    ) -> Result<(), CapacityError> {
        let pending = summaries.components.iter().skip(self.groups.len());
        for component in pending {
            let id = self.groups.next_index();
            let hub = component.hub.0;
            let mut forward: FxHashMap<Query, Vec<(usize, Query)>> = FxHashMap::default();
            let mut reverse: FxHashMap<Query, Vec<(usize, Query)>> = FxHashMap::default();
            let mut exits = Vec::new();
            let members =
                std::iter::once(&component.hub).chain(summaries.nodes.iter(component.others));
            for (node, children) in members {
                let ports = summaries.children.iter(*children).enumerate();
                for (port, &child) in ports {
                    match summaries.groups[&child] == id {
                        true => {
                            forward.entry(*node).or_default().push((port, child));
                            reverse.entry(child).or_default().push((port, *node));
                        }
                        false => exits.push((*node, port, child)),
                    }
                }
            }
            let mut from_hub = FxHashMap::from_iter([(hub, None)]);
            let mut pending = VecDeque::from([hub]);
            while let Some(node) = pending.pop_front() {
                let children = forward.get(&node).into_iter().flatten();
                for &(port, child) in children {
                    if from_hub.contains_key(&child) {
                        continue;
                    }
                    let step = paths.step(port)?;
                    let path = match from_hub[&node] {
                        Some(prefix) => paths.join(prefix, step)?,
                        None => step,
                    };
                    from_hub.insert(child, Some(path));
                    pending.push_back(child);
                }
            }
            let mut to_hub = FxHashMap::from_iter([(hub, None)]);
            let mut pending = VecDeque::from([hub]);
            while let Some(node) = pending.pop_front() {
                let parents = reverse.get(&node).into_iter().flatten();
                for &(port, parent) in parents {
                    if to_hub.contains_key(&parent) {
                        continue;
                    }
                    let step = paths.step(port)?;
                    let path = match to_hub[&node] {
                        Some(tail) => paths.join(step, tail)?,
                        None => step,
                    };
                    to_hub.insert(parent, Some(path));
                    pending.push_back(parent);
                }
            }
            let mut targets = FxIndexMap::default();
            for (source, port, target) in exits {
                let group = summaries.groups[&target];
                if targets.contains_key(&group) {
                    continue;
                }
                let step = paths.step(port)?;
                let path = match from_hub[&source] {
                    Some(prefix) => paths.join(prefix, step)?,
                    None => step,
                };
                let path = match *self
                    .maps
                    .get(self.groups[group].to_hub, &target)
                    .expect("route target reaches its hub")
                {
                    Some(tail) => paths.join(path, tail)?,
                    None => path,
                };
                targets.insert(group, path);
            }
            let mut frozen_to = Map::EMPTY;
            for (query, path) in to_hub {
                self.maps.insert(&mut frozen_to, query, path)?;
            }
            let mut frozen_from = Map::EMPTY;
            for (query, path) in from_hub {
                self.maps.insert(&mut frozen_from, query, path)?;
            }
            let exits = self.exits.from_iter(targets)?;
            self.groups.push(Group {
                to_hub: frozen_to,
                from_hub: frozen_from,
                exits,
            });
        }
        Ok(())
    }

    pub fn path<V>(
        &mut self,
        from: Query,
        to: Query,
        summaries: &Summaries<Query, V>,
        paths: &mut Paths,
    ) -> Result<Option<PathId>, CapacityError> {
        if from == to {
            return Ok(None);
        }
        self.prepare(summaries, paths)?;
        let source = summaries.groups[&from];
        let target = summaries.groups[&to];
        let mut engine = Routing {
            routes: self,
            paths,
        };
        let between = schedule::evaluate(&mut engine, (source, target))?
            .expect("witness site is reachable from its summary");
        let segments = [
            *engine
                .routes
                .maps
                .get(engine.routes.groups[source].to_hub, &from)
                .expect("source reaches its hub"),
            between,
            *engine
                .routes
                .maps
                .get(engine.routes.groups[target].from_hub, &to)
                .expect("target follows its hub"),
        ];
        let mut path = None;
        for segment in segments {
            if let Some(next) = segment {
                path = Some(match path {
                    Some(previous) => engine.paths.join(previous, next)?,
                    None => next,
                });
            }
        }
        Ok(path)
    }
}

struct Routing<'a> {
    routes: &'a mut Routes,
    paths: &'a mut Paths,
}
impl Engine for Routing<'_> {
    type Query = (ComponentId, ComponentId);
    type Answer = Option<Option<PathId>>;
    type Error = CapacityError;
    type Frame = Self::Query;

    fn lookup(&mut self, query: &Self::Query) -> Result<Lookup<Self::Answer>, Self::Error> {
        Ok(match self.routes.completed.get(query) {
            Some(answer) => Lookup::Ready(*answer),
            None => Lookup::Missing,
        })
    }
    fn enter(&mut self, query: Self::Query) -> Result<Self::Frame, Self::Error> {
        Ok(query)
    }
    fn finish(
        &mut self,
        frame: Self::Frame,
        answer: Self::Answer,
    ) -> Finished<Self::Query, Self::Answer> {
        self.routes.completed.insert(frame, answer);
        Finished::Ready(answer)
    }
    async fn execute(
        session: Session<'_, Self>,
        (source, target): Self::Query,
    ) -> Result<Self::Answer, Self::Error> {
        if source == target {
            return Ok(Some(None));
        }
        if source < target {
            return Ok(None);
        }
        let mut index = 0;
        while let Some((child, prefix)) = session.with(|engine| {
            engine
                .routes
                .exits
                .get(engine.routes.groups[source].exits, index)
                .copied()
        }) {
            if let Some(tail) = session.query((child, target)).await? {
                let path = match tail {
                    Some(tail) => session.with(|engine| engine.paths.join(prefix, tail))?,
                    None => prefix,
                };
                return Ok(Some(Some(path)));
            }
            index += 1;
        }
        Ok(None)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Context {
    pub point: Point,
    pub boundary: Option<rustc_middle::mir::BasicBlock>,
    pub entry: Option<Entry>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Locator {
    pub path: Option<PathId>,
    pub selector: Selector,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Feature {
    Shape(Option<PathId>),
    Type { path: Option<PathId>, index: usize },
    Alias(Locator, Locator),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub enum Observation {
    Missing,
    Port(Fingerprint),
    Block {
        coroutine: Fingerprint,
        phase: Phase,
        suffix: Fingerprint,
        successors: usize,
        locals: usize,
    },
    Type(Fingerprint),
    Same,
    Different,
}

#[derive(Default)]
pub struct Observations {
    completed: FxHashMap<(Context, PathId), Option<Context>>,
    answers: FxHashMap<(Context, Feature), Observation>,
    pub(crate) reads: usize,
    pub(crate) evaluations: usize,
}

impl Observations {
    pub fn read<'g>(
        &mut self,
        source: Context,
        feature: Feature,
        bodies: &IndexVec<BodyKey, Registered<'g>>,
        paths: &Paths,
        sequences: &Sequences<'g, TypedLocal>,
        frozen: &Frozen<'g>,
    ) -> Result<Observation, CapacityError> {
        self.reads = self.reads.saturating_add(1);
        if let Some(answer) = self.answers.get(&(source, feature)) {
            return Ok(*answer);
        }
        self.evaluations = self.evaluations.saturating_add(1);
        let mut engine = Walking {
            observations: self,
            bodies,
            paths,
            frozen,
        };
        let mut endpoint = |path| match path {
            None => Ok(Some(source)),
            Some(path) => schedule::evaluate(&mut engine, (source, path)),
        };
        let observed = match feature {
            Feature::Shape(path) => match endpoint(path)? {
                None => Observation::Missing,
                Some(context) => {
                    let body = &bodies[context.point.body];
                    match Some(context.point.block) == context.boundary {
                        true => Observation::Port(body.coroutine),
                        false => {
                            let block = &frozen[(body.blocks, context.point.block.index())];
                            Observation::Block {
                                coroutine: body.coroutine,
                                phase: block.phase,
                                suffix: frozen[(block.suffixes, context.point.start)].fingerprint,
                                successors: frozen.successors.len(block.successors),
                                locals: sequences.len(
                                    frozen[(
                                        frozen[(body.blocks, context.point.block.index())].suffixes,
                                        context.point.start,
                                    )]
                                        .bindings,
                                ),
                            }
                        }
                    }
                }
            },
            Feature::Type { path, index } => match endpoint(path)? {
                Some(context) if Some(context.point.block) != context.boundary => {
                    let body = &bodies[context.point.body];
                    match sequences.get(
                        frozen[(
                            frozen[(body.blocks, context.point.block.index())].suffixes,
                            context.point.start,
                        )]
                            .bindings,
                        index,
                    ) {
                        Some(local) => Observation::Type(local.ty),
                        None => Observation::Missing,
                    }
                }
                None | Some(_) => Observation::Missing,
            },
            Feature::Alias(left, right) => {
                let left_context = endpoint(left.path)?;
                let right_context = endpoint(right.path)?;
                let binding = |context: Option<Context>, selector| {
                    let context = context?;
                    if Some(context.point.block) == context.boundary {
                        return None;
                    }
                    let Point { body, block, start } = context.point;
                    match selector {
                        Selector::Block => Some(Binding::Block(body, block)),
                        Selector::Local(index) => sequences
                            .get(
                                frozen[(
                                    frozen[(bodies[body].blocks, block.index())].suffixes,
                                    start,
                                )]
                                    .bindings,
                                index,
                            )
                            .map(|local| local.binding),
                    }
                };
                match (
                    binding(left_context, left.selector),
                    binding(right_context, right.selector),
                ) {
                    (Some(left), Some(right)) => match left == right {
                        true => Observation::Same,
                        false => Observation::Different,
                    },
                    _ => Observation::Missing,
                }
            }
        };
        self.answers.insert((source, feature), observed);
        Ok(observed)
    }
}

struct Walking<'a, 'g> {
    observations: &'a mut Observations,
    bodies: &'a IndexVec<BodyKey, Registered<'g>>,
    paths: &'a Paths,
    frozen: &'a Frozen<'g>,
}
impl Engine for Walking<'_, '_> {
    type Query = (Context, PathId);
    type Answer = Option<Context>;
    type Error = CapacityError;
    type Frame = Self::Query;

    fn lookup(&mut self, query: &Self::Query) -> Result<Lookup<Self::Answer>, Self::Error> {
        Ok(match self.observations.completed.get(query) {
            Some(answer) => Lookup::Ready(*answer),
            None => Lookup::Missing,
        })
    }
    fn enter(&mut self, query: Self::Query) -> Result<Self::Frame, Self::Error> {
        Ok(query)
    }
    fn finish(
        &mut self,
        frame: Self::Frame,
        answer: Self::Answer,
    ) -> Finished<Self::Query, Self::Answer> {
        self.observations.completed.insert(frame, answer);
        Finished::Ready(answer)
    }
    async fn execute(
        session: Session<'_, Self>,
        (context, path): Self::Query,
    ) -> Result<Self::Answer, Self::Error> {
        match session.with(|engine| {
            engine
                .paths
                .follow(context, path, engine.bodies, engine.frozen)
        }) {
            ControlFlow::Break(endpoint) => Ok(endpoint),
            ControlFlow::Continue((left, right)) => match session.query((context, left)).await? {
                Some(context) => session.query((context, right)).await,
                None => Ok(None),
            },
        }
    }
}
