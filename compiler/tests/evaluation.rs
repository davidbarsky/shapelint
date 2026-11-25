#![feature(rustc_private)]

use shapelint_driver::contracts::schedule::{Engine, Finished, Lookup, Session, evaluate};
use std::convert::Infallible;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct NodeId(usize);

#[derive(Clone)]
enum Node {
    Value(u128),
    Sum(Vec<NodeId>),
}

struct Arithmetic {
    nodes: Vec<Node>,
    answers: Vec<Option<u128>>,
    starts: Vec<usize>,
    prefixes: Vec<usize>,
}

impl Engine for Arithmetic {
    type Query = NodeId;
    type Answer = u128;
    type Error = Infallible;
    type Frame = NodeId;

    fn lookup(&mut self, NodeId(index): &NodeId) -> Result<Lookup<u128>, Infallible> {
        Ok(match self.answers[*index] {
            Some(answer) => Lookup::Ready(answer),
            None => Lookup::Missing,
        })
    }

    fn enter(&mut self, query: NodeId) -> Result<NodeId, Infallible> {
        self.starts[query.0] += 1;
        Ok(query)
    }

    fn finish(&mut self, query: NodeId, answer: u128) -> Finished<NodeId, u128> {
        self.answers[query.0] = Some(answer);
        Finished::Ready(answer)
    }

    async fn execute(session: Session<'_, Self>, query: NodeId) -> Result<u128, Infallible> {
        match session.with(|engine| engine.nodes[query.0].clone()) {
            Node::Value(value) => Ok(value),
            Node::Sum(children) => {
                let mut sum = 0;
                for child in children {
                    sum += session.query(child).await?;
                    session.with(|engine| engine.prefixes[query.0] += 1);
                }
                Ok(sum)
            }
        }
    }
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Leaves {
    values: Vec<u8>,
}

#[hegel::test(print_blob = true)]
fn completed_prefixes_are_processed_once_when_dependencies_suspend(tc: hegel::TestCase) {
    let Leaves { values } = tc.draw(hegel::generators::default::<Leaves>());
    let root = NodeId(values.len());
    let children = (0..values.len()).map(NodeId).collect();
    let mut nodes: Vec<_> = values
        .iter()
        .map(|value| Node::Value(u128::from(*value)))
        .collect();
    nodes.push(Node::Sum(children));
    let mut arithmetic = Arithmetic {
        answers: vec![None; nodes.len()],
        starts: vec![0; nodes.len()],
        prefixes: vec![0; nodes.len()],
        nodes,
    };
    let answer = evaluate(&mut arithmetic, root).unwrap();
    assert_eq!(
        answer,
        values.iter().map(|value| u128::from(*value)).sum::<u128>()
    );
    assert_eq!(arithmetic.prefixes[root.0], values.len());
    assert_eq!(arithmetic.starts, vec![1; values.len() + 1]);
    let prefixes = arithmetic.prefixes.clone();
    assert_eq!(evaluate(&mut arithmetic, root).unwrap(), answer);
    assert_eq!(arithmetic.prefixes, prefixes);
}

#[test]
fn a_shared_dependency_is_evaluated_once_in_a_diamond() {
    let mut arithmetic = Arithmetic {
        nodes: vec![
            Node::Value(7),
            Node::Sum(vec![NodeId(0)]),
            Node::Sum(vec![NodeId(0)]),
            Node::Sum(vec![NodeId(1), NodeId(2)]),
        ],
        answers: vec![None; 4],
        starts: vec![0; 4],
        prefixes: vec![0; 4],
    };
    assert_eq!(evaluate(&mut arithmetic, NodeId(3)).unwrap(), 14);
    assert_eq!(arithmetic.starts, vec![1, 1, 1, 1]);
    assert_eq!(arithmetic.prefixes, vec![0, 1, 1, 2]);
}

#[test]
fn a_deep_dependency_chain_uses_the_scheduler_stack() {
    let depth = 100_000;
    let mut nodes = vec![Node::Value(7)];
    nodes.extend((0..depth).map(|index| Node::Sum(vec![NodeId(index)])));
    let mut arithmetic = Arithmetic {
        answers: vec![None; nodes.len()],
        starts: vec![0; nodes.len()],
        prefixes: vec![0; nodes.len()],
        nodes,
    };
    assert_eq!(evaluate(&mut arithmetic, NodeId(depth)).unwrap(), 7);
    assert_eq!(arithmetic.starts, vec![1; depth + 1]);
    assert_eq!(arithmetic.prefixes[0], 0);
    assert_eq!(arithmetic.prefixes[1..], vec![1; depth]);
}

#[derive(Clone, Copy)]
enum Revision {
    Initial,
    Refined,
}

struct Refinement {
    revision: Revision,
    starts: usize,
    completed: Vec<usize>,
}

impl Engine for Refinement {
    type Query = ();
    type Answer = usize;
    type Error = Infallible;
    type Frame = ();

    fn lookup(&mut self, (): &()) -> Result<Lookup<usize>, Infallible> {
        Ok(Lookup::Missing)
    }

    fn enter(&mut self, (): ()) -> Result<(), Infallible> {
        self.starts += 1;
        Ok(())
    }

    fn finish(&mut self, (): (), answer: usize) -> Finished<(), usize> {
        self.completed.push(answer);
        match self.revision {
            Revision::Initial => {
                self.revision = Revision::Refined;
                Finished::Retry(())
            }
            Revision::Refined => Finished::Ready(answer),
        }
    }

    async fn execute(session: Session<'_, Self>, (): ()) -> Result<usize, Infallible> {
        Ok(session.with(|engine| match engine.revision {
            Revision::Initial => 0,
            Revision::Refined => 1,
        }))
    }
}

#[test]
fn an_explicit_refinement_retry_starts_a_new_computation() {
    let mut refinement = Refinement {
        revision: Revision::Initial,
        starts: 0,
        completed: Vec::new(),
    };
    assert_eq!(evaluate(&mut refinement, ()).unwrap(), 1);
    assert_eq!(refinement.starts, 2);
    assert_eq!(refinement.completed, vec![0, 1]);
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Selection {
    Oldest,
    Newest,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Observation {
    Enter,
    Block(Selection),
    Finish,
    Reuse(Selection),
}

#[hegel::test(print_blob = true)]
fn oldest_blockers_agree_with_all_ancestor_dependency_sets(tc: hegel::TestCase) {
    use shapelint_driver::contracts::schedule::{Dependencies, Dependency, QueryId};
    use std::collections::HashSet;

    let observations = tc.draw(hegel::generators::default::<Vec<Observation>>());
    let mut dependencies = Dependencies::default();
    let root = dependencies.enter().unwrap();
    let mut frames = vec![(root, HashSet::<QueryId>::new())];
    let mut cached = Vec::<(Dependency, HashSet<QueryId>)>::new();
    for observation in observations {
        match observation {
            Observation::Enter => {
                frames.push((dependencies.enter().unwrap(), HashSet::new()));
            }
            Observation::Block(selection) => {
                let (id, _) = match selection {
                    Selection::Oldest => frames.first().unwrap(),
                    Selection::Newest => frames.last().unwrap(),
                };
                let id = *id;
                dependencies.observe(Dependency::Blocked(id));
                for (_, observed) in &mut frames {
                    observed.insert(id);
                }
            }
            Observation::Finish => {
                let (_, expected) = frames.pop().unwrap();
                let actual = dependencies.finish();
                let expected_pending = expected
                    .iter()
                    .copied()
                    .filter(|id| frames.iter().any(|(active, _)| active == id))
                    .min();
                assert_eq!(dependencies.pending(actual), expected_pending);
                match (expected.is_empty(), actual) {
                    (true, Dependency::Independent) => {}
                    (false, Dependency::Observed | Dependency::Blocked(_)) => {}
                    _ => panic!("lost dependency observations: {actual:?}, {expected:?}"),
                }
                cached.push((actual, expected));
                if frames.is_empty() {
                    frames.push((dependencies.enter().unwrap(), HashSet::new()));
                }
            }
            Observation::Reuse(selection) => {
                let cached = match selection {
                    Selection::Oldest => cached.first(),
                    Selection::Newest => cached.last(),
                };
                let Some((actual, expected)) = cached else {
                    continue;
                };
                let expected_pending = expected
                    .iter()
                    .copied()
                    .filter(|id| frames.iter().any(|(active, _)| active == id))
                    .min();
                assert_eq!(dependencies.pending(*actual), expected_pending);
                match dependencies.pending(*actual) {
                    Some(_) => {
                        dependencies.observe(*actual);
                        for (_, observed) in &mut frames {
                            observed.extend(expected.iter().copied());
                        }
                    }
                    None => {}
                }
            }
        }
    }
    while let Some((_, expected)) = frames.pop() {
        let actual = dependencies.finish();
        let pending = expected
            .iter()
            .copied()
            .filter(|id| frames.iter().any(|(active, _)| active == id))
            .min();
        assert_eq!(dependencies.pending(actual), pending);
    }
}

#[test]
fn expired_blockers_do_not_bind_to_a_later_activation() {
    use shapelint_driver::contracts::schedule::{Dependencies, Dependency};

    let mut dependencies = Dependencies::default();
    let first = dependencies.enter().unwrap();
    dependencies.enter().unwrap();
    dependencies.observe(Dependency::Blocked(first));
    let cached = dependencies.finish();
    assert_eq!(dependencies.pending(cached), Some(first));
    assert_eq!(dependencies.finish(), Dependency::Observed);
    let next = dependencies.enter().unwrap();
    assert_ne!(first, next);
    assert_eq!(dependencies.pending(cached), None);
    dependencies.observe(cached);
    dependencies.observe(Dependency::Blocked(next));
    assert_eq!(dependencies.finish(), Dependency::Observed);
}

#[test]
fn deep_blocked_queries_transfer_one_observation_per_frame() {
    use shapelint_driver::contracts::schedule::{Dependencies, Dependency};

    let mut dependencies = Dependencies::default();
    let root = dependencies.enter().unwrap();
    let depth = 100_000;
    for _ in 0..depth {
        dependencies.enter().unwrap();
        dependencies.observe(Dependency::Blocked(root));
    }
    for _ in 0..depth {
        let observed = dependencies.finish();
        assert_eq!(observed, Dependency::Blocked(root));
        assert_eq!(dependencies.pending(observed), Some(root));
    }
    assert_eq!(dependencies.finish(), Dependency::Observed);
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum LifecycleOutcome {
    Complete,
    Retry,
    ChildError,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum LifecycleEvent {
    Enter(usize),
    Start(usize),
    Error(usize),
    Drop(usize),
    Finish(usize),
}

struct Lifecycle {
    outcome: LifecycleOutcome,
    answers: [Option<usize>; 4],
    root_finishes: usize,
    events: std::rc::Rc<std::cell::RefCell<Vec<LifecycleEvent>>>,
}

struct TrackedFuture<'a> {
    query: usize,
    events: std::rc::Rc<std::cell::RefCell<Vec<LifecycleEvent>>>,
    inner: std::pin::Pin<Box<dyn std::future::Future<Output = Result<usize, ()>> + 'a>>,
}

impl std::future::Future for TrackedFuture<'_> {
    type Output = Result<usize, ()>;

    fn poll(
        mut self: std::pin::Pin<&mut Self>,
        context: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        self.inner.as_mut().poll(context)
    }
}

impl Drop for TrackedFuture<'_> {
    fn drop(&mut self) {
        self.events
            .borrow_mut()
            .push(LifecycleEvent::Drop(self.query));
    }
}

impl Engine for Lifecycle {
    type Query = usize;
    type Answer = usize;
    type Error = ();
    type Frame = usize;

    fn lookup(&mut self, query: &usize) -> Result<Lookup<usize>, ()> {
        Ok(match self.answers[*query] {
            Some(answer) => Lookup::Ready(answer),
            None => Lookup::Missing,
        })
    }

    fn enter(&mut self, query: usize) -> Result<usize, ()> {
        self.events.borrow_mut().push(LifecycleEvent::Enter(query));
        Ok(query)
    }

    fn finish(&mut self, query: usize, answer: usize) -> Finished<usize, usize> {
        self.events.borrow_mut().push(LifecycleEvent::Finish(query));
        if query == 0 {
            self.root_finishes += 1;
            if let (LifecycleOutcome::Retry, 1) = (self.outcome, self.root_finishes) {
                return Finished::Retry(query);
            }
        }
        self.answers[query] = Some(answer);
        Finished::Ready(answer)
    }

    fn execute(
        session: Session<'_, Self>,
        query: usize,
    ) -> impl std::future::Future<Output = Result<usize, ()>> {
        let events = session.with(|engine| std::rc::Rc::clone(&engine.events));
        let inner = Box::pin(async move {
            session.with(|engine| {
                engine
                    .events
                    .borrow_mut()
                    .push(LifecycleEvent::Start(query))
            });
            match query {
                0 => Ok(session.query(1).await? + session.query(3).await?),
                1 => session.query(2).await,
                2 => match session.with(|engine| engine.outcome) {
                    LifecycleOutcome::ChildError => {
                        session.with(|engine| {
                            engine
                                .events
                                .borrow_mut()
                                .push(LifecycleEvent::Error(query))
                        });
                        Err(())
                    }
                    LifecycleOutcome::Complete | LifecycleOutcome::Retry => Ok(2),
                },
                3 => Ok(3),
                _ => unreachable!("the test graph has four queries"),
            }
        });
        TrackedFuture {
            query,
            events,
            inner,
        }
    }
}

#[hegel::test(print_blob = true)]
fn suspended_queries_drop_before_finish_and_errors_drop_live_futures(tc: hegel::TestCase) {
    let outcome = tc.draw(hegel::generators::default::<LifecycleOutcome>());
    let events = std::rc::Rc::new(std::cell::RefCell::new(Vec::new()));
    let mut engine = Lifecycle {
        outcome,
        answers: [None; 4],
        root_finishes: 0,
        events: std::rc::Rc::clone(&events),
    };
    let result = evaluate(&mut engine, 0);
    let events = events.borrow();
    match outcome {
        LifecycleOutcome::Complete => {
            assert_eq!(result, Ok(5));
            assert_eq!(
                &*events,
                &[
                    LifecycleEvent::Enter(0),
                    LifecycleEvent::Start(0),
                    LifecycleEvent::Enter(1),
                    LifecycleEvent::Start(1),
                    LifecycleEvent::Enter(2),
                    LifecycleEvent::Start(2),
                    LifecycleEvent::Drop(2),
                    LifecycleEvent::Finish(2),
                    LifecycleEvent::Drop(1),
                    LifecycleEvent::Finish(1),
                    LifecycleEvent::Enter(3),
                    LifecycleEvent::Start(3),
                    LifecycleEvent::Drop(3),
                    LifecycleEvent::Finish(3),
                    LifecycleEvent::Drop(0),
                    LifecycleEvent::Finish(0),
                ]
            );
        }
        LifecycleOutcome::Retry => {
            assert_eq!(result, Ok(5));
            assert_eq!(
                &*events,
                &[
                    LifecycleEvent::Enter(0),
                    LifecycleEvent::Start(0),
                    LifecycleEvent::Enter(1),
                    LifecycleEvent::Start(1),
                    LifecycleEvent::Enter(2),
                    LifecycleEvent::Start(2),
                    LifecycleEvent::Drop(2),
                    LifecycleEvent::Finish(2),
                    LifecycleEvent::Drop(1),
                    LifecycleEvent::Finish(1),
                    LifecycleEvent::Enter(3),
                    LifecycleEvent::Start(3),
                    LifecycleEvent::Drop(3),
                    LifecycleEvent::Finish(3),
                    LifecycleEvent::Drop(0),
                    LifecycleEvent::Finish(0),
                    LifecycleEvent::Enter(0),
                    LifecycleEvent::Start(0),
                    LifecycleEvent::Drop(0),
                    LifecycleEvent::Finish(0),
                ]
            );
        }
        LifecycleOutcome::ChildError => {
            assert_eq!(result, Err(()));
            assert_eq!(
                &events[..7],
                &[
                    LifecycleEvent::Enter(0),
                    LifecycleEvent::Start(0),
                    LifecycleEvent::Enter(1),
                    LifecycleEvent::Start(1),
                    LifecycleEvent::Enter(2),
                    LifecycleEvent::Start(2),
                    LifecycleEvent::Error(2),
                ]
            );
            let drops: std::collections::HashSet<_> = events[7..].iter().copied().collect();
            assert_eq!(
                drops,
                std::collections::HashSet::from([
                    LifecycleEvent::Drop(0),
                    LifecycleEvent::Drop(1),
                    LifecycleEvent::Drop(2)
                ])
            );
            assert_eq!(events.len(), 10);
        }
    }
}
