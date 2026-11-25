use std::cell::RefCell;
use std::future::{Future, poll_fn};
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

use rustc_data_structures::fx::FxHashSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QueryId(u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Dependency {
    Independent,
    Observed,
    Blocked(QueryId),
}

impl Dependency {
    fn current(self, active: &FxHashSet<QueryId>) -> Self {
        match self {
            Self::Blocked(id) if !active.contains(&id) => Self::Observed,
            dependency => dependency,
        }
    }
}

/// Retains the oldest live blocker of each depth-first query activation.
///
/// Live blockers are ancestors. Once the oldest finishes, every blocker observed
/// with it has finished too. Expired observations still require convergence;
/// query identities are never reused, including when the same definition recurs.
#[derive(Default)]
pub struct Dependencies {
    stack: Vec<(QueryId, Dependency)>,
    active: FxHashSet<QueryId>,
    next: u64,
}

impl Dependencies {
    pub fn enter(&mut self) -> Option<QueryId> {
        let Ok(index) = u32::try_from(self.next) else {
            return None;
        };
        let id = QueryId(index);
        self.next = u64::from(index) + 1;
        self.stack.push((id, Dependency::Independent));
        self.active.insert(id);
        Some(id)
    }

    pub fn pending(&self, dependency: Dependency) -> Option<QueryId> {
        match dependency.current(&self.active) {
            Dependency::Blocked(id) => Some(id),
            Dependency::Independent | Dependency::Observed => None,
        }
    }

    pub fn observe(&mut self, dependency: Dependency) {
        let Some((_, previous)) = self.stack.last_mut() else {
            return;
        };
        *previous = match (
            previous.current(&self.active),
            dependency.current(&self.active),
        ) {
            (Dependency::Blocked(left), Dependency::Blocked(right)) => {
                Dependency::Blocked(left.min(right))
            }
            (Dependency::Blocked(id), _) | (_, Dependency::Blocked(id)) => Dependency::Blocked(id),
            (Dependency::Independent, Dependency::Independent) => Dependency::Independent,
            _ => Dependency::Observed,
        };
    }

    /// Finishes the most recently entered activation and transfers its observations
    /// to its immediate parent, including observations from a converged retry.
    ///
    /// # Panics
    ///
    /// Panics when there is no unfinished activation.
    pub fn finish(&mut self) -> Dependency {
        let (id, dependency) = self.stack.pop().expect("finished query is active");
        self.active.remove(&id);
        let dependency = dependency.current(&self.active);
        self.observe(dependency);
        dependency
    }
}

pub enum Lookup<A> {
    Ready(A),
    Missing,
}

pub enum Finished<Q, A> {
    Ready(A),
    Retry(Q),
}

/// Supplies memoized queries and explicit fixed-point retries.
///
/// Execution suspends only through [`Session::query`]. Finishing a child publishes
/// its answer for lookup before returning [`Finished::Ready`].
pub trait Engine: Sized {
    type Query: Clone;
    type Answer;
    type Error;
    type Frame;

    fn lookup(&mut self, query: &Self::Query) -> Result<Lookup<Self::Answer>, Self::Error>;
    fn enter(&mut self, query: Self::Query) -> Result<Self::Frame, Self::Error>;
    fn finish(
        &mut self,
        frame: Self::Frame,
        answer: Self::Answer,
    ) -> Finished<Self::Query, Self::Answer>;
    fn execute(
        session: Session<'_, Self>,
        query: Self::Query,
    ) -> impl Future<Output = Result<Self::Answer, Self::Error>>;
}

/// Synchronous access cannot retain an engine borrow across a dependency suspension.
pub struct Session<'a, E: Engine> {
    engine: &'a RefCell<&'a mut E>,
    demand: &'a RefCell<Option<E::Query>>,
}

impl<E: Engine> Copy for Session<'_, E> {}
impl<E: Engine> Clone for Session<'_, E> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<E: Engine> Session<'_, E> {
    pub fn with<R>(&self, operation: impl FnOnce(&mut E) -> R) -> R {
        let mut engine = self.engine.borrow_mut();
        operation(&mut engine)
    }

    pub async fn query(&self, query: E::Query) -> Result<E::Answer, E::Error> {
        poll_fn(|_| match self.with(|engine| engine.lookup(&query)) {
            Ok(Lookup::Ready(answer)) => Poll::Ready(Ok(answer)),
            Ok(Lookup::Missing) => {
                *self.demand.borrow_mut() = Some(query.clone());
                Poll::Pending
            }
            Err(error) => Poll::Ready(Err(error)),
        })
        .await
    }
}

pub fn evaluate<E: Engine>(engine: &mut E, query: E::Query) -> Result<E::Answer, E::Error> {
    fn allocate<F>(spare: &mut Vec<Pin<Box<F>>>, run: F) -> Pin<Box<F>> {
        match spare.pop() {
            Some(mut execution) => {
                execution.as_mut().set(run);
                execution
            }
            None => Box::pin(run),
        }
    }
    if let Lookup::Ready(answer) = engine.lookup(&query)? {
        return Ok(answer);
    }
    let engine = RefCell::new(engine);
    let demand = RefCell::new(None);
    let session = Session {
        engine: &engine,
        demand: &demand,
    };
    enum Work<Q, F, X> {
        Enter(Q),
        Resume(F, X),
    }
    let mut next = Work::Enter(query);
    let mut parents = Vec::new();
    let mut spare = Vec::new();
    let mut context = Context::from_waker(Waker::noop());
    loop {
        let (frame, mut execution) = match next {
            Work::Enter(query) => {
                let frame = session.with(|engine| engine.enter(query.clone()))?;
                // Awaiting by value drops the engine's future as soon as it finishes.
                // Only the completed outer future and its reusable allocation enter spare.
                let run = async move { E::execute(session, query).await };
                (frame, allocate(&mut spare, run))
            }
            Work::Resume(frame, execution) => (frame, execution),
        };
        next = match execution.as_mut().poll(&mut context) {
            Poll::Pending => {
                let dependency = demand
                    .borrow_mut()
                    .take()
                    .expect("pending query requested a dependency");
                parents.push((frame, execution));
                Work::Enter(dependency)
            }
            Poll::Ready(answer) => {
                let answer = answer?;
                spare.push(execution);
                match session.with(|engine| engine.finish(frame, answer)) {
                    Finished::Retry(query) => Work::Enter(query),
                    Finished::Ready(answer) => match parents.pop() {
                        None => return Ok(answer),
                        Some((frame, execution)) => Work::Resume(frame, execution),
                    },
                }
            }
        };
    }
}
