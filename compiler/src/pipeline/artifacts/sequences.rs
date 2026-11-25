use std::hash::Hash;
use std::marker::PhantomData;

use serde::{Deserialize, Serialize};

use crate::artifacts::Error;
use crate::sequence::{Fold, Part, Sequence, Sequences};

#[derive(Serialize, Deserialize)]
#[serde(transparent, bound = "")]
pub(crate) struct Id<T> {
    index: u32,
    #[serde(skip)]
    marker: PhantomData<fn(T) -> T>,
}
impl<T> Copy for Id<T> {}
impl<T> Clone for Id<T> {
    fn clone(&self) -> Self {
        *self
    }
}

#[derive(Serialize, Deserialize)]
#[serde(transparent, bound = "")]
pub(crate) struct Root<T>(Option<Id<T>>);

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) enum Node<T> {
    Leaf(T),
    Branch(Id<T>, Id<T>),
}

pub(crate) struct Encoder<'g, T, U> {
    pub nodes: Vec<Node<U>>,
    mapped: Fold<'g, T, Id<U>>,
}
impl<T, U> Default for Encoder<'_, T, U> {
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            mapped: Fold::default(),
        }
    }
}
impl<'g, T: Clone + Eq + Hash, U> Encoder<'g, T, U> {
    pub fn root(
        &mut self,
        arena: &Sequences<'g, T>,
        sequence: Sequence<'g, T>,
        mut value: impl FnMut(&T) -> Result<U, Error>,
    ) -> Result<Root<U>, Error> {
        let nodes = &mut self.nodes;
        let mut arena = arena;
        let root = self.mapped.fold(
            &mut arena,
            |arena| *arena,
            sequence,
            |_, part| {
                let node = match part {
                    Part::Leaf(input) => Node::Leaf(value(input)?),
                    Part::Branch(left, right) => Node::Branch(*left, *right),
                };
                let id = Id {
                    index: u32::try_from(nodes.len())
                        .map_err(|_| crate::contracts::graph::CapacityError::Sequences)?,
                    marker: PhantomData,
                };
                nodes.push(node);
                Ok::<_, Error>(id)
            },
        )?;
        Ok(Root(root))
    }
}

pub(crate) struct Decoder<'g, U, T> {
    nodes: Vec<Sequence<'g, T>>,
    marker: PhantomData<fn(U) -> U>,
}
impl<U, T> Default for Decoder<'_, U, T> {
    fn default() -> Self {
        Self {
            nodes: Vec::new(),
            marker: PhantomData,
        }
    }
}
impl<'g, U, T: Clone + Eq + Hash> Decoder<'g, U, T> {
    pub fn decode(
        nodes: Vec<Node<U>>,
        arena: &mut Sequences<'g, T>,
        mut value: impl FnMut(U) -> Result<T, Error>,
    ) -> Result<Self, Error> {
        let mut decoded = Self {
            nodes: Vec::new(),
            marker: PhantomData,
        };
        for node in nodes {
            let sequence = match node {
                Node::Leaf(input) => arena.from_iter([value(input)?])?,
                Node::Branch(left, right) => {
                    let child = |id: Id<U>| {
                        decoded
                            .nodes
                            .get(id.index as usize)
                            .copied()
                            .ok_or_else(|| {
                                Error::Incompatible(format!(
                                    "sequence child {} must precede its parent {}",
                                    id.index,
                                    decoded.nodes.len()
                                ))
                            })
                    };
                    arena.append(child(left)?, child(right)?)?
                }
            };
            decoded.nodes.push(sequence);
        }
        Ok(decoded)
    }
    pub fn root(
        &self,
        empty: Sequence<'g, T>,
        Root(root): Root<U>,
    ) -> Result<Sequence<'g, T>, Error> {
        match root {
            None => Ok(empty),
            Some(id) => self.nodes.get(id.index as usize).copied().ok_or_else(|| {
                Error::Incompatible(format!(
                    "sequence root {} is outside its table of {} nodes",
                    id.index,
                    self.nodes.len()
                ))
            }),
        }
    }
}
