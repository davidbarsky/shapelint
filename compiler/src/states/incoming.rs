use std::hash::Hash;
use std::ops::RangeInclusive;

use crate::contracts::graph::CapacityError;
use crate::persistent::{Map, Maps, Neighbor, Ordered};

/// Retains completed prefixes of an ordered, potentially nonassociative fold.
/// Reused prefixes require the merge operation's meaning to remain unchanged.
pub struct Incoming<'g, T> {
    seed: Option<T>,
    inputs: Map<'g, u128, T, Ordered>,
    prefixes: Map<'g, u128, T, Ordered>,
    dirty: Option<RangeInclusive<u128>>,
    result: Option<T>,
}

impl<'g, T: Clone + Eq + Hash> Incoming<'g, T> {
    pub fn new(seed: Option<T>) -> Self {
        Self {
            result: seed.clone(),
            seed,
            inputs: Map::EMPTY,
            prefixes: Map::EMPTY,
            dirty: None,
        }
    }

    pub fn replace(
        &mut self,
        maps: &mut Maps<'g, u128, T, Ordered>,
        position: usize,
        input: Option<T>,
    ) -> Result<(), CapacityError> {
        let position = position as u128;
        if maps.get(self.inputs, &position) == input.as_ref() {
            return Ok(());
        }
        let mut inputs = self.inputs;
        let mut prefixes = self.prefixes;
        match input {
            Some(input) => {
                maps.insert(&mut inputs, position, input)?;
            }
            None => {
                maps.remove(&mut inputs, &position)?;
                maps.remove(&mut prefixes, &position)?;
            }
        }
        self.inputs = inputs;
        self.prefixes = prefixes;
        self.dirty = Some(match self.dirty.take() {
            Some(dirty) => position.min(*dirty.start())..=position.max(*dirty.end()),
            None => position..=position,
        });
        Ok(())
    }

    /// A failed merge retains the completed prefix for a later retry.
    pub fn fold<E: From<CapacityError>>(
        &mut self,
        maps: &mut Maps<'g, u128, T, Ordered>,
        mut merge: impl FnMut(&mut T, &T) -> Result<(), E>,
    ) -> Result<Option<T>, E> {
        if let Some(dirty) = self.dirty.clone() {
            let mut current = maps
                .neighbor(self.prefixes, *dirty.start(), Neighbor::Before)
                .map(|(_, prefix)| prefix.clone())
                .or_else(|| self.seed.clone());
            let mut next = maps
                .get(self.inputs, dirty.start())
                .map(|input| (*dirty.start(), input.clone()))
                .or_else(|| {
                    maps.neighbor(self.inputs, *dirty.start(), Neighbor::After)
                        .map(|(position, input)| (*position, input.clone()))
                });
            while let Some((position, input)) = next {
                self.dirty = Some(position..=position.max(*dirty.end()));
                let prefix = match &mut current {
                    Some(prefix) => {
                        merge(prefix, &input)?;
                        prefix
                    }
                    None => current.insert(input),
                };
                if position >= *dirty.end() && maps.get(self.prefixes, &position) == Some(prefix) {
                    self.dirty = None;
                    return Ok(self.result.clone());
                }
                maps.insert(&mut self.prefixes, position, prefix.clone())?;
                next = maps
                    .neighbor(self.inputs, position, Neighbor::After)
                    .map(|(position, input)| (*position, input.clone()));
                self.dirty = next
                    .as_ref()
                    .map(|(position, _)| *position..=(*position).max(*dirty.end()));
            }
            self.result = current;
            self.dirty = None;
        }
        Ok(self.result.clone())
    }
}
