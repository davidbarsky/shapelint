use std::cell::RefCell;
use std::hash::Hash;

use rustc_abi::FieldIdx;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_index::IndexVec;
use rustc_middle::mir::{Body, Local, Place, PlaceElem, PlaceTy, ProjectionElem};
use rustc_middle::ty::{self, TyCtxt};

use crate::contracts::graph::CapacityError;
use crate::persistent::{Differences, Map, Maps, Set, Sets};
use crate::states::{Fact, Value, ValueKind};

pub(crate) enum Dependency<'tcx> {
    None,
    Place(Place<'tcx>),
    EveryWrite,
    Reference,
}

pub(crate) trait Stored<'tcx>: Copy + Eq + Hash + Sized {
    fn dependency(&self) -> Dependency<'tcx>;
}

impl<'tcx> Stored<'tcx> for Value<'tcx> {
    fn dependency(&self) -> Dependency<'tcx> {
        match self {
            Self::Direct(
                ValueKind::Origin(place)
                | ValueKind::Discriminant(place)
                | ValueKind::Predicate { place, .. },
            ) => Dependency::Place(*place),
            Self::Negated(_) => Dependency::EveryWrite,
            Self::Direct(ValueKind::Known(_)) => Dependency::None,
            Self::Direct(ValueKind::Reference(_)) => Dependency::Reference,
        }
    }
}
impl<'tcx> Stored<'tcx> for Fact {
    fn dependency(&self) -> Dependency<'tcx> {
        Dependency::None
    }
}
impl<'tcx> Stored<'tcx> for () {
    fn dependency(&self) -> Dependency<'tcx> {
        Dependency::None
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Tracked<'tcx, 's, V> {
    pub(in crate::states) values: Map<'s, Place<'tcx>, V>,
    keys: Places<'tcx, 's>,
    dependencies: Places<'tcx, 's>,
    every_write: Set<'s, Place<'tcx>>,
    references: Map<'s, Place<'tcx>, V>,
    reference_keys: Places<'tcx, 's>,
}
impl<V> Default for Tracked<'_, '_, V> {
    fn default() -> Self {
        Self {
            values: Map::EMPTY,
            keys: Places::default(),
            dependencies: Places::default(),
            every_write: Set::EMPTY,
            references: Map::EMPTY,
            reference_keys: Places::default(),
        }
    }
}
impl<V> PartialEq for Tracked<'_, '_, V> {
    fn eq(&self, other: &Self) -> bool {
        self.values == other.values
    }
}
impl<V> Eq for Tracked<'_, '_, V> {}
impl<V> Hash for Tracked<'_, '_, V> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.values.hash(state);
    }
}
pub(crate) trait Table<'tcx, 's, V> {
    fn table(&self) -> &Maps<'s, Place<'tcx>, V>;
    fn table_mut(&mut self) -> &mut Maps<'s, Place<'tcx>, V>;
}

macro_rules! place_table {
    ($value:ty, $field:ident) => {
        impl<'tcx, 's> Table<'tcx, 's, $value> for Paths<'tcx, 's> {
            fn table(&self) -> &Maps<'s, Place<'tcx>, $value> {
                &self.$field
            }

            fn table_mut(&mut self) -> &mut Maps<'s, Place<'tcx>, $value> {
                &mut self.$field
            }
        }
    };
}

place_table!(Value<'tcx>, values);
place_table!(Fact, facts);
place_table!((), key_sets);

impl<'tcx, 's, V: Stored<'tcx>> Tracked<'tcx, 's, V>
where
    Paths<'tcx, 's>: Table<'tcx, 's, V>,
{
    pub(crate) fn descendants<'a>(
        &self,
        place: Place<'tcx>,
        paths: &'a Paths<'tcx, 's>,
    ) -> impl Iterator<Item = (Place<'tcx>, V)> + 'a
    where
        'tcx: 'a,
        's: 'a,
        V: 'a,
    {
        let keys = paths.overlapping(&self.keys, place, Overlap::Descendants);
        let table = paths.table();
        let values = self.values;
        keys.into_iter().map(move |place| {
            let value = *table
                .get(values, &place)
                .expect("indexed place has a value");
            (place, value)
        })
    }

    pub(crate) fn insert(
        &mut self,
        place: Place<'tcx>,
        value: V,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<(), CapacityError> {
        self.record(place, &value, paths)?;
        paths.table_mut().insert(&mut self.values, place, value)?;
        Ok(())
    }
    fn record(
        &mut self,
        place: Place<'tcx>,
        value: &V,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<(), CapacityError> {
        paths.insert(&mut self.keys, place, place)?;
        paths.remove(&mut self.dependencies, &place)?;
        Table::<()>::table_mut(paths).remove(&mut self.every_write, &place)?;
        paths.table_mut().remove(&mut self.references, &place)?;
        paths.remove(&mut self.reference_keys, &place)?;
        match value.dependency() {
            Dependency::Place(dependency) => {
                paths.insert(&mut self.dependencies, place, dependency)?
            }
            Dependency::EveryWrite => {
                Table::<()>::table_mut(paths).insert(&mut self.every_write, place, ())?;
            }
            Dependency::Reference => {
                paths
                    .table_mut()
                    .insert(&mut self.references, place, *value)?;
                paths.insert(&mut self.reference_keys, place, place)?;
            }
            Dependency::None => {}
        }
        Ok(())
    }
    pub(crate) fn remove(
        &mut self,
        place: &Place<'tcx>,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<(), CapacityError> {
        paths.table_mut().remove(&mut self.values, place)?;
        paths.remove(&mut self.keys, place)?;
        paths.remove(&mut self.dependencies, place)?;
        Table::<()>::table_mut(paths).remove(&mut self.every_write, place)?;
        paths.table_mut().remove(&mut self.references, place)?;
        paths.remove(&mut self.reference_keys, place)?;
        Ok(())
    }
    pub(crate) fn forget(
        &mut self,
        place: Place<'tcx>,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<(), CapacityError> {
        let keys = paths.overlapping(&self.keys, place, Overlap::Prefixes);
        let dependencies = paths.overlapping(&self.dependencies, place, Overlap::Prefixes);
        let every_write = Table::<()>::table(paths)
            .iter(self.every_write)
            .map(|(key, _)| *key)
            .collect::<Vec<_>>();
        let forgotten = keys.into_iter().chain(dependencies).chain(every_write);
        for key in forgotten {
            self.remove(&key, paths)?;
        }
        Ok(())
    }
    pub(crate) fn remove_prefix(
        &mut self,
        place: Place<'tcx>,
        overlap: Overlap,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<(), CapacityError> {
        for key in paths.overlapping(&self.keys, place, overlap) {
            self.remove(&key, paths)?;
        }
        Ok(())
    }
    pub(crate) fn conflicts(
        &mut self,
        place: Place<'tcx>,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<(), CapacityError> {
        for key in paths.candidates(&self.keys, place, tcx, body) {
            if rustc_borrowck::consumers::places_conflict(
                tcx,
                body,
                place,
                key,
                rustc_borrowck::consumers::PlaceConflictBias::Overlap,
            ) {
                self.remove(&key, paths)?;
            }
        }
        Ok(())
    }
    pub(crate) fn intersection(
        &mut self,
        other: &Self,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<(), CapacityError> {
        let removed: Vec<_> = Differences::from((paths.table(), self.values, other.values))
            .filter_map(|(key, difference)| match difference {
                crate::persistent::Difference::Left(_)
                | crate::persistent::Difference::Both(..) => Some(*key),
                crate::persistent::Difference::Right(_) => None,
            })
            .collect();
        for key in removed {
            self.remove(&key, paths)?;
        }
        Ok(())
    }
    pub(crate) fn union(
        &mut self,
        other: &Self,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<(), CapacityError> {
        let added: Vec<_> = Differences::from((paths.table(), self.values, other.values))
            .filter_map(|(key, difference)| match difference {
                crate::persistent::Difference::Right(value) => Some((*key, *value)),
                crate::persistent::Difference::Left(_)
                | crate::persistent::Difference::Both(..) => None,
            })
            .collect();
        for (key, value) in added {
            self.insert(key, value, paths)?;
        }
        Ok(())
    }
    pub(crate) fn references(
        &self,
        destination: Place<'tcx>,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<Self, CapacityError> {
        let mut references = Self {
            values: self.references,
            keys: self.reference_keys,
            dependencies: Places::default(),
            every_write: Set::EMPTY,
            references: self.references,
            reference_keys: self.reference_keys,
        };
        references.remove_prefix(destination, Overlap::Prefixes, paths)?;
        Ok(references)
    }
    pub(crate) fn restore_references(
        &mut self,
        saved: &Self,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<(), CapacityError> {
        let replacements: Vec<_> =
            Differences::from((paths.table(), self.references, saved.references))
                .filter_map(|(key, difference)| match difference {
                    crate::persistent::Difference::Right(value)
                    | crate::persistent::Difference::Both(_, value) => Some((*key, *value)),
                    crate::persistent::Difference::Left(_) => None,
                })
                .collect();
        for (key, value) in replacements {
            self.record(key, &value, paths)?;
            paths.table_mut().insert(&mut self.values, key, value)?;
        }
        Ok(())
    }
}

impl<'tcx, 's> Tracked<'tcx, 's, ()> {
    pub(in crate::states) fn conflicting_writes(
        &self,
        read: Place<'tcx>,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        paths: &mut Paths<'tcx, 's>,
    ) -> impl Iterator<Item = Place<'tcx>> {
        let candidates = paths.candidates(&self.keys, read, tcx, body);
        candidates.into_iter().filter(move |&written| {
            rustc_borrowck::consumers::places_conflict(
                tcx,
                body,
                written,
                read,
                rustc_borrowck::consumers::PlaceConflictBias::Overlap,
            )
        })
    }

    pub(in crate::states) fn empty_drop(
        &self,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        place: Place<'tcx>,
        paths: &Paths<'tcx, 's>,
        memo: &mut FxHashMap<ty::Ty<'tcx>, Option<()>>,
    ) -> Option<()> {
        if let Some(_) = paths.ancestors(&self.keys, place).first() {
            return Some(());
        }
        let ty = place.ty(&body.local_decls, tcx).ty;
        if !ty.needs_drop(tcx, body.typing_env(tcx)) {
            return Some(());
        }
        // A fully droppable, destructor-free aggregate can be preserved as a
        // whole.  A type containing a destructor is only inconclusive here:
        // moved fields may still make its drop glue safe, so keep the
        // field-by-field moved-place walk below for that case.
        if let Some(()) = droppable_type(tcx, body, ty, memo) {
            return Some(());
        }
        let fields: Vec<_> = match ty.kind() {
            ty::Tuple(fields) => fields.iter().collect(),
            ty::Adt(adt, args) if adt.is_struct() && !adt.has_dtor(tcx) => adt
                .non_enum_variant()
                .fields
                .iter()
                .map(|field| field.ty(tcx, args).skip_normalization())
                .collect(),
            _ => return None,
        };
        let fields = fields.into_iter().enumerate();
        for (index, ty) in fields {
            self.empty_drop(
                tcx,
                body,
                place.project_deeper(
                    &[ProjectionElem::Field(FieldIdx::from_usize(index), ty)],
                    tcx,
                ),
                paths,
                memo,
            )?;
        }
        Some(())
    }
}

fn droppable_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    ty: ty::Ty<'tcx>,
    memo: &mut FxHashMap<ty::Ty<'tcx>, Option<()>>,
) -> Option<()> {
    if let Some(result) = memo.get(&ty) {
        return *result;
    }
    if !ty.needs_drop(tcx, body.typing_env(tcx)) {
        memo.insert(ty, Some(()));
        return Some(());
    }
    let result = match ty.kind() {
        ty::Tuple(fields) => fields
            .iter()
            .map(|field| droppable_type(tcx, body, field, memo))
            .collect(),
        ty::Adt(adt, args) if adt.is_struct() && !adt.has_dtor(tcx) => adt
            .non_enum_variant()
            .fields
            .iter()
            .map(|field| droppable_type(tcx, body, field.ty(tcx, args).skip_normalization(), memo))
            .collect(),
        _ => None,
    };
    memo.insert(ty, result);
    result
}

rustc_index::newtype_index! {
    #[max = 0xffff_ffff]
    struct PathId {}
}

struct Path<'tcx> {
    parent: Option<(PathId, PlaceElem<'tcx>)>,
    local: Local,
}

pub(crate) struct Paths<'tcx, 's> {
    values: Maps<'s, Place<'tcx>, Value<'tcx>>,
    facts: Maps<'s, Place<'tcx>, Fact>,
    aliases: RefCell<FxHashMap<(Map<'s, Place<'tcx>, Value<'tcx>>, Place<'tcx>), Place<'tcx>>>,
    nodes: IndexVec<PathId, Path<'tcx>>,
    roots: FxHashMap<Local, PathId>,
    children: FxHashMap<(PathId, PlaceElem<'tcx>), PathId>,
    place_roots: Maps<'s, Local, PathId>,
    place_nodes: Maps<'s, PathId, Branch<'tcx, 's>>,
    place_keys: Maps<'s, Place<'tcx>, PathId>,
    place_children: Maps<'s, PlaceElem<'tcx>, PathId>,
    place_fields: Maps<'s, FieldIdx, Set<'s, PathId>>,
    path_sets: Sets<'s, PathId>,
    key_sets: Sets<'s, Place<'tcx>>,
    pub(in crate::states) prefix_type_steps: usize,
}

impl<'tcx, 's> Default for Paths<'tcx, 's> {
    fn default() -> Self {
        Self {
            values: Maps::new(),
            facts: Maps::new(),
            aliases: RefCell::default(),
            nodes: IndexVec::new(),
            roots: FxHashMap::default(),
            children: FxHashMap::default(),
            place_roots: Maps::new(),
            place_nodes: Maps::new(),
            place_keys: Maps::new(),
            place_children: Maps::new(),
            place_fields: Maps::new(),
            path_sets: Maps::new(),
            key_sets: Maps::new(),
            prefix_type_steps: 0,
        }
    }
}

impl<'tcx, 's> Paths<'tcx, 's> {
    pub(in crate::states) fn resolve(
        &self,
        values: &Tracked<'tcx, 's, Value<'tcx>>,
        tcx: TyCtxt<'tcx>,
        mut place: Place<'tcx>,
    ) -> Place<'tcx> {
        let value_map = values.values;
        if let Some(resolved) = self.aliases.borrow().get(&(value_map, place)).copied() {
            return resolved;
        }
        let original = place;
        let mut visited = FxHashSet::default();
        while visited.insert(place) {
            let next = place
                .projection
                .iter()
                .enumerate()
                .find_map(|(index, projection)| {
                    if projection != ProjectionElem::Deref {
                        return None;
                    }
                    let base = Place {
                        local: place.local,
                        projection: tcx.mk_place_elems(&place.projection[..index]),
                    };
                    match self.values.get(value_map, &base) {
                        Some(Value::Direct(ValueKind::Reference(target))) => {
                            Some(target.project_deeper(&place.projection[index + 1..], tcx))
                        }
                        _ => None,
                    }
                });
            match next {
                Some(next) => place = next,
                None => break,
            }
        }
        self.aliases
            .borrow_mut()
            .insert((value_map, original), place);
        place
    }

    pub(in crate::states) fn value(
        &self,
        tracked: &Tracked<'tcx, 's, Value<'tcx>>,
        place: Place<'tcx>,
    ) -> Value<'tcx> {
        match self.values.get(tracked.values, &place) {
            Some(value) => *value,
            None => Value::Direct(ValueKind::Origin(place)),
        }
    }

    fn intern(&mut self, place: Place<'tcx>) -> Result<PathId, CapacityError> {
        let mut path = match self.roots.get(&place.local) {
            Some(path) => *path,
            None => {
                u32::try_from(self.nodes.len()).map_err(|_| CapacityError::Sets)?;
                let path = self.nodes.push(Path {
                    parent: None,
                    local: place.local,
                });
                self.roots.insert(place.local, path);
                path
            }
        };
        for projection in place.projection.iter() {
            path = match self.children.get(&(path, projection)) {
                Some(path) => *path,
                None => {
                    u32::try_from(self.nodes.len()).map_err(|_| CapacityError::Sets)?;
                    let child = self.nodes.push(Path {
                        parent: Some((path, projection)),
                        local: place.local,
                    });
                    self.children.insert((path, projection), child);
                    child
                }
            };
        }
        Ok(path)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Branch<'tcx, 's> {
    children: Map<'s, PlaceElem<'tcx>, PathId>,
    fields: Map<'s, FieldIdx, Set<'s, PathId>>,
    other: Set<'s, PathId>,
    values: Set<'s, Place<'tcx>>,
}

/// Indexes direct place dependencies. Shared snapshots retain only active
/// prefixes; canonical paths in [`Paths`] do not retain historical users.
pub(crate) struct Places<'tcx, 's> {
    roots: Map<'s, Local, PathId>,
    nodes: Map<'s, PathId, Branch<'tcx, 's>>,
    keys: Map<'s, Place<'tcx>, PathId>,
}

impl Default for Places<'_, '_> {
    fn default() -> Self {
        Self {
            roots: Map::EMPTY,
            nodes: Map::EMPTY,
            keys: Map::EMPTY,
        }
    }
}
impl Copy for Places<'_, '_> {}
impl Clone for Places<'_, '_> {
    fn clone(&self) -> Self {
        Self {
            roots: self.roots.clone(),
            nodes: self.nodes.clone(),
            keys: self.keys.clone(),
        }
    }
}

pub(crate) enum Overlap {
    Prefixes,
    Descendants,
}

impl<'tcx, 's> Paths<'tcx, 's> {
    pub(crate) fn ancestors(
        &self,
        places: &Places<'tcx, 's>,
        place: Place<'tcx>,
    ) -> Vec<Place<'tcx>> {
        let Some(mut path) = self.place_roots.get(places.roots, &place.local).copied() else {
            return Vec::new();
        };
        let mut result = Vec::new();
        let branch = self
            .place_nodes
            .get(places.nodes, &path)
            .expect("active path has a branch");
        result.extend(self.key_sets.iter(branch.values).map(|(key, ())| *key));
        for projection in place.projection.iter() {
            let branch = self
                .place_nodes
                .get(places.nodes, &path)
                .expect("active path has a branch");
            let Some(next) = self.place_children.get(branch.children, &projection) else {
                break;
            };
            path = *next;
            let branch = self
                .place_nodes
                .get(places.nodes, &path)
                .expect("active path has a branch");
            result.extend(self.key_sets.iter(branch.values).map(|(key, ())| *key));
        }
        result
    }

    pub(crate) fn insert(
        &mut self,
        places: &mut Places<'tcx, 's>,
        key: Place<'tcx>,
        place: Place<'tcx>,
    ) -> Result<(), CapacityError> {
        let mut next = *places;
        self.insert_inner(&mut next, key, place)?;
        *places = next;
        Ok(())
    }

    fn insert_inner(
        &mut self,
        places: &mut Places<'tcx, 's>,
        key: Place<'tcx>,
        place: Place<'tcx>,
    ) -> Result<(), CapacityError> {
        let path = self.intern(place)?;
        if self.place_keys.get(places.keys, &key) == Some(&path) {
            return Ok(());
        }
        self.remove_inner(places, &key)?;
        let mut current = path;
        let mut child = None;
        loop {
            let (mut branch, parent) = match self.place_nodes.get(places.nodes, &current) {
                Some(&branch) => (branch, None),
                None => {
                    let branch = Branch {
                        children: Map::EMPTY,
                        fields: Map::EMPTY,
                        other: Set::EMPTY,
                        values: Set::EMPTY,
                    };
                    let parent = self.nodes[current].parent;
                    match parent {
                        Some(parent) => (branch, Some(parent)),
                        None => {
                            self.place_roots
                                .insert(&mut places.roots, place.local, current)?;
                            (branch, None)
                        }
                    }
                }
            };
            match child {
                None => {
                    self.key_sets.insert(&mut branch.values, key, ())?;
                }
                Some((projection, child)) => {
                    self.place_children
                        .insert(&mut branch.children, projection, child)?;
                    match projection {
                        ProjectionElem::Field(field, _) => {
                            let mut children = self
                                .place_fields
                                .get(branch.fields, &field)
                                .copied()
                                .unwrap_or(Set::EMPTY);
                            self.path_sets.insert(&mut children, child, ())?;
                            self.place_fields
                                .insert(&mut branch.fields, field, children)?;
                        }
                        _ => {
                            self.path_sets.insert(&mut branch.other, child, ())?;
                        }
                    }
                }
            }
            self.place_nodes
                .insert(&mut places.nodes, current, branch)?;
            let Some((parent, projection)) = parent else {
                break;
            };
            child = Some((projection, current));
            current = parent;
        }
        self.place_keys.insert(&mut places.keys, key, path)?;
        Ok(())
    }

    pub(crate) fn remove(
        &mut self,
        places: &mut Places<'tcx, 's>,
        key: &Place<'tcx>,
    ) -> Result<(), CapacityError> {
        let mut next = *places;
        self.remove_inner(&mut next, key)?;
        *places = next;
        Ok(())
    }

    fn remove_inner(
        &mut self,
        places: &mut Places<'tcx, 's>,
        key: &Place<'tcx>,
    ) -> Result<(), CapacityError> {
        let Some(mut current) = self.place_keys.remove(&mut places.keys, key)? else {
            return Ok(());
        };
        let mut branch = *self
            .place_nodes
            .get(places.nodes, &current)
            .expect("path branch exists");
        self.key_sets.remove(&mut branch.values, key)?;
        loop {
            if self.key_sets.len(branch.values) != 0
                || self.place_children.len(branch.children) != 0
            {
                self.place_nodes
                    .insert(&mut places.nodes, current, branch)?;
                break;
            }
            self.place_nodes.remove(&mut places.nodes, &current)?;
            match self.nodes[current].parent {
                Some((parent, projection)) => {
                    branch = *self
                        .place_nodes
                        .get(places.nodes, &parent)
                        .expect("parent branch exists");
                    self.place_children
                        .remove(&mut branch.children, &projection)?;
                    match projection {
                        ProjectionElem::Field(field, _) => {
                            let mut children = *self
                                .place_fields
                                .get(branch.fields, &field)
                                .expect("field children exist");
                            self.path_sets.remove(&mut children, &current)?;
                            if self.path_sets.len(children) == 0 {
                                self.place_fields.remove(&mut branch.fields, &field)?;
                            } else {
                                self.place_fields
                                    .insert(&mut branch.fields, field, children)?;
                            }
                        }
                        _ => {
                            self.path_sets.remove(&mut branch.other, &current)?;
                        }
                    }
                    current = parent;
                }
                None => {
                    self.place_roots
                        .remove(&mut places.roots, &self.nodes[current].local)?;
                    break;
                }
            }
        }
        Ok(())
    }

    pub(crate) fn overlapping(
        &self,
        places: &Places<'tcx, 's>,
        place: Place<'tcx>,
        overlap: Overlap,
    ) -> Vec<Place<'tcx>> {
        let Some(mut path) = self.place_roots.get(places.roots, &place.local).copied() else {
            return Vec::new();
        };
        let mut result = Vec::new();
        for projection in place.projection.iter() {
            let branch = self
                .place_nodes
                .get(places.nodes, &path)
                .expect("path branch exists");
            if let Overlap::Prefixes = overlap {
                result.extend(self.key_sets.iter(branch.values).map(|(key, ())| *key));
            }
            let Some(next) = self.place_children.get(branch.children, &projection) else {
                return result;
            };
            path = *next;
        }
        let mut pending = vec![path];
        while let Some(path) = pending.pop() {
            let branch = self
                .place_nodes
                .get(places.nodes, &path)
                .expect("path branch exists");
            result.extend(self.key_sets.iter(branch.values).map(|(key, ())| *key));
            pending.extend(
                self.place_children
                    .iter(branch.children)
                    .map(|(_, path)| *path),
            );
        }
        result
    }

    pub(crate) fn candidates(
        &mut self,
        places: &Places<'tcx, 's>,
        place: Place<'tcx>,
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
    ) -> Vec<Place<'tcx>> {
        let Some(root) = self.place_roots.get(places.roots, &place.local) else {
            return Vec::new();
        };
        let mut result = Vec::new();
        // Compute each prefix once. Trie branches can revisit a depth, but
        // their union check only needs the already-projected `PlaceTy`.
        let mut prefix_types = Vec::with_capacity(place.projection.len() + 1);
        let mut prefix_ty = PlaceTy::from_ty(body.local_decls[place.local].ty);
        prefix_types.push(prefix_ty);
        self.prefix_type_steps = self
            .prefix_type_steps
            .saturating_add(place.projection.len());
        for projection in place.projection.iter() {
            prefix_ty = prefix_ty.projection_ty(tcx, projection);
            prefix_types.push(prefix_ty);
        }
        let mut pending = vec![(*root, 0)];
        while let Some((path, depth)) = pending.pop() {
            let branch = self
                .place_nodes
                .get(places.nodes, &path)
                .expect("path branch exists");
            result.extend(self.key_sets.iter(branch.values).map(|(key, ())| *key));
            match place.projection.get(depth) {
                Some(ProjectionElem::Field(field, _)) => {
                    if let rustc_middle::ty::Adt(adt, _) = prefix_types[depth].ty.kind()
                        && adt.is_union()
                    {
                        pending.extend(
                            self.place_children
                                .iter(branch.children)
                                .map(|(_, child)| (*child, depth + 1)),
                        );
                        continue;
                    }
                    if let Some(children) = self.place_fields.get(branch.fields, field) {
                        pending.extend(
                            self.path_sets
                                .iter(*children)
                                .map(|(child, ())| (*child, depth + 1)),
                        );
                    }
                    pending.extend(
                        self.path_sets
                            .iter(branch.other)
                            .map(|(child, ())| (*child, depth + 1)),
                    );
                }
                _ => pending.extend(
                    self.place_children
                        .iter(branch.children)
                        .map(|(_, child)| (*child, depth + 1)),
                ),
            }
        }
        result
    }
}
