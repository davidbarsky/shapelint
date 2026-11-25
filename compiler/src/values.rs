//! Canonical semantic values owned by one analysis graph.

use parking_lot::Mutex;
use std::hash::Hash;
use std::marker::PhantomData;
use std::sync::Arc;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::{Mutability, def_id::DefId};
use rustc_middle::ty::consts::ConstExt;
use rustc_middle::{mir::Local, ty};

use crate::arena::CapacityError;
use crate::arena::{ArenaId, Intern};
use crate::calls::{self, Generic, Type};
use crate::sequence::{Sequence, Sequences};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Origin {
    pub def: DefId,
    pub name: Option<String>,
    pub adt: Option<DefId>,
    pub identity: Option<Identity>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Identity {
    pub origin: (DefId, Local),
    pub fields: Vec<usize>,
    /// Outermost invocation first; it determines when the identity is retired.
    pub calls: Vec<(DefId, Local)>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Invocation<'g> {
    pub relocation: Relocation<'g>,
    pub generics: GenericsId<'g>,
}

impl<'g> Invocation<'g> {
    pub const LOCAL: Self = Self {
        relocation: Relocation::Preserve,
        generics: GenericsId::EMPTY,
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Relocation<'g> {
    Preserve,
    Into(Option<IdentityId<'g>>),
}

macro_rules! id {
    ($($name:ident),* $(,)?) => {$ (
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name<'g>(u32, PhantomData<fn(&'g ()) -> &'g ()>);
        impl ArenaId for $name<'_> {
            fn from_index(index: u32) -> Self { Self(index, PhantomData) }
            fn index(self) -> u32 { self.0 }
        }
    )*};
}
id!(TextId, TypeId, GenericId, InstanceId, OriginId, IdentityId);

macro_rules! list_id {
    ($name:ident, $element:ty) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
        pub struct $name<'g>(Sequence<'g, $element>);
    };
}
list_id!(TypesId, TypeId<'g>);
list_id!(GenericsId, GenericId<'g>);
list_id!(FieldsId, usize);
list_id!(CallsId, (DefId, Local));

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum TypeNode<'g> {
    Unknown,
    Parameter(u32),
    Bool,
    Char,
    Int(ty::IntTy),
    Uint(ty::UintTy),
    Float(ty::FloatTy),
    Str,
    Never,
    Slice(TypeId<'g>),
    Array(TypeId<'g>, GenericId<'g>),
    Tuple(TypesId<'g>),
    Ref(Mutability, TypeId<'g>),
    RawPtr(Mutability, TypeId<'g>),
    Adt(DefId, GenericsId<'g>),
    Function(DefId, GenericsId<'g>),
    Closure(DefId, GenericsId<'g>),
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum GenericNode<'g> {
    Lifetime,
    Type(TypeId<'g>),
    Const { value: u128, ty: TypeId<'g> },
    Parameter(u32),
    Unknown,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Dispatch {
    Item,
    Virtual,
    Shim,
    Unresolved,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InstanceNode<'g> {
    pub def: DefId,
    pub args: GenericsId<'g>,
    pub dispatch: Dispatch,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct OriginNode<'g> {
    pub def: DefId,
    pub name: Option<TextId<'g>>,
    pub adt: Option<DefId>,
    pub identity: Option<IdentityId<'g>>,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IdentityNode<'g> {
    pub origin: (DefId, Local),
    pub fields: FieldsId<'g>,
    pub calls: CallsId<'g>,
}

pub struct Values<'g> {
    texts: Intern<TextId<'g>, String>,
    types: Intern<TypeId<'g>, TypeNode<'g>>,
    generics: Intern<GenericId<'g>, GenericNode<'g>>,
    instances: Intern<InstanceId<'g>, InstanceNode<'g>>,
    origins: Intern<OriginId<'g>, OriginNode<'g>>,
    identities: Intern<IdentityId<'g>, IdentityNode<'g>>,
    type_lists: Sequences<'g, TypeId<'g>>,
    generic_lists: Sequences<'g, GenericId<'g>>,
    field_lists: Sequences<'g, usize>,
    call_lists: Sequences<'g, (DefId, Local)>,
    /// Structural import keys own their token snapshots, so unlike the
    /// per-import pointer maps they remain valid when the caller's tree is
    /// dropped or rebuilt.
    imported_types: Arc<Mutex<FxHashMap<crate::calls::TypeKey, TypeId<'g>>>>,
    imported_generics: Arc<Mutex<FxHashMap<crate::calls::TypeKey, GenericId<'g>>>>,
    import_visits: usize,
    import_key_visits: usize,
    substituted_types: crate::memo::Memo<(TypeId<'g>, GenericsId<'g>), TypeId<'g>>,
    substituted_generics: crate::memo::Memo<(GenericId<'g>, GenericsId<'g>), GenericId<'g>>,
}

/// Restores branded values into one rustc context and retains completed results.
///
/// The session owns the memo so restored [`ty::Ty`] values cannot outlive the
/// [`ty::TyCtxt`] or be mixed with another values arena.
pub struct Restorer<'tcx, 'g> {
    tcx: ty::TyCtxt<'tcx>,
    values: Values<'g>,
    types: FxHashMap<TypeId<'g>, ty::Ty<'tcx>>,
    generics: FxHashMap<GenericId<'g>, ty::GenericArg<'tcx>>,
    /// Counts restoration worklist entries, including cached child visits.
    pub restore_visits: usize,
}

impl GenericsId<'_> {
    pub const EMPTY: Self = GenericsId(Sequence::EMPTY);
}

macro_rules! index_node {
    ($id:ident, $node:ident, $field:ident) => {
        impl<'g> std::ops::Index<$id<'g>> for Values<'g> {
            type Output = $node<'g>;
            fn index(&self, id: $id<'g>) -> &Self::Output {
                self.$field.get(id)
            }
        }
    };
}
impl<'g> std::ops::Index<TextId<'g>> for Values<'g> {
    type Output = str;
    fn index(&self, id: TextId<'g>) -> &str {
        self.texts.get(id)
    }
}
index_node!(TypeId, TypeNode, types);
index_node!(GenericId, GenericNode, generics);
index_node!(InstanceId, InstanceNode, instances);
index_node!(OriginId, OriginNode, origins);
index_node!(IdentityId, IdentityNode, identities);

mod sealed {
    pub trait List {}
}

pub trait ValueList<'g>: sealed::List + Copy {
    type Item: Copy + Eq + Hash;
    fn arena<'a>(values: &'a Values<'g>) -> &'a Sequences<'g, Self::Item>;
    fn arena_mut<'a>(values: &'a mut Values<'g>) -> &'a mut Sequences<'g, Self::Item>;
    fn root(self) -> Sequence<'g, Self::Item>;
    fn from_root(root: Sequence<'g, Self::Item>) -> Self;
}
macro_rules! value_list {
    ($id:ident, $item:ty, $field:ident) => {
        impl sealed::List for $id<'_> {}
        impl<'g> ValueList<'g> for $id<'g> {
            type Item = $item;
            fn arena<'a>(values: &'a Values<'g>) -> &'a Sequences<'g, Self::Item> {
                &values.$field
            }
            fn arena_mut<'a>(values: &'a mut Values<'g>) -> &'a mut Sequences<'g, Self::Item> {
                &mut values.$field
            }
            fn root(self) -> Sequence<'g, Self::Item> {
                self.0
            }
            fn from_root(root: Sequence<'g, Self::Item>) -> Self {
                Self(root)
            }
        }
    };
}
value_list!(TypesId, TypeId<'g>, type_lists);
value_list!(GenericsId, GenericId<'g>, generic_lists);
value_list!(FieldsId, usize, field_lists);
value_list!(CallsId, (DefId, Local), call_lists);

pub trait InternNode<'g> {
    type Id;
    fn intern(self, values: &mut Values<'g>) -> Result<Self::Id, CapacityError>;
}
macro_rules! intern_node {
    ($node:ident, $id:ident, $field:ident) => {
        impl<'g> InternNode<'g> for $node<'g> {
            type Id = $id<'g>;
            fn intern(self, values: &mut Values<'g>) -> Result<Self::Id, CapacityError> {
                values.$field.intern(self, CapacityError::Values)
            }
        }
    };
}
intern_node!(TypeNode, TypeId, types);
intern_node!(GenericNode, GenericId, generics);
intern_node!(InstanceNode, InstanceId, instances);
intern_node!(OriginNode, OriginId, origins);
intern_node!(IdentityNode, IdentityId, identities);

/// Gives values a fresh lifetime that cannot escape or be shared with another owner.
pub fn with_values<R>(f: impl for<'g> FnOnce(Values<'g>) -> R) -> R {
    let values = Values::new();
    f(values)
}

impl<'g> Values<'g> {
    pub(crate) fn new() -> Self {
        Self {
            texts: Intern::default(),
            types: Intern::default(),
            generics: Intern::default(),
            instances: Intern::default(),
            origins: Intern::default(),
            identities: Intern::default(),
            type_lists: Sequences::new(),
            generic_lists: Sequences::new(),
            field_lists: Sequences::new(),
            call_lists: Sequences::new(),
            imported_types: Arc::new(Mutex::new(FxHashMap::default())),
            imported_generics: Arc::new(Mutex::new(FxHashMap::default())),
            import_visits: 0,
            import_key_visits: 0,
            substituted_types: crate::memo::Memo::new(),
            substituted_generics: crate::memo::Memo::new(),
        }
    }
    /// Creates a view that interns into the same canonical values.
    pub fn share(&self) -> Self {
        Self {
            texts: self.texts.clone(),
            types: self.types.clone(),
            generics: self.generics.clone(),
            instances: self.instances.clone(),
            origins: self.origins.clone(),
            identities: self.identities.clone(),
            type_lists: self.type_lists.share(),
            generic_lists: self.generic_lists.share(),
            field_lists: self.field_lists.share(),
            call_lists: self.call_lists.share(),
            imported_types: Arc::clone(&self.imported_types),
            imported_generics: Arc::clone(&self.imported_generics),
            import_visits: self.import_visits,
            import_key_visits: self.import_key_visits,
            substituted_types: self.substituted_types.clone(),
            substituted_generics: self.substituted_generics.clone(),
        }
    }
    /// Starts a restoration session for this values arena and rustc context.
    pub fn restorer<'tcx>(&self, tcx: ty::TyCtxt<'tcx>) -> Restorer<'tcx, 'g> {
        let values = self.share();
        Restorer::new(tcx, values)
    }
    pub fn iter<'a, L: ValueList<'g> + 'a>(
        &'a self,
        list: L,
    ) -> impl DoubleEndedIterator<Item = L::Item> + 'a
    where
        L::Item: 'a,
    {
        let arena = L::arena(self);
        arena.iter(list.root()).copied()
    }
    // shapelint: allow(shallow-helper) Text identities enter through this checked value-arena boundary.
    pub fn intern_text(&mut self, text: &str) -> Result<TextId<'g>, CapacityError> {
        self.texts.intern_borrowed(text, CapacityError::Values)
    }
    pub fn intern<N: InternNode<'g>>(&mut self, node: N) -> Result<N::Id, CapacityError> {
        let id = node.intern(self)?;
        Ok(id)
    }
    pub fn intern_list<L: ValueList<'g>>(
        &mut self,
        values: impl IntoIterator<Item = L::Item>,
    ) -> Result<L, CapacityError> {
        let root = L::arena_mut(self).from_iter(values)?;
        Ok(L::from_root(root))
    }
    pub fn intern_identity(
        &mut self,
        identity: &Identity,
    ) -> Result<IdentityId<'g>, CapacityError> {
        let fields =
            self.intern_list::<crate::values::FieldsId<'_>>(identity.fields.iter().copied())?;
        let calls =
            self.intern_list::<crate::values::CallsId<'_>>(identity.calls.iter().copied())?;
        self.intern(IdentityNode {
            origin: identity.origin,
            fields,
            calls,
        })
    }
    pub fn export_identity(&self, id: IdentityId<'g>) -> Identity {
        let IdentityNode {
            origin,
            fields,
            calls,
        } = self[id];
        Identity {
            origin,
            fields: self.iter(fields).collect(),
            calls: self.iter(calls).collect(),
        }
    }
    pub fn intern_origin(&mut self, origin: &Origin) -> Result<OriginId<'g>, CapacityError> {
        let name = origin
            .name
            .as_deref()
            .map(|name| self.intern_text(name))
            .transpose()?;
        let identity = origin
            .identity
            .as_ref()
            .map(|identity| self.intern_identity(identity))
            .transpose()?;
        self.intern(OriginNode {
            def: origin.def,
            name,
            adt: origin.adt,
            identity,
        })
    }
    pub fn export_origin(&self, id: OriginId<'g>) -> Origin {
        let OriginNode {
            def,
            name,
            adt,
            identity,
        } = self[id];
        Origin {
            def,
            name: name.map(|id| self[id].to_owned()),
            adt,
            identity: identity.map(|id| self.export_identity(id)),
        }
    }
    pub fn intern_instance(
        &mut self,
        instance: &calls::Instance,
    ) -> Result<InstanceId<'g>, CapacityError> {
        let args = instance
            .args
            .iter()
            .map(|arg| self.intern_generic(arg))
            .collect::<Result<Vec<_>, _>>()?;
        let args = self.intern_list::<crate::values::GenericsId<'_>>(args)?;
        let dispatch = match instance.dispatch {
            calls::Dispatch::Item => Dispatch::Item,
            calls::Dispatch::Virtual => Dispatch::Virtual,
            calls::Dispatch::Shim => Dispatch::Shim,
            calls::Dispatch::Unresolved => Dispatch::Unresolved,
        };
        self.intern(InstanceNode {
            def: instance.def,
            args,
            dispatch,
        })
    }
    pub fn export_instance(&self, id: InstanceId<'g>) -> calls::Instance {
        let InstanceNode {
            def,
            args,
            dispatch,
        } = self[id];
        let args = self.iter(args).map(|id| self.export_generic(id)).collect();
        let dispatch = match dispatch {
            Dispatch::Item => calls::Dispatch::Item,
            Dispatch::Virtual => calls::Dispatch::Virtual,
            Dispatch::Shim => calls::Dispatch::Shim,
            Dispatch::Unresolved => calls::Dispatch::Unresolved,
        };
        calls::Instance {
            def,
            args,
            dispatch,
        }
    }
    pub fn intern_type(&mut self, ty: &Type) -> Result<TypeId<'g>, CapacityError> {
        let key = crate::calls::TypeKey::from(ty);
        self.import_key_visits = self
            .import_key_visits
            .saturating_add((&key).into_iter().count());
        if let Some(id) = self.imported_types.lock().get(&key).copied() {
            return Ok(id);
        }
        let (types, _) = self.import(Input::Type(ty))?;
        let id = types[&(ty as *const Type)];
        self.imported_types.lock().insert(key, id);
        Ok(id)
    }
    pub fn intern_generic(&mut self, arg: &Generic) -> Result<GenericId<'g>, CapacityError> {
        let key = crate::calls::TypeKey::from(arg);
        self.import_key_visits = self
            .import_key_visits
            .saturating_add((&key).into_iter().count());
        if let Some(id) = self.imported_generics.lock().get(&key).copied() {
            return Ok(id);
        }
        let (_, generics) = self.import(Input::Generic(arg))?;
        let id = generics[&(arg as *const Generic)];
        self.imported_generics.lock().insert(key, id);
        Ok(id)
    }
    /// Returns the number of owned type-tree entries traversed by imports.
    ///
    /// Structural cache hits do not add visits. This is intentionally a
    /// narrow work witness for scaling tests, not a semantic statistic.
    // shapelint: allow(shallow-helper) This read-only witness keeps arena accounting on its owner.
    pub fn import_visits(&self) -> usize {
        self.import_visits
    }
    /// Returns the number of structural tokens walked while building owned
    /// import keys. This is a boundary-work witness, not a semantic statistic.
    // shapelint: allow(shallow-helper) The read-only counter keeps key-boundary accounting on its owner.
    pub fn import_key_visits(&self) -> usize {
        self.import_key_visits
    }
    fn import<'a>(
        &mut self,
        input: Input<'a>,
    ) -> Result<
        (
            FxHashMap<*const Type, TypeId<'g>>,
            FxHashMap<*const Generic, GenericId<'g>>,
        ),
        CapacityError,
    > {
        let mut types = FxHashMap::default();
        let mut generics = FxHashMap::default();
        self.import_into(input, &mut types, &mut generics)?;
        Ok((types, generics))
    }
    fn import_into<'a>(
        &mut self,
        input: Input<'a>,
        types: &mut FxHashMap<*const Type, TypeId<'g>>,
        generics: &mut FxHashMap<*const Generic, GenericId<'g>>,
    ) -> Result<(), CapacityError> {
        let mut work = vec![(input, false)];
        while let Some((input, build)) = work.pop() {
            self.import_visits = self.import_visits.saturating_add(1);
            match input {
                Input::Type(ty) => {
                    let key = ty as *const Type;
                    if types.contains_key(&key) {
                        continue;
                    }
                    if !build {
                        work.push((Input::Type(ty), true));
                        match ty {
                            Type::Slice(t) | Type::Ref(_, t) | Type::RawPtr(_, t) => {
                                work.push((Input::Type(t), false))
                            }
                            Type::Array(t, g) => {
                                work.push((Input::Generic(g), false));
                                work.push((Input::Type(t), false));
                            }
                            Type::Tuple(ts) => {
                                work.extend(ts.iter().rev().map(|t| (Input::Type(t), false)))
                            }
                            Type::Adt(_, gs) | Type::Function(_, gs) | Type::Closure(_, gs) => {
                                work.extend(gs.iter().rev().map(|g| (Input::Generic(g), false)))
                            }
                            Type::Unknown
                            | Type::Parameter(_)
                            | Type::Bool
                            | Type::Char
                            | Type::Int(_)
                            | Type::Uint(_)
                            | Type::Float(_)
                            | Type::Str
                            | Type::Never => {}
                        }
                        continue;
                    }
                    let node = match ty {
                        Type::Unknown => TypeNode::Unknown,
                        Type::Parameter(n) => TypeNode::Parameter(*n),
                        Type::Bool => TypeNode::Bool,
                        Type::Char => TypeNode::Char,
                        Type::Int(n) => TypeNode::Int(*n),
                        Type::Uint(n) => TypeNode::Uint(*n),
                        Type::Float(n) => TypeNode::Float(*n),
                        Type::Str => TypeNode::Str,
                        Type::Never => TypeNode::Never,
                        Type::Slice(t) => TypeNode::Slice(types[&(&**t as *const Type)]),
                        Type::Array(t, g) => TypeNode::Array(
                            types[&(&**t as *const Type)],
                            generics[&(&**g as *const Generic)],
                        ),
                        Type::Tuple(ts) => {
                            TypeNode::Tuple(self.intern_list::<crate::values::TypesId<'_>>(
                                ts.iter().map(|t| types[&(t as *const Type)]),
                            )?)
                        }
                        Type::Ref(m, t) => TypeNode::Ref(*m, types[&(&**t as *const Type)]),
                        Type::RawPtr(m, t) => TypeNode::RawPtr(*m, types[&(&**t as *const Type)]),
                        Type::Adt(def, gs) => TypeNode::Adt(
                            *def,
                            self.intern_list::<crate::values::GenericsId<'_>>(
                                gs.iter().map(|g| generics[&(g as *const Generic)]),
                            )?,
                        ),
                        Type::Function(def, gs) => TypeNode::Function(
                            *def,
                            self.intern_list::<crate::values::GenericsId<'_>>(
                                gs.iter().map(|g| generics[&(g as *const Generic)]),
                            )?,
                        ),
                        Type::Closure(def, gs) => TypeNode::Closure(
                            *def,
                            self.intern_list::<crate::values::GenericsId<'_>>(
                                gs.iter().map(|g| generics[&(g as *const Generic)]),
                            )?,
                        ),
                    };
                    types.insert(key, self.intern(node)?);
                }
                Input::Generic(arg) => {
                    let key = arg as *const Generic;
                    if generics.contains_key(&key) {
                        continue;
                    }
                    if !build {
                        work.push((Input::Generic(arg), true));
                        match arg {
                            Generic::Type(t) | Generic::Const { ty: t, .. } => {
                                work.push((Input::Type(t), false))
                            }
                            Generic::Lifetime | Generic::Parameter(_) | Generic::Unknown => {}
                        }
                        continue;
                    }
                    let node = match arg {
                        Generic::Lifetime => GenericNode::Lifetime,
                        Generic::Type(t) => GenericNode::Type(types[&(t as *const Type)]),
                        Generic::Const { value, ty } => GenericNode::Const {
                            value: *value,
                            ty: types[&(ty as *const Type)],
                        },
                        Generic::Parameter(n) => GenericNode::Parameter(*n),
                        Generic::Unknown => GenericNode::Unknown,
                    };
                    generics.insert(key, self.intern(node)?);
                }
            }
        }
        Ok(())
    }
    pub fn replace_generic(
        &mut self,
        args: GenericsId<'g>,
        index: usize,
        value: GenericId<'g>,
    ) -> Result<Option<GenericsId<'g>>, CapacityError> {
        Ok(self
            .generic_lists
            .replace(args.0, index, value)?
            .map(GenericsId))
    }
    pub fn substitute_origin(
        &mut self,
        id: OriginId<'g>,
        scope: &Invocation<'g>,
    ) -> Result<OriginId<'g>, CapacityError> {
        let mut origin = self[id];
        if let Relocation::Into(call) = scope.relocation {
            origin.identity = match (origin.identity, call) {
                (Some(identity), Some(call)) => {
                    let identity = self[identity];
                    let call = self[call];
                    let prefix = self.call_lists.push(call.calls.0, call.origin)?;
                    let calls = CallsId(self.call_lists.append(prefix, identity.calls.0)?);
                    Some(self.intern(IdentityNode {
                        origin: identity.origin,
                        fields: identity.fields,
                        calls,
                    })?)
                }
                (Some(_), None) | (None, Some(_)) | (None, None) => None,
            };
        }
        self.intern(origin)
    }
    pub fn invalidate_origin_local(
        &mut self,
        id: OriginId<'g>,
        local: Local,
    ) -> Result<OriginId<'g>, CapacityError> {
        let mut origin = self[id];
        if let Some(identity) = origin.identity {
            let identity = self[identity];
            let root = self
                .call_lists
                .get(identity.calls.0, 0)
                .copied()
                .unwrap_or(identity.origin);
            if root.1 == local {
                origin.identity = None;
            }
        }
        self.intern(origin)
    }
}
impl<'tcx, 'g> Restorer<'tcx, 'g> {
    pub(crate) fn new(tcx: ty::TyCtxt<'tcx>, values: Values<'g>) -> Self {
        Self {
            tcx,
            values,
            types: FxHashMap::default(),
            generics: FxHashMap::default(),
            restore_visits: 0,
        }
    }

    pub fn restore_type(&mut self, id: TypeId<'g>) -> Option<ty::Ty<'tcx>> {
        if let Some(ty) = self.types.get(&id) {
            return Some(*ty);
        }
        self.restore(OutputId::Type(id))?;
        self.types.get(&id).copied()
    }
    pub fn restore_generic(&mut self, id: GenericId<'g>) -> Option<ty::GenericArg<'tcx>> {
        if let Some(arg) = self.generics.get(&id) {
            return Some(*arg);
        }
        self.restore(OutputId::Generic(id))?;
        self.generics.get(&id).copied()
    }
    fn restore(&mut self, root: OutputId<'g>) -> Option<()> {
        let mut pending = vec![(root, false)];
        while let Some((input, build)) = pending.pop() {
            self.restore_visits = self.restore_visits.saturating_add(1);
            match input {
                OutputId::Type(id) => {
                    if self.types.contains_key(&id) {
                        continue;
                    }
                    let node = self.values[id];
                    if !build {
                        pending.push((input, true));
                        match node {
                            TypeNode::Slice(t) | TypeNode::Ref(_, t) | TypeNode::RawPtr(_, t) => {
                                pending.push((OutputId::Type(t), false))
                            }
                            TypeNode::Array(t, g) => {
                                pending.push((OutputId::Generic(g), false));
                                pending.push((OutputId::Type(t), false));
                            }
                            TypeNode::Tuple(ts) => pending
                                .extend(self.values.iter(ts).map(|t| (OutputId::Type(t), false))),
                            TypeNode::Adt(_, gs)
                            | TypeNode::Function(_, gs)
                            | TypeNode::Closure(_, gs) => pending.extend(
                                self.values.iter(gs).map(|g| (OutputId::Generic(g), false)),
                            ),
                            TypeNode::Unknown
                            | TypeNode::Parameter(_)
                            | TypeNode::Bool
                            | TypeNode::Char
                            | TypeNode::Int(_)
                            | TypeNode::Uint(_)
                            | TypeNode::Float(_)
                            | TypeNode::Str
                            | TypeNode::Never => {}
                        }
                        continue;
                    }
                    let result = match node {
                        TypeNode::Unknown | TypeNode::Parameter(_) => return None,
                        TypeNode::Bool => self.tcx.types.bool,
                        TypeNode::Char => self.tcx.types.char,
                        TypeNode::Int(v) => ty::Ty::new_int(self.tcx, v),
                        TypeNode::Uint(v) => ty::Ty::new_uint(self.tcx, v),
                        TypeNode::Float(v) => ty::Ty::new_float(self.tcx, v),
                        TypeNode::Str => self.tcx.types.str_,
                        TypeNode::Never => self.tcx.types.never,
                        TypeNode::Slice(t) => ty::Ty::new_slice(self.tcx, self.types[&t]),
                        TypeNode::Array(t, g) => {
                            let ty::GenericArgKind::Const(length) = self.generics[&g].kind() else {
                                return None;
                            };
                            ty::Ty::new_array_with_const_len(self.tcx, self.types[&t], length)
                        }
                        TypeNode::Tuple(ts) => {
                            let fields: Vec<_> =
                                self.values.iter(ts).map(|t| self.types[&t]).collect();
                            ty::Ty::new_tup(self.tcx, &fields)
                        }
                        TypeNode::Ref(m, t) => ty::Ty::new_ref(
                            self.tcx,
                            self.tcx.lifetimes.re_erased,
                            self.types[&t],
                            m,
                        ),
                        TypeNode::RawPtr(m, t) => ty::Ty::new_ptr(self.tcx, self.types[&t], m),
                        TypeNode::Adt(def, gs)
                        | TypeNode::Function(def, gs)
                        | TypeNode::Closure(def, gs) => {
                            let args: Vec<_> =
                                self.values.iter(gs).map(|g| self.generics[&g]).collect();
                            match node {
                                TypeNode::Adt(..) => ty::Ty::new_adt(
                                    self.tcx,
                                    self.tcx.adt_def(def),
                                    self.tcx.mk_args(&args),
                                ),
                                TypeNode::Function(..) => {
                                    ty::Ty::new_fn_def(self.tcx, def, ty::Binder::dummy(args))
                                }
                                TypeNode::Closure(..) => {
                                    ty::Ty::new_closure(self.tcx, def, self.tcx.mk_args(&args))
                                }
                                _ => unreachable!("matched nominal type"),
                            }
                        }
                    };
                    self.types.insert(id, result);
                }
                OutputId::Generic(id) => {
                    if self.generics.contains_key(&id) {
                        continue;
                    }
                    let node = self.values[id];
                    if !build {
                        pending.push((input, true));
                        match node {
                            GenericNode::Type(t) | GenericNode::Const { ty: t, .. } => {
                                pending.push((OutputId::Type(t), false))
                            }
                            GenericNode::Lifetime
                            | GenericNode::Parameter(_)
                            | GenericNode::Unknown => {}
                        }
                        continue;
                    }
                    let result = match node {
                        GenericNode::Lifetime => self.tcx.lifetimes.re_erased.into(),
                        GenericNode::Type(t) => self.types[&t].into(),
                        GenericNode::Const { value, ty } => ty::Const::from_bits(
                            self.tcx,
                            value,
                            ty::TypingEnv::fully_monomorphized(),
                            self.types[&ty],
                        )
                        .into(),
                        GenericNode::Parameter(_) | GenericNode::Unknown => return None,
                    };
                    self.generics.insert(id, result);
                }
            }
        }
        Some(())
    }
}
impl<'g> Values<'g> {
    pub fn substitute_type(
        &mut self,
        ty: TypeId<'g>,
        arguments: GenericsId<'g>,
    ) -> Result<TypeId<'g>, CapacityError> {
        self.substitute(arguments, |values| {
            values
                .substituted_types
                .get(&(ty, arguments))
                .ok_or(OutputId::Type(ty))
        })
    }
    pub fn substitute_generic(
        &mut self,
        arg: GenericId<'g>,
        arguments: GenericsId<'g>,
    ) -> Result<GenericId<'g>, CapacityError> {
        self.substitute(arguments, |values| {
            values
                .substituted_generics
                .get(&(arg, arguments))
                .ok_or(OutputId::Generic(arg))
        })
    }
    pub fn substitute_instance(
        &mut self,
        id: InstanceId<'g>,
        arguments: GenericsId<'g>,
    ) -> Result<InstanceId<'g>, CapacityError> {
        let InstanceNode {
            def,
            args,
            dispatch,
        } = self[id];
        let children: Vec<_> = self.iter(args).collect();
        let mapped = children
            .into_iter()
            .map(|arg| self.substitute_generic(arg, arguments))
            .collect::<Result<Vec<_>, _>>()?;
        let args = self.intern_list::<crate::values::GenericsId<'_>>(mapped)?;
        self.intern(InstanceNode {
            def,
            args,
            dispatch,
        })
    }
    fn substitute<R>(
        &mut self,
        arguments: GenericsId<'g>,
        root: impl Fn(&Self) -> Result<R, OutputId<'g>>,
    ) -> Result<R, CapacityError> {
        use crate::memo::{Demand, VisitOrder, collect, resolve};
        resolve(self, root, |values, request| {
            let ty = |child| values.substituted_types.get(&(child, arguments));
            let arg = |child| values.substituted_generics.get(&(child, arguments));
            let need_ty = |child| ty(child).ok_or(Demand::Child(OutputId::Type(child)));
            let need_arg = |child| arg(child).ok_or(Demand::Child(OutputId::Generic(child)));
            match request {
                OutputId::Type(id) => {
                    let key = (id, arguments);
                    if values.substituted_types.get(&key).is_some() {
                        return Ok(());
                    }
                    let result = match values[id] {
                        TypeNode::Parameter(index) => match values
                            .generic_lists
                            .get(arguments.0, index as usize)
                            .map(|arg| values[*arg])
                        {
                            Some(GenericNode::Type(ty)) => ty,
                            _ => id,
                        },
                        TypeNode::Slice(t) => values.intern(TypeNode::Slice(need_ty(t)?))?,
                        TypeNode::Array(t, g) => {
                            values.intern(TypeNode::Array(need_ty(t)?, need_arg(g)?))?
                        }
                        TypeNode::Ref(m, t) => values.intern(TypeNode::Ref(m, need_ty(t)?))?,
                        TypeNode::RawPtr(m, t) => {
                            values.intern(TypeNode::RawPtr(m, need_ty(t)?))?
                        }
                        TypeNode::Tuple(ts) => {
                            let mapped =
                                collect(values.iter(ts), ty, OutputId::Type, VisitOrder::Reverse)?;
                            let ts = values.intern_list::<TypesId<'g>>(mapped)?;
                            values.intern(TypeNode::Tuple(ts))?
                        }
                        node @ (TypeNode::Adt(_, gs)
                        | TypeNode::Function(_, gs)
                        | TypeNode::Closure(_, gs)) => {
                            let mapped = collect(
                                values.iter(gs),
                                arg,
                                OutputId::Generic,
                                VisitOrder::Reverse,
                            )?;
                            let gs = values.intern_list::<GenericsId<'g>>(mapped)?;
                            let node = match node {
                                TypeNode::Adt(def, _) => TypeNode::Adt(def, gs),
                                TypeNode::Function(def, _) => TypeNode::Function(def, gs),
                                TypeNode::Closure(def, _) => TypeNode::Closure(def, gs),
                                _ => unreachable!("matched nominal type"),
                            };
                            values.intern(node)?
                        }
                        TypeNode::Unknown
                        | TypeNode::Bool
                        | TypeNode::Char
                        | TypeNode::Int(_)
                        | TypeNode::Uint(_)
                        | TypeNode::Float(_)
                        | TypeNode::Str
                        | TypeNode::Never => id,
                    };
                    values.substituted_types.insert(key, result);
                }
                OutputId::Generic(id) => {
                    let key = (id, arguments);
                    if values.substituted_generics.get(&key).is_some() {
                        return Ok(());
                    }
                    let result = match values[id] {
                        GenericNode::Parameter(index) => values
                            .generic_lists
                            .get(arguments.0, index as usize)
                            .copied()
                            .unwrap_or(id),
                        GenericNode::Type(t) => values.intern(GenericNode::Type(need_ty(t)?))?,
                        GenericNode::Const { value, ty } => values.intern(GenericNode::Const {
                            value,
                            ty: need_ty(ty)?,
                        })?,
                        GenericNode::Lifetime | GenericNode::Unknown => id,
                    };
                    values.substituted_generics.insert(key, result);
                }
            }
            Ok(())
        })
    }
    pub fn export_type(&self, id: TypeId<'g>) -> Type {
        match self.export(OutputId::Type(id)) {
            Output::Type(t) => t,
            Output::Generic(_) => unreachable!("type root"),
        }
    }
    pub fn export_generic(&self, id: GenericId<'g>) -> Generic {
        match self.export(OutputId::Generic(id)) {
            Output::Generic(g) => g,
            Output::Type(_) => unreachable!("generic root"),
        }
    }
    fn export(&self, root: OutputId<'g>) -> Output {
        let children = |id, work: &mut Vec<(OutputId<'g>, bool)>| match id {
            OutputId::Type(id) => match self[id] {
                TypeNode::Slice(t) | TypeNode::Ref(_, t) | TypeNode::RawPtr(_, t) => {
                    work.push((OutputId::Type(t), false))
                }
                TypeNode::Array(t, g) => {
                    work.push((OutputId::Generic(g), false));
                    work.push((OutputId::Type(t), false));
                }
                TypeNode::Tuple(ts) => {
                    work.extend(self.iter(ts).rev().map(|t| (OutputId::Type(t), false)))
                }
                TypeNode::Adt(_, gs) | TypeNode::Function(_, gs) | TypeNode::Closure(_, gs) => {
                    work.extend(self.iter(gs).rev().map(|g| (OutputId::Generic(g), false)))
                }
                TypeNode::Unknown
                | TypeNode::Parameter(_)
                | TypeNode::Bool
                | TypeNode::Char
                | TypeNode::Int(_)
                | TypeNode::Uint(_)
                | TypeNode::Float(_)
                | TypeNode::Str
                | TypeNode::Never => {}
            },
            OutputId::Generic(id) => match self[id] {
                GenericNode::Type(t) | GenericNode::Const { ty: t, .. } => {
                    work.push((OutputId::Type(t), false))
                }
                GenericNode::Lifetime | GenericNode::Parameter(_) | GenericNode::Unknown => {}
            },
        };
        let build = |id, outputs: &mut Vec<Output>| match id {
            OutputId::Type(id) => {
                let node = match self[id] {
                    TypeNode::Unknown => Type::Unknown,
                    TypeNode::Parameter(n) => Type::Parameter(n),
                    TypeNode::Bool => Type::Bool,
                    TypeNode::Char => Type::Char,
                    TypeNode::Int(n) => Type::Int(n),
                    TypeNode::Uint(n) => Type::Uint(n),
                    TypeNode::Float(n) => Type::Float(n),
                    TypeNode::Str => Type::Str,
                    TypeNode::Never => Type::Never,
                    TypeNode::Slice(_) => Type::Slice(Box::new(pop_type(outputs))),
                    TypeNode::Array(_, _) => {
                        let g = pop_generic(outputs);
                        let t = pop_type(outputs);
                        Type::Array(Box::new(t), Box::new(g))
                    }
                    TypeNode::Tuple(ts) => {
                        let n = self.type_lists.len(ts.0);
                        let mut ts: Vec<_> = (0..n).map(|_| pop_type(outputs)).collect();
                        ts.reverse();
                        Type::Tuple(ts)
                    }
                    TypeNode::Ref(m, _) => Type::Ref(m, Box::new(pop_type(outputs))),
                    TypeNode::RawPtr(m, _) => Type::RawPtr(m, Box::new(pop_type(outputs))),
                    TypeNode::Adt(def, gs)
                    | TypeNode::Function(def, gs)
                    | TypeNode::Closure(def, gs) => {
                        let n = self.generic_lists.len(gs.0);
                        let mut args: Vec<_> = (0..n).map(|_| pop_generic(outputs)).collect();
                        args.reverse();
                        match self[id] {
                            TypeNode::Adt(..) => Type::Adt(def, args),
                            TypeNode::Function(..) => Type::Function(def, args),
                            TypeNode::Closure(..) => Type::Closure(def, args),
                            _ => unreachable!("matched nominal type"),
                        }
                    }
                };
                Output::Type(node)
            }
            OutputId::Generic(id) => {
                let node = match self[id] {
                    GenericNode::Lifetime => Generic::Lifetime,
                    GenericNode::Type(_) => Generic::Type(pop_type(outputs)),
                    GenericNode::Const { value, .. } => Generic::Const {
                        value,
                        ty: pop_type(outputs),
                    },
                    GenericNode::Parameter(n) => Generic::Parameter(n),
                    GenericNode::Unknown => Generic::Unknown,
                };
                Output::Generic(node)
            }
        };
        let mut work = Vec::new();
        let mut outputs = Vec::new();
        children(root, &mut work);
        while let Some((id, ready)) = work.pop() {
            if ready {
                let value = build(id, &mut outputs);
                outputs.push(value);
            } else {
                work.push((id, true));
                children(id, &mut work);
            }
        }
        build(root, &mut outputs)
    }
}
/// Reuses rustc captures within one compiler context and branded value owner.
pub struct Captures<'tcx, 'g> {
    tcx: ty::TyCtxt<'tcx>,
    values: Values<'g>,
    restorer: Restorer<'tcx, 'g>,
    types: FxHashMap<ty::Ty<'tcx>, TypeId<'g>>,
    generics: FxHashMap<ty::GenericArg<'tcx>, GenericId<'g>>,
    instances: FxHashMap<(ty::TypingEnv<'tcx>, DefId, ty::GenericArgsRef<'tcx>), InstanceId<'g>>,
    resolved_instances: FxHashMap<InstanceId<'g>, InstanceId<'g>>,
    /// Counts capture worklist entries, including cached child visits.
    pub capture_visits: usize,
}

impl<'tcx, 'g> Captures<'tcx, 'g> {
    pub fn new(tcx: ty::TyCtxt<'tcx>, values: Values<'g>) -> Self {
        let captures = Self {
            tcx,
            restorer: values.restorer(tcx),
            values,
            types: FxHashMap::default(),
            generics: FxHashMap::default(),
            instances: FxHashMap::default(),
            resolved_instances: FxHashMap::default(),
            capture_visits: 0,
        };
        captures
    }
    pub fn capture_instance(
        &mut self,
        environment: ty::TypingEnv<'tcx>,
        def: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<InstanceId<'g>, CapacityError> {
        let key = (environment, def, args);
        if let Some(instance) = self.instances.get(&key) {
            return Ok(*instance);
        }
        let (def, args, dispatch) =
            match ty::Instance::try_resolve(self.tcx, environment, def, args) {
                Ok(Some(instance)) => (
                    instance.def_id(),
                    instance.args,
                    match instance.def {
                        ty::InstanceKind::Item(_) => Dispatch::Item,
                        ty::InstanceKind::Virtual(..) => Dispatch::Virtual,
                        ty::InstanceKind::Shim(_)
                        | ty::InstanceKind::Intrinsic(_)
                        | ty::InstanceKind::LlvmIntrinsic(_) => Dispatch::Shim,
                    },
                ),
                _ => (def, args, Dispatch::Unresolved),
            };
        let args = args
            .iter()
            .map(|arg| self.capture_generic(arg))
            .collect::<Result<Vec<_>, _>>()?;
        let args = self
            .values
            .intern_list::<crate::values::GenericsId<'_>>(args)?;
        let instance = self.values.intern(InstanceNode {
            def,
            args,
            dispatch,
        })?;
        self.instances.insert(key, instance);
        Ok(instance)
    }
    pub fn resolve_instance(
        &mut self,
        id: InstanceId<'g>,
    ) -> Result<InstanceId<'g>, CapacityError> {
        if let Some(instance) = self.resolved_instances.get(&id) {
            return Ok(*instance);
        }
        let InstanceNode {
            def,
            args,
            dispatch,
        } = self.values[id];
        if let Dispatch::Item = dispatch {
            return Ok(id);
        }
        let Some(args) = self
            .values
            .iter(args)
            .map(|arg| self.restorer.restore_generic(arg))
            .collect::<Option<Vec<_>>>()
        else {
            self.resolved_instances.insert(id, id);
            return Ok(id);
        };
        let instance = self.capture_instance(
            ty::TypingEnv::fully_monomorphized(),
            def,
            self.tcx.mk_args(&args),
        )?;
        self.resolved_instances.insert(id, instance);
        Ok(instance)
    }
    pub fn capture_type(&mut self, ty: ty::Ty<'tcx>) -> Result<TypeId<'g>, CapacityError> {
        self.capture(Capture::Type(ty))?;
        Ok(self.types[&ty])
    }
    pub fn capture_generic(
        &mut self,
        arg: ty::GenericArg<'tcx>,
    ) -> Result<GenericId<'g>, CapacityError> {
        self.capture(Capture::Generic(arg))?;
        Ok(self.generics[&arg])
    }
    fn capture(&mut self, root: Capture<'tcx>) -> Result<(), CapacityError> {
        let types = &mut self.types;
        let generics = &mut self.generics;
        let mut pending = vec![(root, CaptureStep::Visit)];
        while let Some((input, step)) = pending.pop() {
            self.capture_visits = self.capture_visits.saturating_add(1);
            match input {
                Capture::Type(ty) => {
                    if types.contains_key(&ty) {
                        continue;
                    }
                    if let CaptureStep::Visit = step {
                        pending.push((input, CaptureStep::Build));
                        match ty.kind() {
                            ty::Slice(t) | ty::Ref(_, t, _) | ty::RawPtr(t, _) => {
                                pending.push((Capture::Type(*t), CaptureStep::Visit))
                            }
                            ty::Array(t, g) => {
                                pending.push((Capture::Generic((*g).into()), CaptureStep::Visit));
                                pending.push((Capture::Type(*t), CaptureStep::Visit));
                            }
                            ty::Tuple(ts) => pending
                                .extend(ts.iter().map(|t| (Capture::Type(t), CaptureStep::Visit))),
                            ty::Adt(_, gs) | ty::Closure(_, gs) => pending.extend(
                                gs.iter().map(|g| (Capture::Generic(g), CaptureStep::Visit)),
                            ),
                            ty::FnDef(_, gs) => pending.extend(
                                gs.skip_binder()
                                    .iter()
                                    .map(|g| (Capture::Generic(g), CaptureStep::Visit)),
                            ),
                            _ => {}
                        }
                        continue;
                    }
                    let node = match ty.kind() {
                        ty::Param(p) => TypeNode::Parameter(p.index),
                        ty::Bool => TypeNode::Bool,
                        ty::Char => TypeNode::Char,
                        ty::Int(v) => TypeNode::Int(*v),
                        ty::Uint(v) => TypeNode::Uint(*v),
                        ty::Float(v) => TypeNode::Float(*v),
                        ty::Str => TypeNode::Str,
                        ty::Never => TypeNode::Never,
                        ty::Slice(t) => TypeNode::Slice(types[t]),
                        ty::Array(t, g) => TypeNode::Array(types[t], generics[&(*g).into()]),
                        ty::Tuple(ts) => {
                            TypeNode::Tuple(self.values.intern_list::<crate::values::TypesId<'_>>(
                                ts.iter().map(|t| types[&t]),
                            )?)
                        }
                        ty::Ref(_, t, m) => TypeNode::Ref(*m, types[t]),
                        ty::RawPtr(t, m) => TypeNode::RawPtr(*m, types[t]),
                        ty::Adt(adt, gs) => TypeNode::Adt(
                            adt.did(),
                            self.values.intern_list::<crate::values::GenericsId<'_>>(
                                gs.iter().map(|g| generics[&g]),
                            )?,
                        ),
                        ty::FnDef(def, gs) => TypeNode::Function(
                            *def,
                            self.values.intern_list::<crate::values::GenericsId<'_>>(
                                gs.skip_binder().iter().map(|g| generics[&g]),
                            )?,
                        ),
                        ty::Closure(def, gs) => TypeNode::Closure(
                            *def,
                            self.values.intern_list::<crate::values::GenericsId<'_>>(
                                gs.iter().map(|g| generics[&g]),
                            )?,
                        ),
                        _ => TypeNode::Unknown,
                    };
                    types.insert(ty, self.values.intern(node)?);
                }
                Capture::Generic(arg) => {
                    if generics.contains_key(&arg) {
                        continue;
                    }
                    if let CaptureStep::Visit = step {
                        pending.push((input, CaptureStep::Build));
                        match arg.kind() {
                            ty::GenericArgKind::Type(t) => {
                                pending.push((Capture::Type(t), CaptureStep::Visit))
                            }
                            ty::GenericArgKind::Const(c) => {
                                if let ty::ConstKind::Value(value) = c.kind() {
                                    if let Some(_) = value.try_to_leaf() {
                                        pending.push((Capture::Type(value.ty), CaptureStep::Visit));
                                    }
                                }
                            }
                            ty::GenericArgKind::Lifetime(_) => {}
                        }
                        continue;
                    }
                    let node = match arg.kind() {
                        ty::GenericArgKind::Lifetime(_) => GenericNode::Lifetime,
                        ty::GenericArgKind::Type(t) => GenericNode::Type(types[&t]),
                        ty::GenericArgKind::Const(c) => match c.kind() {
                            ty::ConstKind::Param(p) => GenericNode::Parameter(p.index),
                            ty::ConstKind::Value(v) => match v.try_to_leaf() {
                                Some(scalar) => GenericNode::Const {
                                    value: scalar.to_bits_unchecked(),
                                    ty: types[&v.ty],
                                },
                                None => GenericNode::Unknown,
                            },
                            _ => GenericNode::Unknown,
                        },
                    };
                    generics.insert(arg, self.values.intern(node)?);
                }
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy)]
enum CaptureStep {
    Visit,
    Build,
}

#[derive(Clone, Copy)]
enum Capture<'tcx> {
    Type(ty::Ty<'tcx>),
    Generic(ty::GenericArg<'tcx>),
}
#[derive(Clone, Copy)]
enum Input<'a> {
    Type(&'a Type),
    Generic(&'a Generic),
}
#[derive(Clone, Copy)]
enum OutputId<'g> {
    Type(TypeId<'g>),
    Generic(GenericId<'g>),
}
enum Output {
    Type(Type),
    Generic(Generic),
}
fn pop_type(outputs: &mut Vec<Output>) -> Type {
    match outputs.pop() {
        Some(Output::Type(t)) => t,
        _ => unreachable!("type child"),
    }
}
fn pop_generic(outputs: &mut Vec<Output>) -> Generic {
    match outputs.pop() {
        Some(Output::Generic(g)) => g,
        _ => unreachable!("generic child"),
    }
}
