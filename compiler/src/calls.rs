use std::hash::{Hash, Hasher};

use rustc_hir::Mutability;
use rustc_hir::def_id::DefId;
use rustc_middle::ty;

pub use crate::contracts::Target;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Dispatch {
    Item,
    Virtual,
    Shim,
    Unresolved,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Instance {
    pub def: DefId,
    pub args: Vec<Generic>,
    pub dispatch: Dispatch,
}

pub enum Generic {
    Lifetime,
    Type(Type),
    Const { value: u128, ty: Type },
    Parameter(u32),
    Unknown,
}

pub enum Type {
    Unknown,
    Parameter(u32),
    Bool,
    Char,
    Int(ty::IntTy),
    Uint(ty::UintTy),
    Float(ty::FloatTy),
    Str,
    Never,
    Slice(Box<Type>),
    Array(Box<Type>, Box<Generic>),
    Tuple(Vec<Type>),
    Ref(rustc_hir::Mutability, Box<Type>),
    RawPtr(rustc_hir::Mutability, Box<Type>),
    Adt(DefId, Vec<Generic>),
    Function(DefId, Vec<Generic>),
    Closure(DefId, Vec<Generic>),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum TypeToken {
    Unknown,
    Parameter(u32),
    Bool,
    Char,
    Int(ty::IntTy),
    Uint(ty::UintTy),
    Float(ty::FloatTy),
    Str,
    Never,
    Slice,
    Array,
    Tuple(usize),
    Ref(Mutability),
    RawPtr(Mutability),
    Adt(DefId, usize),
    Function(DefId, usize),
    Closure(DefId, usize),
    Lifetime,
    GenericType,
    Const(u128),
    GenericParameter(u32),
    GenericUnknown,
}

enum TypeInput<'a> {
    Type(&'a Type),
    Generic(&'a Generic),
}
pub(crate) enum TypeOutput {
    Type(Type),
    Generic(Generic),
}

struct TypeTokens<'a> {
    first: Option<TypeInput<'a>>,
    pending: Vec<TypeInput<'a>>,
}

impl<'a> TypeTokens<'a> {
    fn new(input: TypeInput<'a>) -> Self {
        Self {
            first: Some(input),
            pending: Vec::new(),
        }
    }

    fn token(&mut self, input: TypeInput<'a>) -> TypeToken {
        match input {
            TypeInput::Type(ty) => match ty {
                Type::Unknown => TypeToken::Unknown,
                Type::Parameter(index) => TypeToken::Parameter(*index),
                Type::Bool => TypeToken::Bool,
                Type::Char => TypeToken::Char,
                Type::Int(ty) => TypeToken::Int(*ty),
                Type::Uint(ty) => TypeToken::Uint(*ty),
                Type::Float(ty) => TypeToken::Float(*ty),
                Type::Str => TypeToken::Str,
                Type::Never => TypeToken::Never,
                Type::Slice(inner) => {
                    self.pending.push(TypeInput::Type(inner));
                    TypeToken::Slice
                }
                Type::Array(inner, length) => {
                    self.pending.push(TypeInput::Generic(length));
                    self.pending.push(TypeInput::Type(inner));
                    TypeToken::Array
                }
                Type::Tuple(fields) => {
                    self.pending
                        .extend(fields.iter().rev().map(TypeInput::Type));
                    TypeToken::Tuple(fields.len())
                }
                Type::Ref(mutability, inner) => {
                    self.pending.push(TypeInput::Type(inner));
                    TypeToken::Ref(*mutability)
                }
                Type::RawPtr(mutability, inner) => {
                    self.pending.push(TypeInput::Type(inner));
                    TypeToken::RawPtr(*mutability)
                }
                Type::Adt(def, args) => {
                    self.pending
                        .extend(args.iter().rev().map(TypeInput::Generic));
                    TypeToken::Adt(*def, args.len())
                }
                Type::Function(def, args) => {
                    self.pending
                        .extend(args.iter().rev().map(TypeInput::Generic));
                    TypeToken::Function(*def, args.len())
                }
                Type::Closure(def, args) => {
                    self.pending
                        .extend(args.iter().rev().map(TypeInput::Generic));
                    TypeToken::Closure(*def, args.len())
                }
            },
            TypeInput::Generic(arg) => match arg {
                Generic::Lifetime => TypeToken::Lifetime,
                Generic::Type(ty) => {
                    self.pending.push(TypeInput::Type(ty));
                    TypeToken::GenericType
                }
                Generic::Const { value, ty } => {
                    self.pending.push(TypeInput::Type(ty));
                    TypeToken::Const(*value)
                }
                Generic::Parameter(index) => TypeToken::GenericParameter(*index),
                Generic::Unknown => TypeToken::GenericUnknown,
            },
        }
    }
}

impl Iterator for TypeTokens<'_> {
    type Item = TypeToken;

    fn next(&mut self) -> Option<Self::Item> {
        let input = self.first.take().or_else(|| self.pending.pop())?;
        Some(self.token(input))
    }
}

#[derive(Default)]
struct TypeBuilder {
    values: Vec<TypeOutput>,
}

impl TypeBuilder {
    fn take_type(&mut self) -> Type {
        match self.values.pop() {
            Some(TypeOutput::Type(ty)) => ty,
            _ => unreachable!("type token owns a type child"),
        }
    }

    fn take_generic(&mut self) -> Generic {
        match self.values.pop() {
            Some(TypeOutput::Generic(arg)) => arg,
            _ => unreachable!("type token owns a generic child"),
        }
    }

    fn assemble(&mut self, token: TypeToken) -> TypeOutput {
        let ty = match token {
            TypeToken::Unknown => Type::Unknown,
            TypeToken::Parameter(index) => Type::Parameter(index),
            TypeToken::Bool => Type::Bool,
            TypeToken::Char => Type::Char,
            TypeToken::Int(ty) => Type::Int(ty),
            TypeToken::Uint(ty) => Type::Uint(ty),
            TypeToken::Float(ty) => Type::Float(ty),
            TypeToken::Str => Type::Str,
            TypeToken::Never => Type::Never,
            TypeToken::Slice => Type::Slice(Box::new(self.take_type())),
            TypeToken::Array => {
                Type::Array(Box::new(self.take_type()), Box::new(self.take_generic()))
            }
            TypeToken::Tuple(len) => Type::Tuple((0..len).map(|_| self.take_type()).collect()),
            TypeToken::Ref(mutability) => Type::Ref(mutability, Box::new(self.take_type())),
            TypeToken::RawPtr(mutability) => Type::RawPtr(mutability, Box::new(self.take_type())),
            TypeToken::Adt(def, len) => {
                Type::Adt(def, (0..len).map(|_| self.take_generic()).collect())
            }
            TypeToken::Function(def, len) => {
                Type::Function(def, (0..len).map(|_| self.take_generic()).collect())
            }
            TypeToken::Closure(def, len) => {
                Type::Closure(def, (0..len).map(|_| self.take_generic()).collect())
            }
            TypeToken::Lifetime => {
                return TypeOutput::Generic(Generic::Lifetime);
            }
            TypeToken::GenericType => {
                let ty = self.take_type();
                return TypeOutput::Generic(Generic::Type(ty));
            }
            TypeToken::Const(value) => {
                let ty = self.take_type();
                return TypeOutput::Generic(Generic::Const { value, ty });
            }
            TypeToken::GenericParameter(index) => {
                return TypeOutput::Generic(Generic::Parameter(index));
            }
            TypeToken::GenericUnknown => {
                return TypeOutput::Generic(Generic::Unknown);
            }
        };
        TypeOutput::Type(ty)
    }
}

impl From<TypeKey> for TypeOutput {
    fn from(TypeKey(snapshot): TypeKey) -> Self {
        let key = *snapshot;
        let mut builder = TypeBuilder::default();
        let children = key.children.into_iter().rev();
        for token in children {
            let child = builder.assemble(token);
            builder.values.push(child);
        }
        builder.assemble(key.root)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct TypeKey(Box<TypeSnapshot>);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct TypeSnapshot {
    root: TypeToken,
    children: Box<[TypeToken]>,
}

#[derive(Debug, thiserror::Error)]
pub enum TypeStructureError {
    #[error("type metadata has a missing child")]
    MissingChild,
    #[error("type metadata has a child of the wrong kind")]
    WrongChildKind,
    #[error("type metadata is empty")]
    Empty,
    #[error("type metadata has {count} roots instead of one")]
    ExtraRoots { count: usize },
}

impl<'a> IntoIterator for &'a TypeKey {
    type Item = &'a TypeToken;
    type IntoIter =
        std::iter::Chain<std::iter::Once<&'a TypeToken>, std::slice::Iter<'a, TypeToken>>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(&self.0.root).chain(&self.0.children)
    }
}
impl TryFrom<Vec<TypeToken>> for TypeKey {
    type Error = TypeStructureError;
    fn try_from(tokens: Vec<TypeToken>) -> Result<Self, Self::Error> {
        #[derive(PartialEq, Eq)]
        enum Kind {
            Type,
            Generic,
        }
        let mut tokens = tokens.into_iter();
        let key = Self(Box::new(TypeSnapshot {
            root: tokens.next().ok_or(TypeStructureError::Empty)?,
            children: tokens.collect(),
        }));
        let mut values = Vec::new();
        let reversed = (&key).into_iter().rev();
        for token in reversed {
            let mut take = |kind| match values.pop() {
                Some(actual) if actual == kind => Ok(()),
                Some(_) => Err(TypeStructureError::WrongChildKind),
                None => Err(TypeStructureError::MissingChild),
            };
            let kind = match token {
                TypeToken::Slice | TypeToken::Ref(_) | TypeToken::RawPtr(_) => {
                    take(Kind::Type)?;
                    Kind::Type
                }
                TypeToken::Array => {
                    take(Kind::Type)?;
                    take(Kind::Generic)?;
                    Kind::Type
                }
                TypeToken::Tuple(count) => {
                    for _ in 0..*count {
                        take(Kind::Type)?;
                    }
                    Kind::Type
                }
                TypeToken::Adt(_, count)
                | TypeToken::Function(_, count)
                | TypeToken::Closure(_, count) => {
                    for _ in 0..*count {
                        take(Kind::Generic)?;
                    }
                    Kind::Type
                }
                TypeToken::GenericType | TypeToken::Const(_) => {
                    take(Kind::Type)?;
                    Kind::Generic
                }
                TypeToken::Lifetime
                | TypeToken::GenericParameter(_)
                | TypeToken::GenericUnknown => Kind::Generic,
                TypeToken::Unknown
                | TypeToken::Parameter(_)
                | TypeToken::Bool
                | TypeToken::Char
                | TypeToken::Int(_)
                | TypeToken::Uint(_)
                | TypeToken::Float(_)
                | TypeToken::Str
                | TypeToken::Never => Kind::Type,
            };
            values.push(kind);
        }
        match values.as_slice() {
            [_] => Ok(key),
            [] => Err(TypeStructureError::Empty),
            values => Err(TypeStructureError::ExtraRoots {
                count: values.len(),
            }),
        }
    }
}

impl From<TypeInput<'_>> for TypeKey {
    fn from(input: TypeInput<'_>) -> Self {
        let mut tokens = TypeTokens {
            first: None,
            pending: Vec::new(),
        };
        Self(Box::new(TypeSnapshot {
            root: tokens.token(input),
            children: tokens.collect(),
        }))
    }
}

impl From<&Type> for TypeKey {
    fn from(ty: &Type) -> Self {
        TypeInput::Type(ty).into()
    }
}
impl From<&Generic> for TypeKey {
    fn from(arg: &Generic) -> Self {
        TypeInput::Generic(arg).into()
    }
}

impl Clone for Type {
    fn clone(&self) -> Self {
        match TypeOutput::from(TypeKey::from(self)) {
            TypeOutput::Type(ty) => ty,
            TypeOutput::Generic(_) => unreachable!("the clone root is a type"),
        }
    }
}
impl PartialEq for Type {
    fn eq(&self, other: &Self) -> bool {
        TypeTokens::new(TypeInput::Type(self)).eq(TypeTokens::new(TypeInput::Type(other)))
    }
}
impl Eq for Type {}
impl Hash for Type {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for token in TypeTokens::new(TypeInput::Type(self)) {
            token.hash(state);
        }
    }
}

impl Clone for Generic {
    fn clone(&self) -> Self {
        match TypeOutput::from(TypeKey::from(self)) {
            TypeOutput::Generic(arg) => arg,
            TypeOutput::Type(_) => unreachable!("the clone root is a generic argument"),
        }
    }
}
impl PartialEq for Generic {
    fn eq(&self, other: &Self) -> bool {
        TypeTokens::new(TypeInput::Generic(self)).eq(TypeTokens::new(TypeInput::Generic(other)))
    }
}
impl Eq for Generic {}
impl Hash for Generic {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for token in TypeTokens::new(TypeInput::Generic(self)) {
            token.hash(state);
        }
    }
}

impl Type {
    fn drain_children(&mut self, pending: &mut Vec<TypeOutput>) {
        let mut take = |ty: &mut Type| {
            if let Type::Unknown = ty {
                return;
            }
            pending.push(TypeOutput::Type(std::mem::replace(ty, Type::Unknown)));
        };
        match self {
            Type::Slice(inner) | Type::Ref(_, inner) | Type::RawPtr(_, inner) => take(inner),
            Type::Array(inner, length) => {
                take(inner);
                if let Generic::Unknown = &**length {
                    return;
                }
                pending.push(TypeOutput::Generic(std::mem::replace(
                    length,
                    Generic::Unknown,
                )));
            }
            Type::Tuple(fields) => pending.extend(fields.drain(..).map(TypeOutput::Type)),
            Type::Adt(_, args) | Type::Function(_, args) | Type::Closure(_, args) => {
                pending.extend(args.drain(..).map(TypeOutput::Generic))
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
    }
}

impl Generic {
    fn drain_children(&mut self, pending: &mut Vec<TypeOutput>) {
        match self {
            Generic::Type(ty) | Generic::Const { value: _, ty } => {
                if let Type::Unknown = ty {
                    return;
                }
                pending.push(TypeOutput::Type(std::mem::replace(ty, Type::Unknown)));
            }
            Generic::Lifetime | Generic::Parameter(_) | Generic::Unknown => {}
        }
    }
}

impl TypeOutput {
    fn drop_pending(mut pending: Vec<TypeOutput>) {
        while let Some(mut value) = pending.pop() {
            match &mut value {
                TypeOutput::Type(ty) => ty.drain_children(&mut pending),
                TypeOutput::Generic(arg) => arg.drain_children(&mut pending),
            }
        }
    }
}

impl Drop for Type {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.drain_children(&mut pending);
        TypeOutput::drop_pending(pending);
    }
}
impl Drop for Generic {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.drain_children(&mut pending);
        TypeOutput::drop_pending(pending);
    }
}
impl std::fmt::Debug for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(TypeTokens::new(TypeInput::Type(self)))
            .finish()
    }
}
impl std::fmt::Debug for Generic {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(TypeTokens::new(TypeInput::Generic(self)))
            .finish()
    }
}
