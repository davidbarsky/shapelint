use crate::calls::{Instance, Type};
use crate::contracts::{Arithmetic, Encoding, Interval, Order, Origin};
use rustc_data_structures::fingerprint::Fingerprint;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Local;
use rustc_span::Span;
use std::fmt;
use std::hash::{Hash, Hasher};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Target {
    Direct(Instance),
    Indirect(Box<Expr>),
}

impl Target {
    pub fn definition(&self) -> Option<DefId> {
        match self {
            Self::Direct(Instance {
                def,
                dispatch: crate::calls::Dispatch::Item,
                ..
            }) => Some(*def),
            Self::Direct(_) | Self::Indirect(_) => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Serialized {
    pub value: Expr,
    pub def: DefId,
    pub span: Span,
    pub encoding: Encoding,
    pub ty: Fingerprint,
}

pub enum Expr {
    Serialized(Box<Serialized>),
    Unknown,
    Function(Instance),
    Typed(Type, Box<Expr>),
    Alternatives(Vec<Expr>),
    Select(Box<Condition>, Box<Expr>, Box<Expr>),
    Opaque(Origin),
    Global(Instance),
    Argument(usize),
    Number(u128),
    Range(Interval),
    Text(String),
    Field(Box<Expr>, usize),
    Element(Box<Expr>, Box<Expr>),
    Closure(DefId, Vec<Expr>),
    Aggregate(Vec<Expr>),
    Variant(DefId, usize, Vec<Expr>),
    Length(Box<Expr>),
    Trimmed(Box<Expr>),
    Found {
        text: Box<Expr>,
        pattern: Box<Expr>,
    },
    MatchIndex {
        text: Box<Expr>,
        pattern: Box<Expr>,
        occurrence: Box<Expr>,
    },
    Matches {
        text: Box<Expr>,
        pattern: Box<Expr>,
    },
    MatchEntry(TextMatch<Box<Expr>>),
    Tokens {
        text: Box<Expr>,
        consumed: Box<Expr>,
    },
    Token(Token<Box<Expr>>),
    NextToken(Token<Box<Expr>>),
    Cursor {
        def: DefId,
        local: Local,
    },
    Partition {
        sequence: Box<Expr>,
        predicate: Box<Expr>,
    },
    Slice {
        text: Box<Expr>,
        start: Box<Expr>,
        end: Box<Expr>,
    },
    Arithmetic(Arithmetic, Box<Expr>, Box<Expr>),
    Call(Target, Vec<Expr>, Option<Origin>),
    Test(Box<Condition>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TextMatch<E> {
    pub text: E,
    pub pattern: E,
    pub occurrence: E,
}

impl<E> TextMatch<E> {
    fn map<X>(self, mut map: impl FnMut(E) -> X) -> TextMatch<X> {
        TextMatch {
            text: map(self.text),
            pattern: map(self.pattern),
            occurrence: map(self.occurrence),
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Token<E> {
    pub text: E,
    pub start: E,
    pub length: E,
}

impl<E> Token<E> {
    fn map<X>(self, mut map: impl FnMut(E) -> X) -> Token<X> {
        Token {
            text: map(self.text),
            start: map(self.start),
            length: map(self.length),
        }
    }
}

pub enum Condition {
    Unknown,
    Compare(Order, Expr, Expr),
    Boundary(Expr, Expr),
    NotBoundary(Expr, Expr),
    Variant(Expr, usize),
    NotVariant(Expr, usize),
    Returned(Target, Vec<Expr>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Root<E, C> {
    Expr(E),
    Condition(C),
}

#[derive(Clone, Copy)]
pub enum Input<'a> {
    Expr(&'a Expr),
    Condition(&'a Condition),
}

pub(crate) type Output = Root<Expr, Condition>;

impl<'a> Input<'a> {
    fn hash_keys<H: Hasher>(self, state: &mut H) {
        for key in self.keys() {
            key.hash(state);
        }
    }

    pub(crate) fn children(self) -> Vec<Self> {
        match self {
            Self::Expr(value) => value.children(),
            Self::Condition(value) => value.children(),
        }
    }
}

impl Target {
    fn call_inputs<'a>(&'a self, arguments: &'a [Expr], pending: &mut Vec<Input<'a>>) {
        if let Self::Indirect(value) = self {
            pending.push(Input::Expr(value));
        }
        pending.extend(arguments.iter().map(Input::Expr));
    }

    fn drain_call(&mut self, arguments: &mut Vec<Expr>, pending: &mut Vec<Root<Expr, Condition>>) {
        if let Self::Indirect(value) = self {
            value.take_for_drop(pending);
        }
        pending.extend(arguments.drain(..).map(Root::Expr));
    }
}

impl Expr {
    pub(crate) fn children(&self) -> Vec<Input<'_>> {
        let mut pending = Vec::new();
        match self {
            Self::Serialized(value) => pending.push(Input::Expr(&value.value)),
            Self::Unknown => {}
            Self::Function(_) => {}
            Self::Typed(_, value) => {
                pending.push(Input::Expr(value));
            }
            Self::Alternatives(values) => {
                pending.extend(values.iter().map(|value| Input::Expr(value)));
            }
            Self::Select(condition, yes, no) => {
                pending.push(Input::Condition(condition));
                pending.push(Input::Expr(yes));
                pending.push(Input::Expr(no));
            }
            Self::Opaque(_) => {}
            Self::Global(_) => {}
            Self::Argument(_) => {}
            Self::Number(_) => {}
            Self::Range(_) => {}
            Self::Text(_) => {}
            Self::Field(value, _) => {
                pending.push(Input::Expr(value));
            }
            Self::Element(value, index) => {
                pending.push(Input::Expr(value));
                pending.push(Input::Expr(index));
            }
            Self::Closure(_, values) => {
                pending.extend(values.iter().map(|value| Input::Expr(value)));
            }
            Self::Aggregate(values) => {
                pending.extend(values.iter().map(|value| Input::Expr(value)));
            }
            Self::Variant(_, _, values) => {
                pending.extend(values.iter().map(|value| Input::Expr(value)));
            }
            Self::Length(value) => {
                pending.push(Input::Expr(value));
            }
            Self::Trimmed(value) => {
                pending.push(Input::Expr(value));
            }
            Self::Found { text, pattern } => {
                pending.push(Input::Expr(text));
                pending.push(Input::Expr(pattern));
            }
            Self::MatchIndex {
                text,
                pattern,
                occurrence,
            } => {
                pending.push(Input::Expr(text));
                pending.push(Input::Expr(pattern));
                pending.push(Input::Expr(occurrence));
            }
            Self::Matches { text, pattern } => {
                pending.push(Input::Expr(text));
                pending.push(Input::Expr(pattern));
            }
            Self::MatchEntry(value) => {
                pending.push(Input::Expr(&value.text));
                pending.push(Input::Expr(&value.pattern));
                pending.push(Input::Expr(&value.occurrence));
            }
            Self::Tokens { text, consumed } => {
                pending.push(Input::Expr(text));
                pending.push(Input::Expr(consumed));
            }
            Self::Token(value) => {
                pending.push(Input::Expr(&value.text));
                pending.push(Input::Expr(&value.start));
                pending.push(Input::Expr(&value.length));
            }
            Self::NextToken(value) => {
                pending.push(Input::Expr(&value.text));
                pending.push(Input::Expr(&value.start));
                pending.push(Input::Expr(&value.length));
            }
            Self::Cursor { def: _, local: _ } => {}
            Self::Partition {
                sequence,
                predicate,
            } => {
                pending.push(Input::Expr(sequence));
                pending.push(Input::Expr(predicate));
            }
            Self::Slice { text, start, end } => {
                pending.push(Input::Expr(text));
                pending.push(Input::Expr(start));
                pending.push(Input::Expr(end));
            }
            Self::Arithmetic(_, left, right) => {
                pending.push(Input::Expr(left));
                pending.push(Input::Expr(right));
            }
            Self::Call(target, arguments, _) => {
                target.call_inputs(arguments, &mut pending);
            }
            Self::Test(condition) => {
                pending.push(Input::Condition(condition));
            }
        }
        pending
    }
}
impl Condition {
    pub(crate) fn children(&self) -> Vec<Input<'_>> {
        let mut pending = Vec::new();
        match self {
            Self::Unknown => {}
            Self::Compare(_, left, right) => {
                pending.push(Input::Expr(left));
                pending.push(Input::Expr(right));
            }
            Self::Boundary(text, offset) => {
                pending.push(Input::Expr(text));
                pending.push(Input::Expr(offset));
            }
            Self::NotBoundary(text, offset) => {
                pending.push(Input::Expr(text));
                pending.push(Input::Expr(offset));
            }
            Self::Variant(value, _) | Self::NotVariant(value, _) => {
                pending.push(Input::Expr(value));
            }
            Self::Returned(target, arguments) => {
                target.call_inputs(arguments, &mut pending);
            }
        }
        pending
    }
}

pub(crate) enum Leaf {
    Unknown,
    Function(Instance),
    Global(Instance),
    Opaque(Origin),
    Argument(usize),
    Number(u128),
    Range(Interval),
    Text(String),
    Cursor { def: DefId, local: Local },
}

pub(crate) enum Unary {
    Length,
    Trimmed,
    Typed(Type),
    Field(usize),
    Serialized(DefId, Span, Encoding, Fingerprint),
}

pub(crate) enum Binary {
    Element,
    Found,
    Matches,
    Partition,
    Tokens,
    Arithmetic(Arithmetic),
}

pub(crate) enum Ternary {
    MatchIndex,
    Slice,
}

pub(crate) enum Collection {
    Alternatives,
    Aggregate,
    Closure(DefId),
    Variant(DefId, usize),
}

pub(crate) enum CallTarget<E> {
    Direct(Instance),
    Indirect(E),
}

impl<E> CallTarget<E> {
    fn map<T>(self, f: impl FnOnce(E) -> T) -> CallTarget<T> {
        match self {
            Self::Direct(instance) => CallTarget::Direct(instance),
            Self::Indirect(value) => CallTarget::Indirect(f(value)),
        }
    }
}

impl From<CallTarget<Expr>> for Target {
    fn from(value: CallTarget<Expr>) -> Self {
        match value {
            CallTarget::Direct(instance) => Self::Direct(instance),
            CallTarget::Indirect(value) => Self::Indirect(Box::new(value)),
        }
    }
}

pub(crate) enum ExprBuild<E, C> {
    Value(Leaf),
    One(Unary, E),
    Two(Binary, E, E),
    Three(Ternary, E, E, E),
    MatchEntry(TextMatch<E>),
    Token(Token<E>),
    NextToken(Token<E>),
    Select(C, E, E),
    Test(C),
    List(Collection, Vec<E>),
    Call(CallTarget<E>, Vec<E>, Option<Origin>),
}

pub(crate) enum ConditionBuild<E> {
    Unknown,
    Variant(E, usize),
    NotVariant(E, usize),
    Compare(Order, E, E),
    Boundary(E, E),
    NotBoundary(E, E),
    Returned(CallTarget<E>, Vec<E>),
}

impl<E, C> Root<ExprBuild<E, C>, ConditionBuild<E>> {
    // Both passes visit children in source order, including the callee of an indirect call.
    fn map_children<S, X, Y>(
        self,
        state: &mut S,
        mut expr: impl FnMut(&mut S, E) -> X,
        mut condition: impl FnMut(&mut S, C) -> Y,
        mut list: impl FnMut(&mut S, Vec<E>) -> Vec<X>,
    ) -> Root<ExprBuild<X, Y>, ConditionBuild<X>> {
        match self {
            Self::Expr(form) => Root::Expr(match form {
                ExprBuild::Value(leaf) => ExprBuild::Value(leaf),
                ExprBuild::One(op, value) => ExprBuild::One(op, expr(state, value)),
                ExprBuild::Two(op, a, b) => ExprBuild::Two(op, expr(state, a), expr(state, b)),
                ExprBuild::Three(op, a, b, c) => {
                    ExprBuild::Three(op, expr(state, a), expr(state, b), expr(state, c))
                }
                ExprBuild::MatchEntry(value) => {
                    ExprBuild::MatchEntry(value.map(|child| expr(state, child)))
                }
                ExprBuild::Token(value) => ExprBuild::Token(value.map(|child| expr(state, child))),
                ExprBuild::NextToken(value) => {
                    ExprBuild::NextToken(value.map(|child| expr(state, child)))
                }
                ExprBuild::Select(guard, yes, no) => {
                    ExprBuild::Select(condition(state, guard), expr(state, yes), expr(state, no))
                }
                ExprBuild::Test(guard) => ExprBuild::Test(condition(state, guard)),
                ExprBuild::List(op, items) => ExprBuild::List(op, list(state, items)),
                ExprBuild::Call(target, args, origin) => ExprBuild::Call(
                    target.map(|value| expr(state, value)),
                    list(state, args),
                    origin,
                ),
            }),
            Self::Condition(form) => Root::Condition(match form {
                ConditionBuild::Unknown => ConditionBuild::Unknown,
                ConditionBuild::Variant(value, variant) => {
                    ConditionBuild::Variant(expr(state, value), variant)
                }
                ConditionBuild::NotVariant(value, variant) => {
                    ConditionBuild::NotVariant(expr(state, value), variant)
                }
                ConditionBuild::Compare(order, a, b) => {
                    ConditionBuild::Compare(order, expr(state, a), expr(state, b))
                }
                ConditionBuild::Boundary(text, offset) => {
                    ConditionBuild::Boundary(expr(state, text), expr(state, offset))
                }
                ConditionBuild::NotBoundary(text, offset) => {
                    ConditionBuild::NotBoundary(expr(state, text), expr(state, offset))
                }
                ConditionBuild::Returned(target, args) => ConditionBuild::Returned(
                    target.map(|value| expr(state, value)),
                    list(state, args),
                ),
            }),
        }
    }
}

impl From<ExprBuild<Expr, Condition>> for Expr {
    fn from(form: ExprBuild<Expr, Condition>) -> Self {
        match form {
            ExprBuild::Value(leaf) => match leaf {
                Leaf::Unknown => Self::Unknown,
                Leaf::Function(instance) => Self::Function(instance),
                Leaf::Global(instance) => Self::Global(instance),
                Leaf::Opaque(origin) => Self::Opaque(origin),
                Leaf::Argument(index) => Self::Argument(index),
                Leaf::Number(value) => Self::Number(value),
                Leaf::Range(interval) => Self::Range(interval),
                Leaf::Text(text) => Self::Text(text),
                Leaf::Cursor { def, local } => Self::Cursor { def, local },
            },
            ExprBuild::One(op, value) => match op {
                Unary::Length => Self::Length(Box::new(value)),
                Unary::Trimmed => Self::Trimmed(Box::new(value)),
                Unary::Typed(ty) => Self::Typed(ty, Box::new(value)),
                Unary::Field(field) => Self::Field(Box::new(value), field),
                Unary::Serialized(def, span, encoding, ty) => {
                    Self::Serialized(Box::new(Serialized {
                        value,
                        def,
                        span,
                        encoding,
                        ty,
                    }))
                }
            },
            ExprBuild::Two(op, left, right) => {
                let (left, right) = (Box::new(left), Box::new(right));
                match op {
                    Binary::Element => Self::Element(left, right),
                    Binary::Found => Self::Found {
                        text: left,
                        pattern: right,
                    },
                    Binary::Matches => Self::Matches {
                        text: left,
                        pattern: right,
                    },
                    Binary::Partition => Self::Partition {
                        sequence: left,
                        predicate: right,
                    },
                    Binary::Tokens => Self::Tokens {
                        text: left,
                        consumed: right,
                    },
                    Binary::Arithmetic(op) => Self::Arithmetic(op, left, right),
                }
            }
            ExprBuild::Three(op, first, second, third) => {
                let (first, second, third) = (Box::new(first), Box::new(second), Box::new(third));
                match op {
                    Ternary::MatchIndex => Self::MatchIndex {
                        text: first,
                        pattern: second,
                        occurrence: third,
                    },
                    Ternary::Slice => Self::Slice {
                        text: first,
                        start: second,
                        end: third,
                    },
                }
            }
            ExprBuild::MatchEntry(value) => Self::MatchEntry(value.map(Box::new)),
            ExprBuild::Token(value) => Self::Token(value.map(Box::new)),
            ExprBuild::NextToken(value) => Self::NextToken(value.map(Box::new)),
            ExprBuild::Select(guard, yes, no) => {
                Self::Select(Box::new(guard), Box::new(yes), Box::new(no))
            }
            ExprBuild::Test(guard) => Self::Test(Box::new(guard)),
            ExprBuild::List(collection, children) => match collection {
                Collection::Alternatives => Self::Alternatives(children),
                Collection::Aggregate => Self::Aggregate(children),
                Collection::Closure(def) => Self::Closure(def, children),
                Collection::Variant(def, variant) => Self::Variant(def, variant, children),
            },
            ExprBuild::Call(target, args, origin) => Self::Call(target.into(), args, origin),
        }
    }
}

impl From<ConditionBuild<Expr>> for Condition {
    fn from(form: ConditionBuild<Expr>) -> Self {
        match form {
            ConditionBuild::Unknown => Self::Unknown,
            ConditionBuild::Variant(value, variant) => Self::Variant(value, variant),
            ConditionBuild::NotVariant(value, variant) => Self::NotVariant(value, variant),
            ConditionBuild::Compare(order, a, b) => Self::Compare(order, a, b),
            ConditionBuild::Boundary(text, offset) => Self::Boundary(text, offset),
            ConditionBuild::NotBoundary(text, offset) => Self::NotBoundary(text, offset),
            ConditionBuild::Returned(target, args) => Self::Returned(target.into(), args),
        }
    }
}

impl<E, C> Root<E, C> {
    pub(crate) fn build(
        self,
        expression: impl Fn(E) -> ExprBuild<E, C>,
        condition: impl Fn(C) -> ConditionBuild<E>,
    ) -> Root<Expr, Condition> {
        let mut inputs = vec![self];
        let mut frames = Vec::new();
        let mut expressions = Vec::new();
        let mut conditions = Vec::new();
        while let Some(input) = inputs.pop() {
            let remaining = inputs.len();
            let form = match input {
                Self::Expr(value) => Root::Expr(expression(value)),
                Self::Condition(value) => Root::Condition(condition(value)),
            };
            // Visiting the last operand first leaves the first result on top.
            let form = form.map_children(
                &mut inputs,
                |inputs, value| inputs.push(Self::Expr(value)),
                |inputs, value| inputs.push(Self::Condition(value)),
                |inputs, children| {
                    let count = children.len();
                    inputs.extend(children.into_iter().map(Self::Expr));
                    vec![(); count]
                },
            );
            frames.push((remaining, form));
            while let Some((_, form)) = frames.pop_if(|(remaining, _)| *remaining == inputs.len()) {
                let completed = form.map_children(
                    &mut (&mut expressions, &mut conditions),
                    |(values, _), ()| values.pop().expect("expression child was built"),
                    |(_, guards), ()| guards.pop().expect("condition child was built"),
                    |(values, _), children| {
                        let start = values.len() - children.len();
                        let mut items = if start == 0 {
                            std::mem::take(*values)
                        } else {
                            values.split_off(start)
                        };
                        items.reverse();
                        items
                    },
                );
                match completed {
                    Root::Expr(form) => expressions.push(Expr::from(form)),
                    Root::Condition(form) => conditions.push(Condition::from(form)),
                }
            }
        }
        match (expressions.pop(), conditions.pop()) {
            (Some(expr), None) => Root::Expr(expr),
            (None, Some(condition)) => Root::Condition(condition),
            _ => unreachable!("one result per root"),
        }
    }
}

impl Target {
    fn decompose(&self) -> CallTarget<&Expr> {
        match self {
            Target::Direct(instance) => CallTarget::Direct(instance.clone()),
            Target::Indirect(value) => CallTarget::Indirect(value),
        }
    }
}

impl Expr {
    fn decompose(&self) -> ExprBuild<&Expr, &Condition> {
        match self {
            Expr::Serialized(value) => ExprBuild::One(
                Unary::Serialized(value.def, value.span, value.encoding, value.ty),
                &value.value,
            ),
            Expr::Unknown => ExprBuild::Value(Leaf::Unknown),
            Expr::Function(value) => ExprBuild::Value(Leaf::Function(value.clone())),
            Expr::Global(value) => ExprBuild::Value(Leaf::Global(value.clone())),
            Expr::Opaque(value) => ExprBuild::Value(Leaf::Opaque(value.clone())),
            Expr::Argument(value) => ExprBuild::Value(Leaf::Argument(*value)),
            Expr::Number(value) => ExprBuild::Value(Leaf::Number(*value)),
            Expr::Range(value) => ExprBuild::Value(Leaf::Range(*value)),
            Expr::Text(value) => ExprBuild::Value(Leaf::Text(value.clone())),
            Expr::Cursor { def, local } => ExprBuild::Value(Leaf::Cursor {
                def: *def,
                local: *local,
            }),
            Expr::Typed(ty, value) => ExprBuild::One(Unary::Typed(ty.clone()), value),
            Expr::Field(value, field) => ExprBuild::One(Unary::Field(*field), value),
            Expr::Length(value) => ExprBuild::One(Unary::Length, value),
            Expr::Trimmed(value) => ExprBuild::One(Unary::Trimmed, value),
            Expr::Element(left, right) => ExprBuild::Two(Binary::Element, left, right),
            Expr::Found { text, pattern } => ExprBuild::Two(Binary::Found, text, pattern),
            Expr::Matches { text, pattern } => ExprBuild::Two(Binary::Matches, text, pattern),
            Expr::Partition {
                sequence,
                predicate,
            } => ExprBuild::Two(Binary::Partition, sequence, predicate),
            Expr::Tokens { text, consumed } => ExprBuild::Two(Binary::Tokens, text, consumed),
            Expr::Arithmetic(op, left, right) => {
                ExprBuild::Two(Binary::Arithmetic(*op), left, right)
            }
            Expr::MatchIndex {
                text,
                pattern,
                occurrence,
            } => ExprBuild::Three(Ternary::MatchIndex, text, pattern, occurrence),
            Expr::MatchEntry(value) => ExprBuild::MatchEntry(TextMatch {
                text: &value.text,
                pattern: &value.pattern,
                occurrence: &value.occurrence,
            }),
            Expr::Slice { text, start, end } => ExprBuild::Three(Ternary::Slice, text, start, end),
            Expr::Token(value) => ExprBuild::Token(Token {
                text: &value.text,
                start: &value.start,
                length: &value.length,
            }),
            Expr::NextToken(value) => ExprBuild::NextToken(Token {
                text: &value.text,
                start: &value.start,
                length: &value.length,
            }),
            Expr::Select(guard, yes, no) => ExprBuild::Select(guard, yes, no),
            Expr::Test(condition) => ExprBuild::Test(condition),
            Expr::Aggregate(values) => {
                ExprBuild::List(Collection::Aggregate, values.iter().collect())
            }
            Expr::Closure(def, values) => {
                ExprBuild::List(Collection::Closure(*def), values.iter().collect())
            }
            Expr::Variant(def, variant, values) => {
                ExprBuild::List(Collection::Variant(*def, *variant), values.iter().collect())
            }
            Expr::Alternatives(values) => {
                ExprBuild::List(Collection::Alternatives, values.iter().collect())
            }
            Expr::Call(target, args, origin) => {
                ExprBuild::Call(target.decompose(), args.iter().collect(), origin.clone())
            }
        }
    }
}

impl Condition {
    fn decompose(&self) -> ConditionBuild<&Expr> {
        match self {
            Condition::Unknown => ConditionBuild::Unknown,
            Condition::Compare(order, left, right) => ConditionBuild::Compare(*order, left, right),
            Condition::Boundary(left, right) => ConditionBuild::Boundary(left, right),
            Condition::NotBoundary(left, right) => ConditionBuild::NotBoundary(left, right),
            Condition::Variant(value, index) => ConditionBuild::Variant(value, *index),
            Condition::NotVariant(value, index) => ConditionBuild::NotVariant(value, *index),
            Condition::Returned(target, args) => {
                ConditionBuild::Returned(target.decompose(), args.iter().collect())
            }
        }
    }
}

impl Clone for Expr {
    fn clone(&self) -> Self {
        match Root::Expr(self).build(Expr::decompose, Condition::decompose) {
            Root::Expr(value) => value,
            Root::Condition(_) => unreachable!("expression root"),
        }
    }
}
impl Clone for Condition {
    fn clone(&self) -> Self {
        match Root::Condition(self).build(Expr::decompose, Condition::decompose) {
            Root::Condition(value) => value,
            Root::Expr(_) => unreachable!("condition root"),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
enum Metadata<'a> {
    Def(DefId),
    Span(Span),
    Encoding(Encoding),
    Fingerprint(Fingerprint),
    Origin(&'a Origin),
    OptionalOrigin(&'a Option<Origin>),
    Interval(&'a Interval),
    Text(&'a str),
    Index(usize),
    Number(u128),
    Local(Local),
    Arithmetic(Arithmetic),
    Order(Order),
    Type(&'a Type),
    Instance(&'a Instance),
    Direct,
    Indirect,
}
#[derive(Debug, PartialEq, Eq, Hash)]
struct TokenKey<'a> {
    variant: Root<std::mem::Discriminant<Expr>, std::mem::Discriminant<Condition>>,
    children: usize,
    metadata: Vec<Metadata<'a>>,
}
impl Target {
    fn append_metadata<'a>(&'a self, metadata: &mut Vec<Metadata<'a>>) {
        match self {
            Target::Direct(instance) => {
                metadata.push(Metadata::Direct);
                metadata.push(Metadata::Instance(instance));
            }
            Target::Indirect(_) => metadata.push(Metadata::Indirect),
        }
    }
}
impl<'a> Input<'a> {
    fn key(self, children: usize) -> TokenKey<'a> {
        let mut metadata = Vec::new();
        let variant = match self {
            Self::Expr(value) => {
                match value {
                    Expr::Serialized(value) => {
                        metadata.push(Metadata::Def(value.def));
                        metadata.push(Metadata::Span(value.span));
                        metadata.push(Metadata::Encoding(value.encoding));
                        metadata.push(Metadata::Fingerprint(value.ty));
                    }
                    Expr::Function(instance) | Expr::Global(instance) => {
                        metadata.push(Metadata::Instance(instance))
                    }
                    Expr::Typed(ty, _) => metadata.push(Metadata::Type(ty)),
                    Expr::Opaque(origin) => metadata.push(Metadata::Origin(origin)),
                    Expr::Argument(index) | Expr::Field(_, index) => {
                        metadata.push(Metadata::Index(*index))
                    }
                    Expr::Number(value) => metadata.push(Metadata::Number(*value)),
                    Expr::Range(value) => metadata.push(Metadata::Interval(value)),
                    Expr::Text(value) => metadata.push(Metadata::Text(value)),
                    Expr::Closure(def, _) => metadata.push(Metadata::Def(*def)),
                    Expr::Variant(def, variant, _) => {
                        metadata.push(Metadata::Def(*def));
                        metadata.push(Metadata::Index(*variant));
                    }
                    Expr::Cursor { def, local } => {
                        metadata.push(Metadata::Def(*def));
                        metadata.push(Metadata::Local(*local));
                    }
                    Expr::Arithmetic(op, _, _) => metadata.push(Metadata::Arithmetic(*op)),
                    Expr::Call(target, _, origin) => {
                        target.append_metadata(&mut metadata);
                        metadata.push(Metadata::OptionalOrigin(origin));
                    }
                    Expr::Unknown
                    | Expr::Alternatives(_)
                    | Expr::Select(_, _, _)
                    | Expr::Element(_, _)
                    | Expr::Aggregate(_)
                    | Expr::Length(_)
                    | Expr::Trimmed(_)
                    | Expr::Found { .. }
                    | Expr::MatchIndex { .. }
                    | Expr::Matches { .. }
                    | Expr::MatchEntry(_)
                    | Expr::Tokens { .. }
                    | Expr::Token(_)
                    | Expr::NextToken(_)
                    | Expr::Partition { .. }
                    | Expr::Slice { .. }
                    | Expr::Test(_) => {}
                }
                Root::Expr(std::mem::discriminant(value))
            }
            Self::Condition(value) => {
                match value {
                    Condition::Compare(order, _, _) => metadata.push(Metadata::Order(*order)),
                    Condition::Variant(_, index) | Condition::NotVariant(_, index) => {
                        metadata.push(Metadata::Index(*index))
                    }
                    Condition::Returned(target, _) => target.append_metadata(&mut metadata),
                    Condition::Unknown
                    | Condition::Boundary(_, _)
                    | Condition::NotBoundary(_, _) => {}
                }
                Root::Condition(std::mem::discriminant(value))
            }
        };
        TokenKey {
            variant,
            children,
            metadata,
        }
    }
}
impl<'a> Input<'a> {
    fn keys(self) -> impl Iterator<Item = TokenKey<'a>> {
        let mut pending = vec![self];
        std::iter::from_fn(move || {
            let value = pending.pop()?;
            let children = value.children();
            let key = value.key(children.len());
            pending.extend(children.into_iter().rev());
            Some(key)
        })
    }
}
impl PartialEq for Expr {
    fn eq(&self, other: &Self) -> bool {
        Input::Expr(self).keys().eq(Input::Expr(other).keys())
    }
}
impl Eq for Expr {}
impl Hash for Expr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Input::Expr(self).hash_keys(state);
    }
}
impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(Input::Expr(self).keys()).finish()
    }
}
impl PartialEq for Condition {
    fn eq(&self, other: &Self) -> bool {
        Input::Condition(self)
            .keys()
            .eq(Input::Condition(other).keys())
    }
}
impl Eq for Condition {}
impl Hash for Condition {
    fn hash<H: Hasher>(&self, state: &mut H) {
        Input::Condition(self).hash_keys(state);
    }
}
impl fmt::Debug for Condition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list()
            .entries(Input::Condition(self).keys())
            .finish()
    }
}

impl Expr {
    fn take_for_drop(&mut self, pending: &mut Vec<Root<Expr, Condition>>) {
        if let Expr::Unknown = self {
            return;
        }
        pending.push(Root::Expr(std::mem::replace(self, Expr::Unknown)));
    }
}
impl Condition {
    fn take_for_drop(&mut self, pending: &mut Vec<Root<Expr, Condition>>) {
        if let Condition::Unknown = self {
            return;
        }
        pending.push(Root::Condition(std::mem::replace(self, Condition::Unknown)));
    }
}
impl Expr {
    fn drain_children(&mut self, pending: &mut Vec<Root<Expr, Condition>>) {
        match self {
            Expr::Serialized(value) => value.value.take_for_drop(pending),
            Expr::Typed(_, value)
            | Expr::Field(value, _)
            | Expr::Length(value)
            | Expr::Trimmed(value) => value.take_for_drop(pending),
            Expr::Alternatives(values)
            | Expr::Closure(_, values)
            | Expr::Aggregate(values)
            | Expr::Variant(_, _, values) => pending.extend(values.drain(..).map(Root::Expr)),
            Expr::Select(condition, yes, no) => {
                condition.take_for_drop(pending);
                yes.take_for_drop(pending);
                no.take_for_drop(pending);
            }
            Expr::Element(left, right) | Expr::Arithmetic(_, left, right) => {
                left.take_for_drop(pending);
                right.take_for_drop(pending);
            }
            Expr::Found { text, pattern } | Expr::Matches { text, pattern } => {
                text.take_for_drop(pending);
                pattern.take_for_drop(pending);
            }
            Expr::MatchIndex {
                text,
                pattern,
                occurrence,
            }
            | Expr::MatchEntry(TextMatch {
                text,
                pattern,
                occurrence,
            }) => {
                text.take_for_drop(pending);
                pattern.take_for_drop(pending);
                occurrence.take_for_drop(pending);
            }
            Expr::Tokens { text, consumed } => {
                text.take_for_drop(pending);
                consumed.take_for_drop(pending);
            }
            Expr::Token(Token {
                text,
                start,
                length,
            })
            | Expr::NextToken(Token {
                text,
                start,
                length,
            }) => {
                text.take_for_drop(pending);
                start.take_for_drop(pending);
                length.take_for_drop(pending);
            }
            Expr::Partition {
                sequence,
                predicate,
            } => {
                sequence.take_for_drop(pending);
                predicate.take_for_drop(pending);
            }
            Expr::Slice { text, start, end } => {
                text.take_for_drop(pending);
                start.take_for_drop(pending);
                end.take_for_drop(pending);
            }
            Expr::Call(target, args, _) => {
                target.drain_call(args, pending);
            }
            Expr::Test(condition) => condition.take_for_drop(pending),
            Expr::Unknown
            | Expr::Function(_)
            | Expr::Opaque(_)
            | Expr::Global(_)
            | Expr::Argument(_)
            | Expr::Number(_)
            | Expr::Range(_)
            | Expr::Text(_)
            | Expr::Cursor { .. } => {}
        }
    }
}
impl Condition {
    fn drain_children(&mut self, pending: &mut Vec<Root<Expr, Condition>>) {
        match self {
            Condition::Compare(_, left, right)
            | Condition::Boundary(left, right)
            | Condition::NotBoundary(left, right) => {
                left.take_for_drop(pending);
                right.take_for_drop(pending);
            }
            Condition::Variant(value, _) | Condition::NotVariant(value, _) => {
                value.take_for_drop(pending)
            }
            Condition::Returned(target, args) => {
                target.drain_call(args, pending);
            }
            Condition::Unknown => {}
        }
    }
}
impl Root<Expr, Condition> {
    fn drop_pending(mut pending: Vec<Self>) {
        while let Some(mut value) = pending.pop() {
            match &mut value {
                Root::Expr(value) => value.drain_children(&mut pending),
                Root::Condition(value) => value.drain_children(&mut pending),
            }
        }
    }
}
impl Drop for Expr {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.drain_children(&mut pending);
        Root::drop_pending(pending);
    }
}
impl Drop for Condition {
    fn drop(&mut self) {
        let mut pending = Vec::new();
        self.drain_children(&mut pending);
        Root::drop_pending(pending);
    }
}
