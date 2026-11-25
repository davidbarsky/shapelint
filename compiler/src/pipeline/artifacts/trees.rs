use crate::artifacts::{
    Arithmetic, Decoder, Definition, Dispatch, Encoder, Error, Float, Instance, Integer, Location,
    Mutability, Order, Signed, ValueOrigin,
};
use crate::contracts;
use crate::contracts::graph::{
    AlternativeId, ChoiceId, ChoiceNode, ConditionId, ConditionNode, ExprId, ExprNode, FlowId,
    FlowNodeId, Graph, NodeId, TargetNode, TextMatchNode, TokenNode,
};
use crate::values::{ExportValue, StoreValue};
use crate::{calls, protocols};
use rustc_middle::mir::Local;
use rustc_middle::ty;
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Serialize, Deserialize)]
pub(crate) struct Expression(usize);
#[derive(Clone, Copy, Serialize, Deserialize)]
pub(crate) struct Predicate(usize);
pub(crate) trait NodeReference<'g> {
    type Id: Copy;
    fn graph_node(id: Self::Id) -> NodeId<'g>;
    fn from_index(index: usize) -> Self;
}

impl<'g> NodeReference<'g> for Expression {
    type Id = ExprId<'g>;

    fn graph_node(id: Self::Id) -> NodeId<'g> {
        NodeId::Expr(id)
    }

    fn from_index(index: usize) -> Self {
        Self(index)
    }
}

impl<'g> NodeReference<'g> for Predicate {
    type Id = ConditionId<'g>;

    fn graph_node(id: Self::Id) -> NodeId<'g> {
        NodeId::Condition(id)
    }

    fn from_index(index: usize) -> Self {
        Self(index)
    }
}

#[derive(Clone, Copy, Serialize, Deserialize)]
struct Choice(usize);
#[derive(Serialize, Deserialize)]
enum NodeChoice {
    Value(Expression),
    Branch(Choice, Choice),
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(crate) struct Node {
    kind: Kind,
    expressions: Vec<Expression>,
    conditions: Vec<Predicate>,
}
#[derive(Serialize, Deserialize)]
enum Kind {
    Choice(NodeChoice),
    Expression(ExpressionNode),
    Predicate(PredicateNode),
}
#[derive(Serialize, Deserialize)]
enum NodeTarget {
    Direct(Instance),
    Indirect,
}
#[derive(Serialize, Deserialize)]
enum ExpressionNode {
    Unknown,
    Select,
    Opaque(ValueOrigin),
    Argument(usize),
    Number(u128),
    Range(u128, u128),
    Text(String),
    Field(usize),
    Element,
    Closure(Definition, usize),
    Aggregate(usize),
    Variant(Definition, usize, usize),
    Length,
    Trimmed,
    Found,
    MatchIndex,
    Matches,
    MatchEntry,
    Tokens,
    Token,
    NextToken,
    Cursor { def: Definition, local: usize },
    Partition,
    Slice,
    Arithmetic(Arithmetic),
    Call(NodeTarget, usize, Option<ValueOrigin>),
    Global(Instance),
    Function(Instance),
    Typed(Type),
    Alternatives(Option<Choice>),
    Test,
}
#[derive(Serialize, Deserialize)]
enum PredicateNode {
    Unknown,
    Compare(Order),
    Boundary,
    NotBoundary,
    Variant(usize),
    NotVariant(usize),
    Returned(NodeTarget, usize),
}

impl<'g> Encoder<'_, '_, 'g> {
    fn node_target(&self, value: &TargetNode<'g>) -> NodeTarget {
        match value {
            TargetNode::Direct(instance) => {
                NodeTarget::Direct(self.instance(&self.graph.export_value(*instance)))
            }
            TargetNode::Indirect(_) => NodeTarget::Indirect,
        }
    }
    fn node(&self, value: NodeId<'g>) -> Kind {
        match value {
            NodeId::Choice(value) => {
                let indices = self.node_indices.borrow();
                Kind::Choice(match self.graph[value].node {
                    ChoiceNode::Value(value) => {
                        NodeChoice::Value(Expression(indices[&NodeId::Expr(value)]))
                    }
                    ChoiceNode::Branch(left, right) => NodeChoice::Branch(
                        Choice(indices[&NodeId::Choice(left)]),
                        Choice(indices[&NodeId::Choice(right)]),
                    ),
                })
            }
            NodeId::Expr(value) => Kind::Expression(match &self.graph[value] {
                ExprNode::Serialized { .. } | ExprNode::Unknown => ExpressionNode::Unknown,
                ExprNode::Select(_, _, _) => ExpressionNode::Select,
                ExprNode::Opaque(value) => {
                    ExpressionNode::Opaque(self.origin(&self.graph.export_value(*value)))
                }
                ExprNode::Argument(value) => ExpressionNode::Argument(*value),
                ExprNode::Number(value) => ExpressionNode::Number(*value),
                ExprNode::Range(value) => ExpressionNode::Range(value.lower, value.upper),
                ExprNode::Text(value) => ExpressionNode::Text(self.graph[*value].to_owned()),
                ExprNode::Field(_, index) => ExpressionNode::Field(*index),
                ExprNode::Element(_, _) => ExpressionNode::Element,
                ExprNode::Closure(def, fields) => ExpressionNode::Closure(
                    self.definition(*def),
                    crate::sequence::Sequences::len(self.graph.as_ref(), *fields),
                ),
                ExprNode::Aggregate(fields) => ExpressionNode::Aggregate(
                    crate::sequence::Sequences::len(self.graph.as_ref(), *fields),
                ),
                ExprNode::Variant(def, index, fields) => ExpressionNode::Variant(
                    self.definition(*def),
                    *index,
                    crate::sequence::Sequences::len(self.graph.as_ref(), *fields),
                ),
                ExprNode::Length(_) => ExpressionNode::Length,
                ExprNode::Trimmed(_) => ExpressionNode::Trimmed,
                ExprNode::Found { .. } => ExpressionNode::Found,
                ExprNode::MatchIndex { .. } => ExpressionNode::MatchIndex,
                ExprNode::Matches { .. } => ExpressionNode::Matches,
                ExprNode::MatchEntry(_) => ExpressionNode::MatchEntry,
                ExprNode::Tokens { .. } => ExpressionNode::Tokens,
                ExprNode::Token(_) => ExpressionNode::Token,
                ExprNode::NextToken(_) => ExpressionNode::NextToken,
                ExprNode::Cursor { def, local } => ExpressionNode::Cursor {
                    def: self.definition(*def),
                    local: local.as_usize(),
                },
                ExprNode::Partition { .. } => ExpressionNode::Partition,
                ExprNode::Slice { .. } => ExpressionNode::Slice,
                ExprNode::Arithmetic(op, _, _) => ExpressionNode::Arithmetic(match op {
                    contracts::Arithmetic::Add(ty) => Arithmetic::Add(Integer::from(*ty)),
                    contracts::Arithmetic::Subtract(ty) => Arithmetic::Subtract(Integer::from(*ty)),
                    contracts::Arithmetic::WrappingSubtract(bits) => {
                        Arithmetic::WrappingSubtract(*bits)
                    }
                }),
                ExprNode::Call(target, args, origin) => ExpressionNode::Call(
                    self.node_target(target),
                    crate::sequence::Sequences::len(self.graph.as_ref(), *args),
                    origin.map(|value| self.origin(&self.graph.export_value(value))),
                ),
                ExprNode::Global(value) => {
                    ExpressionNode::Global(self.instance(&self.graph.export_value(*value)))
                }
                ExprNode::Function(value) => {
                    ExpressionNode::Function(self.instance(&self.graph.export_value(*value)))
                }
                ExprNode::Typed(ty, _) => ExpressionNode::Typed(Type(
                    self.type_tokens(calls::TypeKey::from(&self.graph.export_value(*ty))),
                )),
                ExprNode::Alternatives(root) => ExpressionNode::Alternatives(
                    root.map(|root| Choice(self.node_indices.borrow()[&NodeId::Choice(root)])),
                ),
                ExprNode::Test(_) => ExpressionNode::Test,
            }),
            NodeId::Condition(value) => Kind::Predicate(match &self.graph[value] {
                ConditionNode::Unknown => PredicateNode::Unknown,
                ConditionNode::Compare(order, _, _) => PredicateNode::Compare(match order {
                    contracts::Order::Less => Order::Less,
                    contracts::Order::LessEqual => Order::LessEqual,
                    contracts::Order::Equal => Order::Equal,
                    contracts::Order::NotEqual => Order::NotEqual,
                }),
                ConditionNode::Boundary(_, _) => PredicateNode::Boundary,
                ConditionNode::NotBoundary(_, _) => PredicateNode::NotBoundary,
                ConditionNode::Variant(_, index) => PredicateNode::Variant(*index),
                ConditionNode::NotVariant(_, index) => PredicateNode::NotVariant(*index),
                ConditionNode::Returned(target, args) => PredicateNode::Returned(
                    self.node_target(target),
                    crate::sequence::Sequences::len(self.graph.as_ref(), *args),
                ),
            }),
        }
    }
    pub(crate) fn intern<R: NodeReference<'g>>(&self, id: &R::Id) -> R {
        let root = R::graph_node(*id);
        enum Work<'g> {
            Visit(NodeId<'g>),
            Build(NodeId<'g>, Vec<ExprId<'g>>, Vec<ConditionId<'g>>),
        }
        let mut pending = vec![Work::Visit(root)];
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(value) => {
                    if self.node_indices.borrow().contains_key(&value) {
                        continue;
                    }
                    let mut children = Vec::new();
                    match value {
                        NodeId::Expr(id) if let ExprNode::Serialized { .. } = self.graph[id] => {}
                        _ => self
                            .graph
                            .visit_children(value, |child| children.push(child)),
                    }
                    let mut expressions = Vec::new();
                    let mut conditions = Vec::new();
                    match value {
                        NodeId::Choice(_) => {}
                        NodeId::Expr(_) | NodeId::Condition(_) => {
                            for child in &children {
                                match child {
                                    NodeId::Expr(id) => expressions.push(*id),
                                    NodeId::Condition(id) => conditions.push(*id),
                                    NodeId::Choice(_) => {}
                                }
                            }
                        }
                    }
                    // Expression and condition roots retain the previous allocation order.
                    let mut ordered: Vec<_> = children
                        .iter()
                        .copied()
                        .filter(|child| match child {
                            NodeId::Condition(_) => false,
                            NodeId::Expr(_) | NodeId::Choice(_) => true,
                        })
                        .collect();
                    ordered.extend(children.into_iter().filter(|child| match child {
                        NodeId::Condition(_) => true,
                        NodeId::Expr(_) | NodeId::Choice(_) => false,
                    }));
                    let children = ordered;
                    pending.push(Work::Build(value, expressions, conditions));
                    pending.extend(children.into_iter().rev().map(Work::Visit));
                }
                Work::Build(value, expressions, conditions) => {
                    if self.node_indices.borrow().contains_key(&value) {
                        continue;
                    }
                    let indices = self.node_indices.borrow();
                    let expressions = expressions
                        .into_iter()
                        .map(|id| Expression(indices[&NodeId::Expr(id)]))
                        .collect();
                    let conditions = conditions
                        .into_iter()
                        .map(|id| Predicate(indices[&NodeId::Condition(id)]))
                        .collect();
                    drop(indices);
                    let node = Node {
                        kind: self.node(value),
                        expressions,
                        conditions,
                    };
                    let mut nodes = self.nodes.borrow_mut();
                    let index = nodes.len();
                    nodes.push(node);
                    self.node_indices.borrow_mut().insert(value, index);
                }
            }
        }
        R::from_index(self.node_indices.borrow()[&root])
    }
}
impl<'g> Decoder<'_, 'g> {
    fn node_target(
        &self,
        target: NodeTarget,
        graph: &mut Graph<'g>,
        expression: &mut impl FnMut() -> Result<ExprId<'g>, Error>,
    ) -> Result<TargetNode<'g>, Error> {
        Ok(match target {
            NodeTarget::Direct(instance) => {
                TargetNode::Direct(graph.intern_value(&self.instance(instance)?)?)
            }
            NodeTarget::Indirect => TargetNode::Indirect(expression()?),
        })
    }
    pub(crate) fn decode_nodes(
        &mut self,
        nodes: Vec<Node>,
        graph: &mut Graph<'g>,
    ) -> Result<(), Error> {
        for Node {
            kind,
            expressions,
            conditions,
        } in nodes
        {
            let mut expressions = expressions
                .into_iter()
                .map(|value| self.expression(value))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter();
            let mut conditions = conditions
                .into_iter()
                .map(|value| self.predicate(value))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter();
            let mut expression = || {
                expressions.next().ok_or_else(|| {
                    Error::Incompatible("summary expression has a missing child".into())
                })
            };
            let mut predicate = || {
                conditions.next().ok_or_else(|| {
                    Error::Incompatible("summary condition has a missing child".into())
                })
            };
            let value = match kind {
                Kind::Choice(node) => {
                    let node = match node {
                        NodeChoice::Value(value) => ChoiceNode::Value(self.expression(value)?),
                        NodeChoice::Branch(left, right) => {
                            ChoiceNode::Branch(self.choice(left)?, self.choice(right)?)
                        }
                    };
                    let root = graph.intern_choice(node)?.ok_or_else(|| {
                        Error::Incompatible("summary choice has no members".into())
                    })?;
                    NodeId::Choice(root)
                }

                Kind::Expression(node) => {
                    let node = match node {
                        ExpressionNode::Unknown => ExprNode::Unknown,
                        ExpressionNode::Select => {
                            ExprNode::Select(predicate()?, expression()?, expression()?)
                        }
                        ExpressionNode::Opaque(value) => {
                            ExprNode::Opaque(graph.intern_value(&self.origin(value)?)?)
                        }
                        ExpressionNode::Argument(index) => ExprNode::Argument(index),
                        ExpressionNode::Number(value) => ExprNode::Number(value),
                        ExpressionNode::Range(lower, upper) => {
                            if lower > upper {
                                return Err(Error::Incompatible(
                                    "summary interval is reversed".into(),
                                ));
                            }
                            ExprNode::Range(contracts::Interval { lower, upper })
                        }
                        ExpressionNode::Text(value) => {
                            ExprNode::Text(graph.intern_value(value.as_str())?)
                        }
                        ExpressionNode::Field(index) => ExprNode::Field(expression()?, index),
                        ExpressionNode::Element => ExprNode::Element(expression()?, expression()?),
                        ExpressionNode::Closure(def, count) => ExprNode::Closure(
                            self.definition(def)?,
                            crate::sequence::Sequences::from_iter(
                                graph.as_mut(),
                                (0..count)
                                    .map(|_| expression())
                                    .collect::<Result<Vec<_>, _>>()?,
                            )?,
                        ),
                        ExpressionNode::Aggregate(count) => {
                            ExprNode::Aggregate(crate::sequence::Sequences::from_iter(
                                graph.as_mut(),
                                (0..count)
                                    .map(|_| expression())
                                    .collect::<Result<Vec<_>, _>>()?,
                            )?)
                        }
                        ExpressionNode::Variant(def, index, count) => ExprNode::Variant(
                            self.definition(def)?,
                            index,
                            crate::sequence::Sequences::from_iter(
                                graph.as_mut(),
                                (0..count)
                                    .map(|_| expression())
                                    .collect::<Result<Vec<_>, _>>()?,
                            )?,
                        ),
                        ExpressionNode::Length => ExprNode::Length(expression()?),
                        ExpressionNode::Trimmed => ExprNode::Trimmed(expression()?),
                        ExpressionNode::Found => ExprNode::Found {
                            text: expression()?,
                            pattern: expression()?,
                        },
                        ExpressionNode::MatchIndex => ExprNode::MatchIndex {
                            text: expression()?,
                            pattern: expression()?,
                            occurrence: expression()?,
                        },
                        ExpressionNode::Matches => ExprNode::Matches {
                            text: expression()?,
                            pattern: expression()?,
                        },
                        ExpressionNode::MatchEntry => ExprNode::MatchEntry(TextMatchNode {
                            text: expression()?,
                            pattern: expression()?,
                            occurrence: expression()?,
                        }),
                        ExpressionNode::Tokens => ExprNode::Tokens {
                            text: expression()?,
                            consumed: expression()?,
                        },
                        ExpressionNode::Token => ExprNode::Token(TokenNode {
                            text: expression()?,
                            start: expression()?,
                            length: expression()?,
                        }),
                        ExpressionNode::NextToken => ExprNode::NextToken(TokenNode {
                            text: expression()?,
                            start: expression()?,
                            length: expression()?,
                        }),
                        ExpressionNode::Cursor { def, local } => ExprNode::Cursor {
                            def: self.definition(def)?,
                            local: Local::from_usize(local),
                        },
                        ExpressionNode::Partition => ExprNode::Partition {
                            sequence: expression()?,
                            predicate: expression()?,
                        },
                        ExpressionNode::Slice => ExprNode::Slice {
                            text: expression()?,
                            start: expression()?,
                            end: expression()?,
                        },
                        ExpressionNode::Arithmetic(op) => ExprNode::Arithmetic(
                            match op {
                                Arithmetic::Add(ty) => contracts::Arithmetic::Add(ty.into()),
                                Arithmetic::Subtract(ty) => {
                                    contracts::Arithmetic::Subtract(ty.into())
                                }
                                Arithmetic::WrappingSubtract(bits) => {
                                    contracts::Arithmetic::WrappingSubtract(bits)
                                }
                            },
                            expression()?,
                            expression()?,
                        ),
                        ExpressionNode::Call(target, count, origin) => ExprNode::Call(
                            self.node_target(target, graph, &mut expression)?,
                            crate::sequence::Sequences::from_iter(
                                graph.as_mut(),
                                (0..count)
                                    .map(|_| expression())
                                    .collect::<Result<Vec<_>, _>>()?,
                            )?,
                            origin
                                .map(|value| {
                                    self.origin(value)
                                        .and_then(|value| Ok(graph.intern_value(&value)?))
                                })
                                .transpose()?,
                        ),
                        ExpressionNode::Global(value) => {
                            ExprNode::Global(graph.intern_value(&self.instance(value)?)?)
                        }
                        ExpressionNode::Function(value) => {
                            ExprNode::Function(graph.intern_value(&self.instance(value)?)?)
                        }
                        ExpressionNode::Typed(ty) => {
                            ExprNode::Typed(graph.intern_value(&self.ty(ty)?)?, expression()?)
                        }
                        ExpressionNode::Alternatives(root) => {
                            ExprNode::Alternatives(root.map(|root| self.choice(root)).transpose()?)
                        }
                        ExpressionNode::Test => ExprNode::Test(predicate()?),
                    };
                    NodeId::Expr(graph.intern_expr(node)?)
                }
                Kind::Predicate(node) => {
                    let node = match node {
                        PredicateNode::Unknown => ConditionNode::Unknown,
                        PredicateNode::Compare(order) => ConditionNode::Compare(
                            match order {
                                Order::Less => contracts::Order::Less,
                                Order::LessEqual => contracts::Order::LessEqual,
                                Order::Equal => contracts::Order::Equal,
                                Order::NotEqual => contracts::Order::NotEqual,
                            },
                            expression()?,
                            expression()?,
                        ),
                        PredicateNode::Boundary => {
                            ConditionNode::Boundary(expression()?, expression()?)
                        }
                        PredicateNode::NotBoundary => {
                            ConditionNode::NotBoundary(expression()?, expression()?)
                        }
                        PredicateNode::Variant(index) => {
                            ConditionNode::Variant(expression()?, index)
                        }
                        PredicateNode::NotVariant(index) => {
                            ConditionNode::NotVariant(expression()?, index)
                        }
                        PredicateNode::Returned(target, count) => ConditionNode::Returned(
                            self.node_target(target, graph, &mut expression)?,
                            crate::sequence::Sequences::from_iter(
                                graph.as_mut(),
                                (0..count)
                                    .map(|_| expression())
                                    .collect::<Result<Vec<_>, _>>()?,
                            )?,
                        ),
                    };
                    NodeId::Condition(graph.intern_condition(node)?)
                }
            };
            match (expressions.next(), conditions.next()) {
                (None, None) => {}
                _ => {
                    return Err(Error::Incompatible(
                        "summary graph node has extra children".into(),
                    ));
                }
            }
            self.nodes.push(value);
        }
        Ok(())
    }
}
#[derive(Serialize, Deserialize)]
pub(crate) struct Type(Vec<TypeToken>);
#[derive(Serialize, Deserialize)]
pub(crate) struct Generic(Vec<TypeToken>);
#[derive(Serialize, Deserialize)]
enum TypeToken {
    Unknown,
    Parameter(u32),
    Bool,
    Char,
    Int(Signed),
    Uint(Integer),
    Float(Float),
    Str,
    Never,
    Slice,
    Array,
    Tuple(usize),
    Ref(Mutability),
    RawPtr(Mutability),
    Adt(Definition, usize),
    Function(Definition, usize),
    Closure(Definition, usize),
    Lifetime,
    GenericType,
    Const(u128),
    GenericParameter(u32),
    GenericUnknown,
}
impl<'g> Encoder<'_, '_, 'g> {
    pub(crate) fn instance(&self, instance: &calls::Instance) -> Instance {
        Instance {
            def: self.definition(instance.def),
            args: instance
                .args
                .iter()
                .map(|argument| Generic(self.type_tokens(calls::TypeKey::from(argument))))
                .collect(),
            dispatch: match instance.dispatch {
                calls::Dispatch::Item => Dispatch::Item,
                calls::Dispatch::Virtual => Dispatch::Virtual,
                calls::Dispatch::Shim => Dispatch::Shim,
                calls::Dispatch::Unresolved => Dispatch::Unresolved,
            },
        }
    }

    fn type_tokens(&self, value: calls::TypeKey) -> Vec<TypeToken> {
        let mutable = |value: &rustc_hir::Mutability| match value {
            rustc_hir::Mutability::Not => Mutability::Shared,
            rustc_hir::Mutability::Mut => Mutability::Mutable,
        };
        (&value)
            .into_iter()
            .map(|token| match token {
                calls::TypeToken::Unknown => TypeToken::Unknown,
                calls::TypeToken::Parameter(index) => TypeToken::Parameter(*index),
                calls::TypeToken::Bool => TypeToken::Bool,
                calls::TypeToken::Char => TypeToken::Char,
                calls::TypeToken::Int(value) => TypeToken::Int(match value {
                    ty::IntTy::I8 => Signed::I8,
                    ty::IntTy::I16 => Signed::I16,
                    ty::IntTy::I32 => Signed::I32,
                    ty::IntTy::I64 => Signed::I64,
                    ty::IntTy::I128 => Signed::I128,
                    ty::IntTy::Isize => Signed::Isize,
                }),
                calls::TypeToken::Uint(value) => TypeToken::Uint(Integer::from(*value)),
                calls::TypeToken::Float(value) => TypeToken::Float(match value {
                    ty::FloatTy::F16 => Float::F16,
                    ty::FloatTy::F32 => Float::F32,
                    ty::FloatTy::F64 => Float::F64,
                    ty::FloatTy::F128 => Float::F128,
                }),
                calls::TypeToken::Str => TypeToken::Str,
                calls::TypeToken::Never => TypeToken::Never,
                calls::TypeToken::Slice => TypeToken::Slice,
                calls::TypeToken::Array => TypeToken::Array,
                calls::TypeToken::Tuple(count) => TypeToken::Tuple(*count),
                calls::TypeToken::Ref(value) => TypeToken::Ref(mutable(value)),
                calls::TypeToken::RawPtr(value) => TypeToken::RawPtr(mutable(value)),
                calls::TypeToken::Adt(def, count) => TypeToken::Adt(self.definition(*def), *count),
                calls::TypeToken::Function(def, count) => {
                    TypeToken::Function(self.definition(*def), *count)
                }
                calls::TypeToken::Closure(def, count) => {
                    TypeToken::Closure(self.definition(*def), *count)
                }
                calls::TypeToken::Lifetime => TypeToken::Lifetime,
                calls::TypeToken::GenericType => TypeToken::GenericType,
                calls::TypeToken::Const(value) => TypeToken::Const(*value),
                calls::TypeToken::GenericParameter(index) => TypeToken::GenericParameter(*index),
                calls::TypeToken::GenericUnknown => TypeToken::GenericUnknown,
            })
            .collect()
    }
}
impl<'g> Decoder<'_, 'g> {
    fn type_tokens(&self, tokens: Vec<TypeToken>) -> Result<calls::TypeKey, Error> {
        let mutable = |value| match value {
            Mutability::Shared => rustc_hir::Mutability::Not,
            Mutability::Mutable => rustc_hir::Mutability::Mut,
        };
        let tokens = tokens
            .into_iter()
            .map(|token| {
                Ok(match token {
                    TypeToken::Unknown => calls::TypeToken::Unknown,
                    TypeToken::Parameter(index) => calls::TypeToken::Parameter(index),
                    TypeToken::Bool => calls::TypeToken::Bool,
                    TypeToken::Char => calls::TypeToken::Char,
                    TypeToken::Int(value) => calls::TypeToken::Int(match value {
                        Signed::I8 => ty::IntTy::I8,
                        Signed::I16 => ty::IntTy::I16,
                        Signed::I32 => ty::IntTy::I32,
                        Signed::I64 => ty::IntTy::I64,
                        Signed::I128 => ty::IntTy::I128,
                        Signed::Isize => ty::IntTy::Isize,
                    }),
                    TypeToken::Uint(value) => calls::TypeToken::Uint(value.into()),
                    TypeToken::Float(value) => calls::TypeToken::Float(match value {
                        Float::F16 => ty::FloatTy::F16,
                        Float::F32 => ty::FloatTy::F32,
                        Float::F64 => ty::FloatTy::F64,
                        Float::F128 => ty::FloatTy::F128,
                    }),
                    TypeToken::Str => calls::TypeToken::Str,
                    TypeToken::Never => calls::TypeToken::Never,
                    TypeToken::Slice => calls::TypeToken::Slice,
                    TypeToken::Array => calls::TypeToken::Array,
                    TypeToken::Tuple(count) => calls::TypeToken::Tuple(count),
                    TypeToken::Ref(value) => calls::TypeToken::Ref(mutable(value)),
                    TypeToken::RawPtr(value) => calls::TypeToken::RawPtr(mutable(value)),
                    TypeToken::Adt(def, count) => {
                        calls::TypeToken::Adt(self.definition(def)?, count)
                    }
                    TypeToken::Function(def, count) => {
                        calls::TypeToken::Function(self.definition(def)?, count)
                    }
                    TypeToken::Closure(def, count) => {
                        calls::TypeToken::Closure(self.definition(def)?, count)
                    }
                    TypeToken::Lifetime => calls::TypeToken::Lifetime,
                    TypeToken::GenericType => calls::TypeToken::GenericType,
                    TypeToken::Const(value) => calls::TypeToken::Const(value),
                    TypeToken::GenericParameter(index) => calls::TypeToken::GenericParameter(index),
                    TypeToken::GenericUnknown => calls::TypeToken::GenericUnknown,
                })
            })
            .collect::<Result<Vec<_>, Error>>()?;
        Ok(calls::TypeKey::try_from(tokens)?)
    }
}

#[derive(Clone, Copy, Serialize, Deserialize)]
pub(crate) struct Flow(usize);

#[derive(Clone, Copy, Serialize, Deserialize)]
pub(crate) struct Alternative(usize);

#[derive(Serialize, Deserialize)]
pub(crate) enum FlowNode {
    Incoming,
    Unknown,
    Ready,
    Dirty {
        def: Definition,
        location: Location,
    },
    Call {
        callee: Definition,
        argument: usize,
        input: Flow,
    },
    Alternatives(Option<Alternative>),
    Alternative {
        previous: Option<Alternative>,
        value: Flow,
    },
    Select(Predicate, Flow, Flow),
}

impl<'g> Encoder<'_, '_, 'g> {
    pub(crate) fn flow(&self, root: &FlowId<'g>) -> Result<Flow, Error> {
        enum Work<'g> {
            Visit(FlowNodeId<'g>),
            Build(FlowNodeId<'g>),
        }
        let root = FlowNodeId::Flow(*root);
        let mut pending = vec![Work::Visit(root)];
        while let Some(work) = pending.pop() {
            match work {
                Work::Visit(id) => {
                    if self.flow_indices.borrow().contains_key(&id) {
                        continue;
                    }
                    pending.push(Work::Build(id));
                    match id {
                        FlowNodeId::Flow(id) => match self.graph[id] {
                            protocols::Flow::Call { input, .. } => {
                                pending.push(Work::Visit(FlowNodeId::Flow(input)))
                            }
                            protocols::Flow::Alternatives(sequence) => {
                                if let Some(sequence) = sequence {
                                    pending.push(Work::Visit(FlowNodeId::Alternative(sequence)));
                                }
                            }
                            protocols::Flow::Select(_, yes, no) => {
                                pending.push(Work::Visit(FlowNodeId::Flow(no)));
                                pending.push(Work::Visit(FlowNodeId::Flow(yes)));
                            }
                            protocols::Flow::Incoming
                            | protocols::Flow::Unknown
                            | protocols::Flow::Ready
                            | protocols::Flow::Dirty { .. } => {}
                        },
                        FlowNodeId::Alternative(id) => {
                            pending.push(Work::Visit(FlowNodeId::Flow(self.graph[id].value)));
                            if let Some(previous) = self.graph[id].previous {
                                pending.push(Work::Visit(FlowNodeId::Alternative(previous)));
                            }
                        }
                    }
                }
                Work::Build(id) => {
                    if self.flow_indices.borrow().contains_key(&id) {
                        continue;
                    }
                    let flow = |id| Flow(self.flow_indices.borrow()[&FlowNodeId::Flow(id)]);
                    let alternative =
                        |id| Alternative(self.flow_indices.borrow()[&FlowNodeId::Alternative(id)]);
                    let node = match id {
                        FlowNodeId::Flow(id) => match &self.graph[id] {
                            protocols::Flow::Incoming => FlowNode::Incoming,
                            protocols::Flow::Unknown => FlowNode::Unknown,
                            protocols::Flow::Ready => FlowNode::Ready,
                            protocols::Flow::Dirty { def, span } => FlowNode::Dirty {
                                def: self.definition(*def),
                                location: self.location(*def, *span)?,
                            },
                            protocols::Flow::Call {
                                callee,
                                argument,
                                input,
                            } => FlowNode::Call {
                                callee: self.definition(*callee),
                                argument: *argument,
                                input: flow(*input),
                            },
                            protocols::Flow::Alternatives(sequence) => {
                                FlowNode::Alternatives(sequence.map(alternative))
                            }
                            protocols::Flow::Select(condition, yes, no) => FlowNode::Select(
                                self.intern::<Predicate>(condition),
                                flow(*yes),
                                flow(*no),
                            ),
                        },
                        FlowNodeId::Alternative(id) => FlowNode::Alternative {
                            previous: self.graph[id].previous.map(alternative),
                            value: flow(self.graph[id].value),
                        },
                    };
                    let mut flows = self.flows.borrow_mut();
                    self.flow_indices.borrow_mut().insert(id, flows.len());
                    flows.push(node);
                }
            }
        }
        Ok(Flow(self.flow_indices.borrow()[&root]))
    }
}

impl<'g> Decoder<'_, 'g> {
    pub(crate) fn flow(&self, flow: Flow) -> Result<FlowId<'g>, Error> {
        match self.flows.get(flow.0) {
            Some(FlowNodeId::Flow(id)) => Ok(*id),
            Some(FlowNodeId::Alternative(_)) => Err(Error::Incompatible(
                "summary flow reference names an alternative sequence".into(),
            )),
            None => Err(Error::Incompatible(
                "summary flow reference is missing or forward".into(),
            )),
        }
    }

    fn alternative(&self, alternative: Alternative) -> Result<AlternativeId<'g>, Error> {
        match self.flows.get(alternative.0) {
            Some(FlowNodeId::Alternative(id)) => Ok(*id),
            Some(FlowNodeId::Flow(_)) => Err(Error::Incompatible(
                "summary alternative reference names a flow".into(),
            )),
            None => Err(Error::Incompatible(
                "summary alternative reference is missing or forward".into(),
            )),
        }
    }

    pub(crate) fn decode_flows(
        &mut self,
        nodes: Vec<FlowNode>,
        graph: &mut Graph<'g>,
    ) -> Result<(), Error> {
        for node in nodes {
            let node = match node {
                FlowNode::Alternative { previous, value } => {
                    let previous = previous.map(|id| self.alternative(id)).transpose()?;
                    let id = graph.intern_alternative(previous, self.flow(value)?)?;
                    self.flows.push(FlowNodeId::Alternative(id));
                    continue;
                }
                FlowNode::Incoming => protocols::Flow::Incoming,
                FlowNode::Unknown => protocols::Flow::Unknown,
                FlowNode::Ready => protocols::Flow::Ready,
                FlowNode::Dirty { def, location } => protocols::Flow::Dirty {
                    def: self.definition(def)?,
                    span: self.location(location)?,
                },
                FlowNode::Call {
                    callee,
                    argument,
                    input,
                } => protocols::Flow::Call {
                    callee: self.definition(callee)?,
                    argument,
                    input: self.flow(input)?,
                },
                FlowNode::Alternatives(sequence) => protocols::Flow::Alternatives(
                    sequence.map(|id| self.alternative(id)).transpose()?,
                ),
                FlowNode::Select(condition, yes, no) => protocols::Flow::Select(
                    self.predicate(condition)?,
                    self.flow(yes)?,
                    self.flow(no)?,
                ),
            };
            self.flows.push(FlowNodeId::Flow(graph.intern_flow(node)?));
        }
        Ok(())
    }
}

impl<'g> Decoder<'_, 'g> {
    pub(crate) fn expression(&self, value: Expression) -> Result<ExprId<'g>, Error> {
        match self.nodes.get(value.0) {
            Some(NodeId::Expr(value)) => Ok(*value),
            Some(NodeId::Condition(_) | NodeId::Choice(_)) => Err(Error::Incompatible(
                "summary expression reference names a condition".into(),
            )),
            None => Err(Error::Incompatible(
                "summary expression reference is missing or forward".into(),
            )),
        }
    }

    pub(crate) fn predicate(&self, value: Predicate) -> Result<ConditionId<'g>, Error> {
        match self.nodes.get(value.0) {
            Some(NodeId::Condition(value)) => Ok(*value),
            Some(NodeId::Expr(_) | NodeId::Choice(_)) => Err(Error::Incompatible(
                "summary condition reference names an expression".into(),
            )),
            None => Err(Error::Incompatible(
                "summary condition reference is missing or forward".into(),
            )),
        }
    }

    fn choice(&self, value: Choice) -> Result<ChoiceId<'g>, Error> {
        match self.nodes.get(value.0) {
            Some(NodeId::Choice(value)) => Ok(*value),
            Some(NodeId::Expr(_) | NodeId::Condition(_)) => Err(Error::Incompatible(
                "summary choice reference names another node kind".into(),
            )),
            None => Err(Error::Incompatible(
                "summary choice reference is missing or forward".into(),
            )),
        }
    }

    fn ty(&self, Type(tokens): Type) -> Result<calls::Type, Error> {
        match calls::TypeOutput::from(self.type_tokens(tokens)?) {
            calls::TypeOutput::Type(ty) => Ok(ty),
            calls::TypeOutput::Generic(_) => Err(Error::Incompatible(
                "summary type has a generic argument root".into(),
            )),
        }
    }

    pub(crate) fn generic(&self, Generic(tokens): Generic) -> Result<calls::Generic, Error> {
        match calls::TypeOutput::from(self.type_tokens(tokens)?) {
            calls::TypeOutput::Generic(argument) => Ok(argument),
            calls::TypeOutput::Type(_) => Err(Error::Incompatible(
                "summary generic argument has a type root".into(),
            )),
        }
    }
}
