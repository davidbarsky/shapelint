//! Human-readable descriptions of symbolic contract expressions.

use std::fmt;

use rustc_arena::TypedArena;
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, Ty, TyCtxt};

use crate::contracts::graph::{ConditionId, ConditionNode, ExprId, ExprNode, Graph, TextMatchNode};
use crate::contracts::{self, Operation, Order};
use crate::diagnostics::item;

pub enum Description {
    Check {
        unproven: &'static str,
        invalid: &'static str,
        requirement: String,
    },
    Unsupported(String),
}

impl<'g> Condition<'_, '_, 'g> {
    pub fn unsupported<'a>(&self, consumer: &'a contracts::Consumer) -> Option<&'a str> {
        match &consumer.operation {
            Operation::Unsupported(reason) => Some(reason),
            Operation::Subtraction { .. } => None,
            Operation::Condition => match self.graph[self.condition] {
                ConditionNode::Unknown => Some("the asserted condition could not be modeled"),
                ConditionNode::Returned(..) => {
                    Some("the call's return conditions could not be modeled")
                }
                ConditionNode::Compare(..)
                | ConditionNode::Boundary(..)
                | ConditionNode::NotBoundary(..)
                | ConditionNode::Variant(..)
                | ConditionNode::NotVariant(..) => None,
            },
        }
    }

    pub fn describe(
        &self,
        consumer: &contracts::Consumer,
    ) -> Result<Description, crate::contracts::graph::CapacityError> {
        if let Some(reason) = self.unsupported(consumer) {
            return Ok(Description::Unsupported(reason.into()));
        }
        let (unproven, invalid, requirement) = match &consumer.operation {
            Operation::Unsupported(_) => {
                unreachable!("unsupported operation was classified before description")
            }
            Operation::Subtraction { left, right } => {
                let name = |value: &ExprId<'g>, source: &Option<String>| {
                    if let ExprNode::Range(_) = self.graph[*value]
                        && self.def == consumer.def
                        && let Some(source) = source
                    {
                        return Ok(Some(source.clone()));
                    }
                    self.expression(value).map(|value| value.text)
                };
                let names = match &self.graph[self.condition] {
                    ConditionNode::Compare(Order::LessEqual, subtrahend, minuend) => {
                        (name(minuend, left)?, name(subtrahend, right)?)
                    }
                    _ => (None, None),
                };
                let requirement = match names {
                    (Some(left), Some(right)) => format!("requires {left} >= {right}"),
                    (left_name, right_name) => {
                        let (left, right) = match self.def == consumer.def {
                            true => (
                                left_name.or_else(|| left.clone()),
                                right_name.or_else(|| right.clone()),
                            ),
                            false => (left.clone(), right.clone()),
                        };
                        let requirement = match (left, right) {
                            (Some(left), Some(right)) => format!("requires {left} >= {right}"),
                            (Some(left), None) => {
                                format!("requires the subtracted amount to be at most {left}")
                            }
                            (None, Some(right)) => {
                                format!("requires the starting value to be at least {right}")
                            }
                            (None, None) => {
                                "requires the subtracted amount to be at most the starting value"
                                    .into()
                            }
                        };
                        match self.def == consumer.def {
                            true => requirement,
                            false => {
                                format!("in `{}`: {requirement}", item(self.tcx, consumer.def))
                            }
                        }
                    }
                };
                (
                    "could not prove subtraction cannot underflow",
                    "subtraction will underflow",
                    requirement,
                )
            }
            Operation::Condition => {
                let (unproven, invalid) = match &self.graph[self.condition] {
                    ConditionNode::Compare(order, _, right) => match (order, &self.graph[*right]) {
                        (Order::Less | Order::LessEqual, ExprNode::Length(_)) => (
                            "could not prove the index or range is within bounds",
                            "the index or range is out of bounds",
                        ),
                        _ => (
                            "could not prove the required comparison holds",
                            "the required comparison does not hold",
                        ),
                    },
                    ConditionNode::Boundary(..) => (
                        "could not prove the string offset is on a UTF-8 boundary",
                        "the string offset is not on the required UTF-8 boundary",
                    ),
                    ConditionNode::NotBoundary(..) => (
                        "could not prove the string offset is between UTF-8 boundaries",
                        "the string offset is on a forbidden UTF-8 boundary",
                    ),
                    ConditionNode::Variant(..) => (
                        "could not prove the value has the required variant",
                        "the value has the wrong variant for this operation",
                    ),
                    ConditionNode::NotVariant(..) => (
                        "could not prove the value excludes the forbidden variant",
                        "the value has a forbidden variant for this operation",
                    ),
                    ConditionNode::Unknown | ConditionNode::Returned(..) => {
                        unreachable!("unsupported condition was classified before description")
                    }
                };
                (unproven, invalid, self.text()?)
            }
        };
        Ok(Description::Check {
            unproven,
            invalid,
            requirement,
        })
    }
}

pub struct Condition<'a, 'tcx, 'g> {
    pub tcx: TyCtxt<'tcx>,
    pub def: DefId,
    pub condition: ConditionId<'g>,
    pub graph: &'a Graph<'g>,
    pub restorer: &'a std::cell::RefCell<crate::values::Restorer<'tcx, 'g>>,
}

#[derive(Clone, Copy)]
struct Fragment<'f>(&'f Vec<FragmentPart<'f>>);

enum FragmentPart<'f> {
    Text(std::borrow::Cow<'static, str>),
    Shared(Fragment<'f>),
}

impl From<&'static str> for FragmentPart<'_> {
    fn from(text: &'static str) -> Self {
        Self::Text(text.into())
    }
}

impl From<String> for FragmentPart<'_> {
    fn from(text: String) -> Self {
        Self::Text(text.into())
    }
}

impl<'f> From<Fragment<'f>> for FragmentPart<'f> {
    fn from(fragment: Fragment<'f>) -> Self {
        Self::Shared(fragment)
    }
}

struct Fragments<'f> {
    nodes: &'f TypedArena<Vec<FragmentPart<'f>>>,
    available: std::ops::RangeInclusive<u32>,
    overflow: Option<fmt::Error>,
}

impl<'f> Fragments<'f> {
    fn push(&mut self, parts: impl IntoIterator<Item = FragmentPart<'f>>) -> Fragment<'f> {
        if let None = self.available.next() {
            static EMPTY: Vec<FragmentPart<'static>> = Vec::new();
            self.overflow = Some(fmt::Error);
            return Fragment(&EMPTY);
        }
        Fragment(self.nodes.alloc(parts.into_iter().collect()))
    }

    fn write(&self, root: Fragment<'f>, output: &mut impl fmt::Write) -> fmt::Result {
        if let Some(_) = self.overflow {
            return Err(fmt::Error);
        }
        let mut pending = vec![root.0.iter()];
        while let Some(parts) = pending.last_mut() {
            match parts.next() {
                Some(FragmentPart::Text(text)) => output.write_str(text)?,
                Some(FragmentPart::Shared(fragment)) => pending.push(fragment.0.iter()),
                None => {
                    pending.pop();
                }
            }
        }
        Ok(())
    }
}

macro_rules! fragment {
    ($fragments:ident; $($part:expr),+ $(,)?) => {
        $fragments.push([$($part.into()),+])
    };
}

#[derive(Clone)]
struct Expression<'tcx, Text = String> {
    text: Option<Text>,
    ty: Option<Ty<'tcx>>,
}

#[derive(Clone, Copy)]
enum RenderNode<'g> {
    Expr(ExprId<'g>),
    Condition(ConditionId<'g>),
}

struct Rendering<'tcx, 'g, 'f> {
    fragments: Fragments<'f>,
    expressions: FxHashMap<ExprId<'g>, Expression<'tcx, Fragment<'f>>>,
    conditions: FxHashMap<ConditionId<'g>, Fragment<'f>>,
}

impl<'tcx, 'g> Condition<'_, 'tcx, 'g> {
    pub fn text(&self) -> Result<String, crate::contracts::graph::CapacityError> {
        let mut text = String::new();
        std::fmt::write(&mut text, format_args!("{self}"))
            .map_err(|_| crate::contracts::graph::CapacityError::Values)?;
        Ok(text)
    }

    fn expression(
        &self,
        expression: &ExprId<'g>,
    ) -> Result<Expression<'tcx>, crate::contracts::graph::CapacityError> {
        let nodes = TypedArena::default();
        let (fragments, Expression { text, ty }) = self.render(&nodes, |rendering| {
            rendering
                .expressions
                .get(expression)
                .cloned()
                .ok_or(RenderNode::Expr(*expression))
        })?;
        let text = text
            .map(|root| {
                let mut text = String::new();
                fragments
                    .write(root, &mut text)
                    .map_err(|_| crate::contracts::graph::CapacityError::Values)?;
                Ok::<_, crate::contracts::graph::CapacityError>(text)
            })
            .transpose()?;
        Ok(Expression { text, ty })
    }

    fn render<'f, R>(
        &self,
        nodes: &'f TypedArena<Vec<FragmentPart<'f>>>,
        root: impl Fn(&Rendering<'tcx, 'g, 'f>) -> Result<R, RenderNode<'g>>,
    ) -> Result<(Fragments<'f>, R), crate::arena::CapacityError> {
        use crate::memo::{Demand, resolve};
        let mut rendering = Rendering {
            fragments: Fragments {
                nodes,
                available: 0..=u32::MAX,
                overflow: None,
            },
            expressions: FxHashMap::default(),
            conditions: FxHashMap::default(),
        };
        let result = resolve(&mut rendering, root, |rendering, request| {
            match request {
                RenderNode::Expr(id) => {
                    if rendering.expressions.contains_key(&id) {
                        return Ok(());
                    }
                    let node = &self.graph[id];
                    match self.build_expression(
                        node,
                        &mut rendering.fragments,
                        &rendering.expressions,
                        &rendering.conditions,
                    ) {
                        Ok(result) => {
                            rendering.expressions.insert(id, result);
                        }
                        Err(dependency) => {
                            // A wide node can request its outstanding fields together, in source order.
                            let fields = match node {
                                ExprNode::Call(_, fields, _)
                                | ExprNode::Variant(_, _, fields)
                                | ExprNode::Aggregate(fields) => fields,
                                _ => return Err(Demand::Child(dependency)),
                            };
                            let missing = self
                                .graph
                                .items(*fields)
                                .filter(|id| !rendering.expressions.contains_key(*id))
                                .copied()
                                .map(RenderNode::Expr)
                                .collect::<Vec<_>>();
                            return Err(if missing.is_empty() {
                                Demand::Child(dependency)
                            } else {
                                Demand::Children(missing)
                            });
                        }
                    }
                }
                RenderNode::Condition(id) => {
                    if rendering.conditions.contains_key(&id) {
                        return Ok(());
                    }
                    let result = Condition {
                        condition: id,
                        ..*self
                    }
                    .build_condition(&mut rendering.fragments, &rendering.expressions)
                    .map_err(Demand::Child)?;
                    rendering.conditions.insert(id, result);
                }
            }
            Ok(())
        })?;
        Ok((rendering.fragments, result))
    }

    fn build_expression<'f>(
        &self,
        expression: &ExprNode<'g>,
        fragments: &mut Fragments<'f>,
        expressions: &FxHashMap<ExprId<'g>, Expression<'tcx, Fragment<'f>>>,
        conditions: &FxHashMap<ConditionId<'g>, Fragment<'f>>,
    ) -> Result<Expression<'tcx, Fragment<'f>>, RenderNode<'g>> {
        let child = |id: &ExprId<'g>| expressions.get(id).cloned().ok_or(RenderNode::Expr(*id));
        let tcx = self.tcx;
        let (text, ty) = match expression {
            ExprNode::Serialized { .. } => {
                (Some(fragment!(fragments; "the serialized value")), None)
            }
            ExprNode::Element(base, index) => {
                let text = match (child(base)?.text, child(index)?.text) {
                    (Some(base), Some(index)) => Some(fragment!(fragments; base, "[", index, "]")),
                    _ => None,
                };
                (text, None)
            }
            ExprNode::Closure(def, _) => (Some(fragment!(fragments; item(tcx, *def))), None),
            ExprNode::Cursor { .. } => (
                Some(fragment!(fragments; "bytes consumed by the lexer")),
                Some(tcx.types.usize),
            ),
            ExprNode::Tokens { .. } | ExprNode::Token(_) | ExprNode::NextToken(_) => (None, None),

            ExprNode::Argument(index) => {
                let closure = match tcx.def_kind(self.def) {
                    DefKind::Closure | DefKind::SyntheticCoroutineBody => Some(()),
                    _ => None,
                };
                let parameter = match closure {
                    Some(()) => index.checked_sub(1),
                    None => Some(*index),
                };
                let text = self.def.as_local().and_then(|def| {
                    let body = tcx.hir_maybe_body_owned_by(def)?;
                    let parameter = body.params.get(parameter?)?;
                    match parameter.pat.kind {
                        rustc_hir::PatKind::Binding(_, _, name, _) => Some(name.to_string()),
                        _ => Some(rustc_hir_pretty::pat_to_string(
                            &(&tcx as &dyn rustc_hir::intravisit::HirTyCtxt),
                            parameter.pat,
                        )),
                    }
                });
                let text = match (text, closure, parameter) {
                    (Some(text), _, _) => text,
                    (None, Some(()), None) => "captured state".into(),
                    _ => "an unnamed parameter".into(),
                };
                let ty = match tcx.def_kind(self.def) {
                    DefKind::Fn | DefKind::AssocFn => tcx
                        .fn_sig(self.def)
                        .instantiate_identity()
                        .skip_binder()
                        .inputs()
                        .get(*index)
                        .copied(),
                    DefKind::Closure => {
                        let ty = tcx
                            .type_of(self.def)
                            .instantiate_identity()
                            .skip_normalization();
                        match (*ty.kind(), parameter) {
                            (_, None) => Some(ty),
                            (ty::Closure(_, args), Some(parameter)) => {
                                let signature = args.as_closure().sig().skip_binder();
                                match signature.inputs().first().map(|input| input.kind()) {
                                    Some(ty::Tuple(types)) => types.get(parameter).copied(),
                                    _ => None,
                                }
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                };
                (Some(fragment!(fragments; text)), ty)
            }
            ExprNode::Field(base, index) => {
                let base = child(base)?;
                match base.ty.map(|ty| ty.peel_refs()) {
                    Some(ty) => match ty.kind() {
                        ty::Adt(adt, args) if adt.is_struct() => {
                            match adt
                                .non_enum_variant()
                                .fields
                                .get(rustc_abi::FieldIdx::from_usize(*index))
                            {
                                Some(field) => (
                                    base.text.map(|base| fragment!(fragments; base, format!(".{}", field.name))),
                                    Some(field.ty(tcx, args).skip_normalization()),
                                ),
                                None => (base.text.map(|base| fragment!(fragments; "a field of ", base)), None),
                            }
                        }
                        ty::Tuple(types) => (
                            base.text
                                .map(|base| fragment!(fragments; base, format!(".{index}"))),
                            types.get(*index).copied(),
                        ),
                        ty::Closure(def, args) => {
                            let capture = def
                                .as_local()
                                .and_then(|def| tcx.closure_captures(def).get(*index).copied());
                            let text = match capture {
                                Some(capture) => capture.to_string(tcx),
                                None => format!("a captured value in {}", item(tcx, *def)),
                            };
                            (
                                Some(fragment!(fragments; text)),
                                args.as_closure().upvar_tys().get(*index).copied(),
                            )
                        }
                        ty::Adt(..) => (
                            base.text
                                .map(|base| fragment!(fragments; "the payload of ", base)),
                            None,
                        ),
                        _ => (
                            base.text
                                .map(|base| fragment!(fragments; "a field of ", base)),
                            None,
                        ),
                    },
                    None => (
                        base.text
                            .map(|base| fragment!(fragments; "a field of ", base)),
                        None,
                    ),
                }
            }
            ExprNode::Select(condition, yes, no) => {
                let condition = conditions
                    .get(condition)
                    .copied()
                    .ok_or(RenderNode::Condition(*condition))?;
                let text = match (child(yes)?.text, child(no)?.text) {
                    (Some(yes), Some(no)) => Some(
                        fragment!(fragments; "(if ", condition, " { ", yes, " } else { ", no, " })"),
                    ),
                    _ => None,
                };
                (text, None)
            }
            ExprNode::Range(interval) => (
                Some(fragment!(fragments; format!("a value in {interval}"))),
                None,
            ),
            ExprNode::Number(value) => (Some(fragment!(fragments; value.to_string())), None),
            ExprNode::Text(text) => (
                Some(fragment!(fragments; format!("{:?}", &self.graph[*text]))),
                Some(tcx.types.str_),
            ),
            ExprNode::Unknown => (None, None),
            ExprNode::Arithmetic(op, left, right) => {
                let text = match (child(left)?.text, child(right)?.text) {
                    (Some(left), Some(right)) => Some(match op {
                        contracts::Arithmetic::WrappingSubtract(_) => {
                            fragment!(fragments; left, ".wrapping_sub(", right, ")")
                        }
                        contracts::Arithmetic::Add(_) | contracts::Arithmetic::Subtract(_) => {
                            fragment!(fragments; "(", left, format!(" {op} "), right, ")")
                        }
                    }),
                    _ => None,
                };
                (text, None)
            }
            ExprNode::Matches { text, pattern } => {
                let text = match (child(text)?.text, child(pattern)?.text) {
                    (Some(text), Some(pattern)) => {
                        Some(fragment!(fragments; text, ".match_indices(", pattern, ")"))
                    }
                    _ => None,
                };
                (text, None)
            }
            ExprNode::Partition { sequence, .. } => (
                child(sequence)?
                    .text
                    .map(|base| fragment!(fragments; "the partition point in ", base)),
                Some(tcx.types.usize),
            ),
            ExprNode::Trimmed(base) => (
                child(base)?
                    .text
                    .map(|base| fragment!(fragments; base, ".trim_start()")),
                Some(tcx.types.str_),
            ),
            ExprNode::Found { text, pattern } => {
                let text = match (child(text)?.text, child(pattern)?.text) {
                    (Some(text), Some(pattern)) => {
                        Some(fragment!(fragments; text, ".find(", pattern, ")"))
                    }
                    _ => None,
                };
                (text, None)
            }
            ExprNode::MatchIndex { text, pattern, .. }
            | ExprNode::MatchEntry(TextMatchNode { text, pattern, .. }) => {
                let text = match (child(text)?.text, child(pattern)?.text) {
                    (Some(text), Some(pattern)) => {
                        Some(fragment!(fragments; "the position of ", pattern, " in ", text))
                    }
                    _ => None,
                };
                (text, Some(tcx.types.usize))
            }
            ExprNode::Slice { text, start, end } => {
                let text = match (child(text)?.text, child(start)?.text, child(end)?.text) {
                    (Some(text), Some(start), Some(end)) => {
                        Some(fragment!(fragments; text, "[", start, "..", end, "]"))
                    }
                    _ => None,
                };
                (text, None)
            }
            ExprNode::Opaque(origin) => {
                let origin = self.graph[*origin];
                (
                    origin
                        .name
                        .map(|name| fragment!(fragments; self.graph[name].to_owned())),
                    origin
                        .adt
                        .map(|def| tcx.type_of(def).instantiate_identity().skip_normalization()),
                )
            }
            ExprNode::Length(base) => (
                child(base)?
                    .text
                    .map(|base| fragment!(fragments; base, ".len()")),
                Some(tcx.types.usize),
            ),
            ExprNode::Call(target, arguments, _) => {
                let mut parts = Vec::new();
                let name = match target.definition(self.graph) {
                    Some(def) => item(tcx, def),
                    None => "callback".into(),
                };
                parts.push(name.into());
                parts.push("(".into());
                let arguments = self.graph.items(*arguments).enumerate();
                for (index, argument) in arguments {
                    if index != 0 {
                        parts.push(", ".into());
                    }
                    parts.push(match child(argument)?.text {
                        Some(text) => text.into(),
                        None => "unknown".into(),
                    });
                }
                parts.push(")".into());
                let text = fragments.push(parts);
                match target.definition(self.graph) {
                    Some(def) => {
                        let ty = match tcx.def_kind(def) {
                            DefKind::Fn | DefKind::AssocFn => Some(
                                tcx.fn_sig(def)
                                    .instantiate_identity()
                                    .skip_binder()
                                    .output(),
                            ),
                            _ => None,
                        };
                        (Some(text), ty)
                    }
                    None => (Some(text), None),
                }
            }
            ExprNode::Function(instance) | ExprNode::Global(instance) => (
                Some(fragment!(fragments; item(tcx, self.graph[*instance].def))),
                None,
            ),
            ExprNode::Typed(ty, value) => {
                let value = child(value)?;
                (value.text, self.restorer.borrow_mut().restore_type(*ty))
            }
            ExprNode::Alternatives(_) => (None, None),

            ExprNode::Variant(def, variant, fields) => {
                let name =
                    tcx.adt_def(*def).variants()[rustc_abi::VariantIdx::from_usize(*variant)].name;
                let name = format!("{}::{name}", item(tcx, *def));
                let mut parts = vec![name.into()];
                match crate::sequence::Sequences::len(self.graph.as_ref(), *fields) {
                    0 => {}
                    _ => {
                        parts.push("(".into());
                        let fields = self.graph.items(*fields).enumerate();
                        for (index, field) in fields {
                            if index != 0 {
                                parts.push(", ".into());
                            }
                            parts.push(match child(field)?.text {
                                Some(text) => text.into(),
                                None => "unknown".into(),
                            });
                        }
                        parts.push(")".into());
                    }
                }
                let text = fragments.push(parts);
                (
                    Some(text),
                    Some(
                        tcx.type_of(*def)
                            .instantiate_identity()
                            .skip_normalization(),
                    ),
                )
            }
            ExprNode::Aggregate(fields) => {
                let mut parts = vec!["fields (".into()];
                let fields = self.graph.items(*fields).enumerate();
                for (index, field) in fields {
                    if index != 0 {
                        parts.push(", ".into());
                    }
                    parts.push(match child(field)?.text {
                        Some(text) => text.into(),
                        None => "unknown".into(),
                    });
                }
                parts.push(")".into());
                (Some(fragments.push(parts)), None)
            }
            ExprNode::Test(condition) => (
                Some(
                    conditions
                        .get(condition)
                        .copied()
                        .ok_or(RenderNode::Condition(*condition))?,
                ),
                Some(tcx.types.bool),
            ),
        };
        Ok(Expression { text, ty })
    }
}

impl<'tcx, 'g> Condition<'_, 'tcx, 'g> {
    fn build_condition<'f>(
        &self,
        fragments: &mut Fragments<'f>,
        expressions: &FxHashMap<ExprId<'g>, Expression<'tcx, Fragment<'f>>>,
    ) -> Result<Fragment<'f>, RenderNode<'g>> {
        let child = |id: &ExprId<'g>| expressions.get(id).cloned().ok_or(RenderNode::Expr(*id));
        Ok(match &self.graph[self.condition] {
            ConditionNode::Compare(order, left, right) => {
                let left_value = child(left)?;
                let right_value = child(right)?;
                match (left_value.text, right_value.text) {
                    (Some(left_text), Some(right_text)) => {
                        let mut scalar =
                            |expression: &ExprId<'g>, text: Fragment<'f>, other: Option<Ty<'_>>| {
                                match (&self.graph[*expression], other.map(|ty| ty.is_bool())) {
                                    (ExprNode::Number(0), Some(true)) => {
                                        fragment!(fragments; "false")
                                    }
                                    (ExprNode::Number(1), Some(true)) => {
                                        fragment!(fragments; "true")
                                    }
                                    _ => text,
                                }
                            };
                        let left = scalar(left, left_text, right_value.ty);
                        let right = scalar(right, right_text, left_value.ty);
                        fragment!(fragments; left, format!(" {order} "), right)
                    }
                    (Some(name), None) => {
                        fragment!(fragments; "could not prove ", name, format!(" {order} the unknown value"))
                    }
                    (None, Some(name)) => {
                        fragment!(fragments; format!("could not prove the unknown value {order} "), name)
                    }
                    (None, None) => fragment!(fragments; "could not prove the required comparison"),
                }
            }
            ConditionNode::Boundary(text, index) | ConditionNode::NotBoundary(text, index) => {
                let relation = match &self.graph[self.condition] {
                    ConditionNode::NotBoundary(..) => "is not",
                    _ => "is",
                };
                match (child(text)?.text, child(index)?.text) {
                    (Some(text), Some(index)) => {
                        fragment!(fragments; index, format!(" {relation} a UTF-8 boundary in "), text)
                    }
                    (Some(text), None) => {
                        fragment!(fragments; format!("could not prove the offset {relation} a UTF-8 boundary in "), text)
                    }
                    (None, Some(index)) => {
                        fragment!(fragments; "could not prove ", index, format!(" {relation} a UTF-8 boundary"))
                    }
                    (None, None) => {
                        fragment!(fragments; format!("could not prove the offset {relation} a UTF-8 boundary"))
                    }
                }
            }
            ConditionNode::Variant(value, variant) | ConditionNode::NotVariant(value, variant) => {
                let relation = match &self.graph[self.condition] {
                    ConditionNode::NotVariant(_, _) => "must not be",
                    _ => "must be",
                };
                let value = child(value)?;
                let variant = match value.ty.map(|ty| ty.peel_refs()) {
                    Some(ty) => match ty.kind() {
                        ty::Adt(adt, _) => adt
                            .variants()
                            .get(rustc_abi::VariantIdx::from_usize(*variant))
                            .map(|variant| {
                                format!("{}::{}", item(self.tcx, adt.did()), variant.name)
                            }),
                        _ => None,
                    },
                    None => None,
                };
                match (variant, value.text) {
                    (Some(variant), Some(value)) => {
                        fragment!(fragments; value, format!(" {relation} {variant}"))
                    }
                    (Some(variant), None) => {
                        fragment!(fragments; format!("the value {relation} {variant}"))
                    }
                    (None, _) => {
                        fragment!(fragments; "could not determine the required enum variant")
                    }
                }
            }
            ConditionNode::Returned(target, _) => match target.definition(self.graph) {
                Some(def) => fragment!(fragments; item(self.tcx, def), " must return normally"),
                None => fragment!(fragments; "the callback must return normally"),
            },
            ConditionNode::Unknown => {
                fragment!(fragments; "could not determine the required condition")
            }
        })
    }
}
impl fmt::Display for Condition<'_, '_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let nodes = TypedArena::default();
        let (fragments, root) = self
            .render(&nodes, |rendering| {
                rendering
                    .conditions
                    .get(&self.condition)
                    .copied()
                    .ok_or(RenderNode::Condition(self.condition))
            })
            .map_err(|_| fmt::Error)?;
        fragments.write(root, f)
    }
}
