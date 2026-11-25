use rustc_hir::def::{CtorOf, DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Expr, ExprKind, HirId, Node, PatKind, QPath, StmtKind, UnOp};
use rustc_middle::ty::{self, TyCtxt, TypeckResults};
use rustc_span::{Span, Symbol};
use shapelint::CompilerEvidence;

use crate::Located;
use crate::standard::{self, OptionOrResult};

pub fn findings(tcx: TyCtxt<'_>) -> Vec<Located> {
    let mut findings = Vec::new();
    for def in tcx.hir_body_owners() {
        let root = tcx.typeck_root_def_id(def.to_def_id());
        let mut visitor = Expressions {
            tcx,
            typeck: tcx.typeck(root.expect_local()),
            def,
            findings: &mut findings,
        };
        visitor.visit_body(tcx.hir_body_owned_by(def));
    }
    findings
}

struct Expressions<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    def: LocalDefId,
    findings: &'a mut Vec<Located>,
}

struct Call<'hir> {
    owner: OptionOrResult,
    method: Symbol,
    span: Span,
    receiver: &'hir Expr<'hir>,
    arguments: &'hir [Expr<'hir>],
}

impl<'tcx> Expressions<'tcx, '_> {
    fn call(&self, expression: &'tcx Expr<'tcx>) -> Option<Call<'tcx>> {
        let expression = expression.peel_drop_temps();
        let ((def, span), receiver, arguments) = match expression.kind {
            ExprKind::MethodCall(segment, receiver, arguments, _) => (
                (
                    self.typeck.type_dependent_def_id(expression.hir_id)?,
                    segment.ident.span,
                ),
                receiver,
                arguments,
            ),
            ExprKind::Call(callee, [receiver, arguments @ ..]) => {
                let ExprKind::Path(ref path) = callee.kind else {
                    return None;
                };
                let Res::Def(_, def) = self.typeck.qpath_res(path, callee.hir_id) else {
                    return None;
                };
                let span = match path {
                    QPath::Resolved(_, path) => path.segments.last()?.ident.span,
                    QPath::TypeRelative(_, segment) => segment.ident.span,
                };
                ((def, span), receiver, arguments)
            }
            _ => return None,
        };
        if span.from_expansion() || expression.span.from_expansion() {
            return None;
        }
        let call = Call {
            owner: standard::method_owner(self.tcx, def)?,
            method: self.tcx.item_name(def),
            span,
            receiver,
            arguments,
        };
        Some(call)
    }

    fn local(&self, expression: &Expr<'_>) -> Option<HirId> {
        let expression = expression.peel_borrows();
        let ExprKind::Path(ref path) = expression.kind else {
            return None;
        };
        let Res::Local(id) = self.typeck.qpath_res(path, expression.hir_id) else {
            return None;
        };
        Some(id)
    }

    fn guarded_extraction(
        &self,
        condition: &'tcx Expr<'tcx>,
        yes: &'tcx Expr<'tcx>,
        no: Option<&'tcx Expr<'tcx>>,
    ) -> Option<(Span, CompilerEvidence)> {
        let condition = condition.peel_drop_temps();
        let (condition, yes, no) = match condition.kind {
            ExprKind::Unary(UnOp::Not, inner) => (inner, no, Some(yes)),
            _ => (condition, Some(yes), no),
        };
        let predicate = self.call(condition)?;
        let local = self.local(predicate.receiver)?;
        let ty::Adt(adt, _) = self.typeck.expr_ty(predicate.receiver).peel_refs().kind() else {
            return None;
        };
        let owner = match predicate.owner {
            OptionOrResult::Option => rustc_span::sym::Option,
            OptionOrResult::Result => rustc_span::sym::Result,
        };
        if !self.tcx.is_diagnostic_item(owner, adt.did()) {
            return None;
        }
        let (payload, error) = match predicate.method.as_str() {
            "is_some" | "is_ok" => (yes, no),
            "is_none" | "is_err" => (no, yes),
            _ => return None,
        };
        payload
            .and_then(|branch| self.extraction(branch, local, &predicate, "unwrap", "expect"))
            .or_else(|| match predicate.owner {
                OptionOrResult::Result => {
                    self.extraction(error?, local, &predicate, "unwrap_err", "expect_err")
                }
                OptionOrResult::Option => None,
            })
    }

    fn extraction(
        &self,
        branch: &'tcx Expr<'tcx>,
        local: HirId,
        predicate: &Call<'_>,
        extract: &str,
        expect: &str,
    ) -> Option<(Span, CompilerEvidence)> {
        let mut expression = branch;
        let call = loop {
            if let Some(call) = self.call(expression)
                && self.local(call.receiver) == Some(local)
            {
                break call;
            }
            expression = match expression.kind {
                ExprKind::Block(block, _) => match block.stmts.first().map(|stmt| &stmt.kind) {
                    Some(StmtKind::Expr(value) | StmtKind::Semi(value)) => value,
                    Some(StmtKind::Let(binding)) => binding.init?,
                    Some(StmtKind::Item(_)) => return None,
                    None => block.expr?,
                },
                ExprKind::Ret(Some(value)) | ExprKind::DropTemps(value) => value,
                ExprKind::Call(callee, [first, ..])
                    if let ExprKind::Path(ref path) = callee.kind =>
                {
                    match self.typeck.qpath_res(path, callee.hir_id) {
                        Res::Def(DefKind::Fn | DefKind::AssocFn | DefKind::Ctor(..), _) => first,
                        Res::Local(_) if self.typeck.expr_ty(callee).is_fn_ptr() => first,
                        _ => return None,
                    }
                }
                ExprKind::MethodCall(_, receiver, _, _) => receiver,
                _ => return None,
            };
        };
        match (call.method.as_str(), call.arguments) {
            (name, []) if name == extract => {}
            (name, [message])
                if name == expect
                    && let ExprKind::Lit(_) = message.kind => {}
            _ => return None,
        }
        Some((
            predicate.span,
            CompilerEvidence::PayloadPredicate {
                method: predicate.method.to_string(),
            },
        ))
    }

    fn discarded_error(
        &self,
        callee: &Expr<'_>,
        argument: &'tcx Expr<'tcx>,
        result: &'tcx Expr<'tcx>,
    ) -> Option<(Span, CompilerEvidence)> {
        if variant_constructor(self.tcx, self.typeck, callee)?
            != self.tcx.lang_items().result_ok_variant()?
        {
            return None;
        }
        let call = self.call(argument)?;
        let OptionOrResult::Result = call.owner else {
            return None;
        };
        let ty = self.typeck.expr_ty(result);
        if self.typeck.expr_ty(call.receiver).peel_refs() != ty {
            return None;
        }
        let ty::Adt(_, args) = ty.kind() else {
            return None;
        };
        match (call.method.as_str(), call.arguments) {
            ("unwrap_or", [fallback]) if let ExprKind::Lit(_) = fallback.kind => {}
            ("unwrap_or_default", []) if args.type_at(0).is_primitive() => {}
            ("unwrap_or_else", [fallback]) if let ExprKind::Closure(closure) = fallback.kind => {
                let body = self.tcx.hir_body(closure.body);
                let [parameter] = body.params else {
                    return None;
                };
                let PatKind::Wild = parameter.pat.kind else {
                    return None;
                };
                let mut value = body.value;
                while let ExprKind::Block(block, _) = value.kind {
                    if !block.stmts.is_empty() {
                        return None;
                    }
                    value = block.expr?;
                }
                let ExprKind::Lit(_) = value.kind else {
                    return None;
                };
            }
            _ => return None,
        }
        Some((
            call.span,
            CompilerEvidence::Fallback {
                method: call.method.to_string(),
            },
        ))
    }
}

fn variant_constructor(
    tcx: TyCtxt<'_>,
    typeck: &TypeckResults<'_>,
    callee: &Expr<'_>,
) -> Option<DefId> {
    let ExprKind::Path(ref path) = callee.kind else {
        return None;
    };
    let Res::Def(DefKind::Ctor(CtorOf::Variant, _), ctor) = typeck.qpath_res(path, callee.hir_id)
    else {
        return None;
    };
    Some(tcx.parent(ctor))
}

impl<'tcx> Visitor<'tcx> for Expressions<'tcx, '_> {
    fn visit_expr(&mut self, expression: &'tcx Expr<'tcx>) {
        intravisit::walk_expr(self, expression);
        if expression.span.from_expansion() {
            return;
        }
        let finding = match expression.kind {
            ExprKind::If(condition, yes, no) => self.guarded_extraction(condition, yes, no),
            ExprKind::Call(callee, [argument]) => {
                self.discarded_error(callee, argument, expression)
            }
            _ => return,
        };
        if let Some((span, evidence)) = finding {
            self.findings.push(Located {
                def: self.def,
                item_span: self
                    .tcx
                    .def_span(self.tcx.typeck_root_def_id(self.def.to_def_id())),
                span,
                evidence,
            });
        }
    }
}

pub(crate) struct DirectCall<'tcx> {
    pub owner: LocalDefId,
    pub typeck: &'tcx TypeckResults<'tcx>,
    pub expr: &'tcx Expr<'tcx>,
    pub arguments: &'tcx [Expr<'tcx>],
    pub first_parameter: usize,
}

impl<'tcx> DirectCall<'tcx> {
    pub fn argument(&self, parameter: usize) -> Option<&'tcx Expr<'tcx>> {
        self.arguments
            .get(parameter.checked_sub(self.first_parameter)?)
    }
}

// A function path also escapes when used as a value in unreachable or generated code.
pub(crate) fn function_uses<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut observe: impl FnMut(DefId, Option<DirectCall<'tcx>>),
) {
    struct Uses<'a, 'tcx, F> {
        tcx: TyCtxt<'tcx>,
        typeck: &'tcx TypeckResults<'tcx>,
        owner: LocalDefId,
        observe: &'a mut F,
    }
    impl<'tcx, F: FnMut(DefId, Option<DirectCall<'tcx>>)> Visitor<'tcx> for Uses<'_, 'tcx, F> {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            let direct = |expr, arguments, first_parameter| DirectCall {
                owner: self.owner,
                typeck: self.typeck,
                expr,
                arguments,
                first_parameter,
            };
            match expr.kind {
                ExprKind::MethodCall(_, _, args, _) => {
                    if let Some(def) = self.typeck.type_dependent_def_id(expr.hir_id) {
                        (self.observe)(def, Some(direct(expr, args, 1)));
                    }
                }
                ExprKind::Path(ref path)
                    if let Res::Def(DefKind::Fn | DefKind::AssocFn, def) =
                        self.typeck.qpath_res(path, expr.hir_id) =>
                {
                    let usage = match self.tcx.parent_hir_node(expr.hir_id) {
                        Node::Expr(call)
                            if let ExprKind::Call(callee, args) = call.kind
                                && callee.hir_id == expr.hir_id =>
                        {
                            Some(direct(call, args, 0))
                        }
                        _ => None,
                    };
                    (self.observe)(def, usage);
                }
                _ => {}
            }
            intravisit::walk_expr(self, expr);
        }
    }
    for owner in tcx.hir_body_owners() {
        let root = tcx.typeck_root_def_id(owner.to_def_id()).expect_local();
        Uses {
            tcx,
            typeck: tcx.typeck(root),
            owner,
            observe: &mut observe,
        }
        .visit_body(tcx.hir_body_owned_by(owner));
    }
}
