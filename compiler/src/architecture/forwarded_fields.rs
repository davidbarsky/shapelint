use std::collections::hash_map::Entry;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::LocalDefId;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{
    BinOpKind, BindingMode, Body, Expr, ExprKind, HirId, MatchSource, Node, PatKind, StmtKind, UnOp,
};
use rustc_middle::ty::{self, TyCtxt, TypeckResults};
use rustc_span::{Span, Symbol, kw, sym};
use shapelint::{CompilerEvidence, LintError};

use crate::architecture::{Field, Site, local, visible_sites};
use crate::callers::{self, Exposure, Scope};
use crate::diagnostics::{self, Located, Sources};
use crate::hir_rules::{self, DirectCall};

struct Forwarded<'tcx> {
    parameter: usize,
    field: Field<'tcx>,
    sites: Vec<Site>,
}

pub(crate) fn findings(tcx: TyCtxt<'_>, sources: &Sources) -> Result<Vec<Located>, LintError> {
    let mut candidates: FxHashMap<LocalDefId, Vec<Forwarded<'_>>> = FxHashMap::default();
    hir_rules::function_uses(tcx, |def, usage| {
        let Some(callee) = def.as_local() else { return };
        let entry = candidates.entry(callee);
        let Some(call) = usage else {
            entry.or_default().clear();
            return;
        };
        match entry {
            Entry::Vacant(entry) => {
                let fields = call
                    .arguments
                    .iter()
                    .enumerate()
                    .filter_map(|(offset, arg)| {
                        let (field, site) = forwarded(tcx, &call, arg)?;
                        Some(Forwarded {
                            parameter: call.first_parameter + offset,
                            field,
                            sites: vec![site],
                        })
                    });
                entry.insert(fields.collect());
            }
            Entry::Occupied(mut entry) => {
                entry.get_mut().retain_mut(|candidate| {
                    let arg = call.argument(candidate.parameter);
                    if let Some((field, site)) = arg.and_then(|arg| forwarded(tcx, &call, arg))
                        && field == candidate.field
                    {
                        candidate.sites.push(site);
                        true
                    } else {
                        false
                    }
                });
            }
        }
    });

    let mut reports = Vec::new();
    let mut suppressions = FxHashMap::default();
    for (callee, fields) in candidates {
        if fields.is_empty() {
            continue;
        }
        if let Exposure::External = callers::exposure(tcx, callee.to_def_id(), Scope::Library) {
            continue;
        }
        if let Some(_) = tcx
            .trait_of_assoc(callee.to_def_id())
            .or_else(|| tcx.trait_impl_of_assoc(callee.to_def_id()))
        {
            continue;
        }
        let Some(body) = tcx.hir_maybe_body_owned_by(callee) else {
            continue;
        };
        let typeck = tcx.typeck(callee);
        for Forwarded {
            parameter,
            field,
            sites,
        } in fields
        {
            let owner = tcx.parent(field.def);
            if ![field.def, owner].into_iter().all(|def| {
                tcx.visibility(def)
                    .is_accessible_from(callee.to_def_id(), tcx)
            }) || tcx.def_kind(tcx.parent(owner)) != DefKind::Mod
            {
                continue;
            }
            let Some((span, label)) = decision(tcx, typeck, body, parameter) else {
                continue;
            };
            let call_count = sites.len();
            let visible = visible_sites(
                tcx,
                sources,
                &mut suppressions,
                "forwarded-field",
                sites,
                |site| *site,
            )?;
            let Some((&first, rest)) = visible.split_first() else {
                continue;
            };
            let decision = Site { def: callee, span }.related(tcx, sources, label)?;
            let other_calls = rest
                .iter()
                .map(|site| site.related(tcx, sources, "forwards the same field".into()))
                .collect::<Result<_, _>>()?;
            reports.push(Located {
                def: first.def,
                item_span: first.item_span(tcx),
                span: first.span,
                evidence: CompilerEvidence::ForwardedField {
                    callee: tcx.def_path_str(callee),
                    owner: field.owner.to_string(),
                    field: tcx.item_name(field.def).to_string(),
                    call_count,
                    decision,
                    other_calls,
                },
            });
        }
    }
    Ok(reports)
}

// Only a by-value, immutable let can name a copy that has never been reassigned.
fn initializer<'tcx>(tcx: TyCtxt<'tcx>, id: HirId) -> Option<&'tcx Expr<'tcx>> {
    let Node::LetStmt(binding) = tcx.parent_hir_node(id) else {
        return None;
    };
    let PatKind::Binding(BindingMode::NONE, binding_id, _, None) = binding.pat.kind else {
        return None;
    };
    if binding_id != id {
        return None;
    }
    binding.init
}

fn forwarded<'tcx>(
    tcx: TyCtxt<'tcx>,
    call: &DirectCall<'tcx>,
    argument: &'tcx Expr<'tcx>,
) -> Option<(Field<'tcx>, Site)> {
    let mut expr = argument;
    while let Some(id) = local(call.typeck, expr) {
        expr = initializer(tcx, id)?;
    }
    let ExprKind::Field(receiver, _) = expr.kind else {
        return None;
    };
    // Project an existing record. A freshly constructed or selected record may
    // already contain a caller-specific override.
    let mut base = receiver;
    while let ExprKind::Field(inner, _) | ExprKind::Unary(UnOp::Deref, inner) = base.kind {
        base = inner;
    }
    let ExprKind::Path(ref path) = base.kind else {
        return None;
    };
    match call.typeck.qpath_res(path, base.hir_id) {
        Res::Local(id) if expr.hir_id != argument.hir_id => {
            // A saved copy can outlive a mutable record or a local reborrow.
            let Node::Pat(pat) = tcx.hir_node(id) else {
                return None;
            };
            let PatKind::Binding(mode, _, _, _) = pat.kind else {
                return None;
            };
            match (
                mode,
                call.typeck.expr_ty(base).kind(),
                tcx.parent_hir_node(id),
            ) {
                (BindingMode::NONE, ty::Ref(_, _, rustc_hir::Mutability::Not), Node::Param(_)) => {}
                (BindingMode::NONE, ty::Adt(..), _) => {}
                _ => adjacent_copy(tcx, call, argument, expr)?,
            }
        }
        Res::Local(_)
        | Res::Def(
            DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::Static { .. },
            _,
        ) => {}
        _ => return None,
    }
    let mut field = Field::projected(call.typeck, receiver, expr.hir_id)?;
    field.owner = tcx.erase_and_anonymize_regions(field.owner);
    diagnostics::source_span(tcx, call.owner.to_def_id(), expr.span)?;
    let span = diagnostics::source_span(tcx, call.owner.to_def_id(), argument.span)?;
    Some((
        field,
        Site {
            def: call.owner,
            span,
        },
    ))
}

// For a mutable source, accept a sequence of copies immediately consumed by
// the call. Other statements or argument evaluation could change the record.
fn adjacent_copy<'tcx>(
    tcx: TyCtxt<'tcx>,
    call: &DirectCall<'tcx>,
    mut operand: &'tcx Expr<'tcx>,
    field: &Expr<'_>,
) -> Option<()> {
    if call.arguments.iter().any(Expr::can_have_side_effects) {
        return None;
    }
    if let ExprKind::MethodCall(_, receiver, _, _) = call.expr.kind
        && receiver.can_have_side_effects()
    {
        return None;
    }
    let preceding = match tcx.parent_hir_node(call.expr.hir_id) {
        Node::Block(block) => block.stmts,
        Node::Stmt(stmt) if let Node::Block(block) = tcx.parent_hir_node(stmt.hir_id) => {
            let index = block
                .stmts
                .iter()
                .position(|statement| statement.hir_id == stmt.hir_id)?;
            &block.stmts[..index]
        }
        _ => return None,
    };
    let copies = preceding.iter().rev();
    for statement in copies {
        let StmtKind::Let(binding) = statement.kind else {
            return None;
        };
        if local(call.typeck, operand)? != binding.pat.hir_id {
            return None;
        }
        operand = binding.init?;
        if operand.hir_id == field.hir_id {
            return Some(());
        }
    }
    None
}

fn decision<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    body: &'tcx Body<'tcx>,
    parameter: usize,
) -> Option<(Span, String)> {
    let pat = body.params.get(parameter)?.pat;
    let PatKind::Binding(BindingMode::NONE, binding, ident, None) = pat.kind else {
        return None;
    };
    if ident.name == kw::SelfLower {
        return None;
    }
    let ty = typeck.node_type(pat.hir_id);
    match ty.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => {}
        ty::Adt(adt, _) if adt.is_enum() && adt.is_payloadfree() => {}
        _ => return None,
    }
    let mut parameters = FxHashMap::default();
    for argument in body.params {
        argument.pat.each_binding(|mode, id, _, ident| {
            if !mode.1.is_mut() {
                parameters.insert(id, ident.name);
            }
        });
    }
    let mut decisions = Decisions {
        tcx,
        typeck,
        binding,
        parameters,
        conditions: FxHashSet::default(),
        found: None,
    };
    let mut value = body.value;
    if let ExprKind::Closure(closure) = value.kind
        && let rustc_hir::ClosureKind::Coroutine(kind) = closure.kind
        && kind.is_fn_like()
    {
        value = tcx.hir_body(closure.body).value;
    }
    decisions.condition(value.peel_blocks());
    decisions.visit_expr(value);
    let (span, input) = decisions.found?;
    Some((
        span,
        format!("uses `{}` in a decision about `{input}`", ident.name),
    ))
}

struct Decisions<'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    binding: HirId,
    parameters: FxHashMap<HirId, Symbol>,
    conditions: FxHashSet<HirId>,
    found: Option<(Span, Symbol)>,
}

impl<'tcx> Decisions<'tcx> {
    // The forwarded operand can change units inside the callee. Opaque functions
    // accepting the operand need not return a value derived from it.
    fn threshold(&self, mut expr: &'tcx Expr<'tcx>) -> Option<()> {
        loop {
            expr = expr.peel_drop_temps().peel_blocks();
            if let Some(id) = local(self.typeck, expr) {
                if id == self.binding {
                    return Some(());
                }
                expr = initializer(self.tcx, id)?;
                continue;
            }
            expr = match expr.kind {
                ExprKind::Cast(value, _) | ExprKind::Unary(UnOp::Not | UnOp::Neg, value) => value,
                ExprKind::Binary(op, lhs, rhs)
                    if let None = self.typeck.type_dependent_def_id(expr.hir_id) =>
                {
                    match op.node {
                        BinOpKind::Mul | BinOpKind::Div | BinOpKind::Add | BinOpKind::Sub => {}
                        comparison if comparison.is_comparison() => {}
                        _ => return None,
                    }
                    if let Some(()) = self.constant(rhs) {
                        lhs
                    } else if let Some(()) = self.constant(lhs) {
                        rhs
                    } else {
                        return None;
                    }
                }
                ExprKind::Call(callee, [value])
                    if let ExprKind::Path(ref path) = callee.kind
                        && let Res::Def(_, def) = self.typeck.qpath_res(path, callee.hir_id)
                        && let Some(trait_id) = self.tcx.trait_of_assoc(def)
                        && self.tcx.is_diagnostic_item(sym::From, trait_id)
                        && self.typeck.expr_ty(value).is_numeric()
                        && self.typeck.expr_ty(expr).is_numeric() =>
                {
                    value
                }
                ExprKind::MethodCall(_, value, args, _)
                    if self.typeck.expr_ty(value).is_numeric()
                        && self.typeck.expr_ty(expr).is_numeric()
                        && let Some(def) = self.typeck.type_dependent_def_id(expr.hir_id) =>
                {
                    match self.tcx.trait_of_assoc(def) {
                        Some(trait_id)
                            if args.is_empty()
                                && self.tcx.is_diagnostic_item(sym::Into, trait_id) =>
                        {
                            value
                        }
                        None if let Some(owner) = self.tcx.inherent_impl_of_assoc(def)
                            && self
                                .tcx
                                .type_of(owner)
                                .instantiate_identity()
                                .skip_normalization()
                                .is_numeric()
                            && args.iter().all(|arg| self.constant(arg) == Some(())) =>
                        {
                            value
                        }
                        _ => return None,
                    }
                }
                _ => return None,
            };
        }
    }

    fn constant(&self, mut expr: &'tcx Expr<'tcx>) -> Option<()> {
        loop {
            expr = expr.peel_drop_temps();
            match expr.kind {
                ExprKind::Lit(_) => return Some(()),
                ExprKind::Cast(value, _) => expr = value,
                ExprKind::Path(ref path) => match self.typeck.qpath_res(path, expr.hir_id) {
                    Res::Def(DefKind::Const { .. } | DefKind::AssocConst { .. }, _) => {
                        return Some(());
                    }
                    Res::Local(id) => expr = initializer(self.tcx, id)?,
                    _ => return None,
                },
                _ => return None,
            }
        }
    }

    // Trace the value of the other operand, including a payload bound by a
    // pattern. A statement discarded on the way to producing it supplies no value.
    fn other_input(&self, expr: &'tcx Expr<'tcx>) -> Option<Symbol> {
        let mut pending = vec![expr];
        let mut visited = FxHashSet::default();
        let mut other = None;
        while let Some(expr) = pending.pop() {
            if !visited.insert(expr.hir_id) {
                continue;
            }
            if let Some(id) = local(self.typeck, expr) {
                if id == self.binding {
                    return None;
                }
                if let Some(&name) = self.parameters.get(&id) {
                    other = Some(name);
                } else if let Some(init) = self.binding_value(id) {
                    pending.push(init);
                }
                continue;
            }
            match expr.kind {
                ExprKind::Field(base, _)
                | ExprKind::Unary(_, base)
                | ExprKind::Cast(base, _)
                | ExprKind::AddrOf(_, _, base)
                | ExprKind::DropTemps(base) => pending.push(base),
                ExprKind::Binary(_, a, b) | ExprKind::Index(a, b, _) => pending.extend([a, b]),
                ExprKind::Call(callee, [value])
                    if let ExprKind::Path(ref path) = callee.kind
                        && let Res::Def(kind, def) = self.typeck.qpath_res(path, callee.hir_id) =>
                {
                    let lang = self.tcx.lang_items();
                    match kind {
                        DefKind::Ctor(..) => pending.push(value),
                        _ if [lang.into_iter_fn(), lang.next_fn()].contains(&Some(def)) => {
                            pending.push(value)
                        }
                        _ => {}
                    }
                }
                ExprKind::MethodCall(_, receiver, _, _)
                    if let Some(def) = self.typeck.type_dependent_def_id(expr.hir_id) =>
                {
                    // Trace the receiver of standard operations on numeric values,
                    // strings, collections and iterators. An opaque helper can ignore its input.
                    let core = self.tcx.lang_items().option_type().map(|id| id.krate);
                    let alloc = self.tcx.get_diagnostic_item(sym::Vec).map(|id| id.krate);
                    if [core, alloc].contains(&Some(def.krate)) {
                        pending.push(receiver);
                    }
                }
                ExprKind::If(_, yes, no) => {
                    pending.push(yes);
                    pending.extend(no);
                }
                ExprKind::Match(_, arms, _) => pending.extend(arms.iter().map(|arm| arm.body)),
                ExprKind::Block(block, _) => pending.extend(block.expr),
                _ => {}
            }
        }
        other
    }

    fn binding_value(&self, id: HirId) -> Option<&'tcx Expr<'tcx>> {
        let Node::Pat(pat) = self.tcx.hir_node(id) else {
            return None;
        };
        let PatKind::Binding(mode, _, _, _) = pat.kind else {
            return None;
        };
        for (parent, node) in self.tcx.hir_parent_iter(id) {
            match node {
                Node::Pat(_) | Node::PatField(_) => continue,
                Node::LetStmt(binding) if !mode.1.is_mut() => return binding.init,
                Node::Expr(expr)
                    if !mode.1.is_mut()
                        && let ExprKind::Let(binding) = expr.kind =>
                {
                    return Some(binding.init);
                }
                Node::Arm(_)
                    if let Node::Expr(expr) = self.tcx.parent_hir_node(parent)
                    && let ExprKind::Match(scrutinee, arms, source) = expr.kind
                    // The outer for-loop match binds the compiler's mutable iterator.
                    && (!mode.1.is_mut() || (source == MatchSource::ForLoopDesugar && arms.len() == 1)) =>
                {
                    return Some(scrutinee);
                }
                _ => break,
            }
        }
        None
    }

    fn condition(&mut self, expr: &'tcx Expr<'tcx>) {
        let expr = expr.peel_drop_temps().peel_blocks();
        if let Some(_) = self.found {
            return;
        }
        if !self.conditions.insert(expr.hir_id) {
            return;
        }
        match expr.kind {
            ExprKind::Binary(op, a, b) if op.node.is_comparison() => {
                let input = [(a, b), (b, a)].into_iter().find_map(|(limit, input)| {
                    self.threshold(limit)?;
                    self.other_input(input)
                });
                self.record(expr, input);
            }
            ExprKind::Binary(op, a, b) if let BinOpKind::And | BinOpKind::Or = op.node => {
                self.condition(a);
                self.condition(b);
                for (gate, input) in [(a, b), (b, a)] {
                    if let Some(()) = self.threshold(gate) {
                        self.record(gate, self.other_input(input));
                    }
                }
            }
            ExprKind::Unary(UnOp::Not, inner) => self.condition(inner),
            ExprKind::Path(_)
                if let Some(init) =
                    local(self.typeck, expr).and_then(|id| initializer(self.tcx, id)) =>
            {
                self.condition(init)
            }
            _ => {}
        }
    }

    fn record(&mut self, expr: &Expr<'_>, input: Option<Symbol>) {
        if let (None, Some(input)) = (self.found, input)
            && let Some(span) = diagnostics::source_span(
                self.tcx,
                self.tcx.hir_enclosing_body_owner(expr.hir_id).to_def_id(),
                expr.span,
            )
        {
            self.found = Some((span, input));
        }
    }

    fn controlled_input(&self, expr: &'tcx Expr<'tcx>) -> Option<Symbol> {
        match expr.kind {
            ExprKind::Block(block, _) => block
                .stmts
                .iter()
                .find_map(|stmt| match stmt.kind {
                    StmtKind::Expr(expr) | StmtKind::Semi(expr) if expr.can_have_side_effects() => {
                        self.controlled_input(expr)
                    }
                    _ => None,
                })
                .or_else(|| self.controlled_input(block.expr?)),
            ExprKind::Assign(place, _, _) | ExprKind::AssignOp(_, place, _) => {
                self.other_input(place)
            }
            ExprKind::Ret(Some(value)) => self.other_input(value),
            ExprKind::Call(_, args) | ExprKind::MethodCall(_, _, args, _)
                if args.iter().any(|arg| self.threshold(arg) == Some(())) =>
            {
                None
            }
            ExprKind::Call(_, args) => args.iter().find_map(|arg| self.other_input(arg)),
            ExprKind::MethodCall(_, receiver, _, _) => self.controlled_input(receiver),
            _ => self.other_input(expr),
        }
    }
}

impl<'tcx> Visitor<'tcx> for Decisions<'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let Some(_) = self.found {
            return;
        }
        match expr.kind {
            ExprKind::If(condition, yes, no) => {
                self.condition(condition);
                if let Some(()) = self.threshold(condition) {
                    self.record(
                        condition,
                        self.controlled_input(yes)
                            .or_else(|| self.controlled_input(no?)),
                    );
                }
            }
            ExprKind::Ret(Some(condition)) => self.condition(condition),
            ExprKind::Match(scrutinee, arms, MatchSource::Normal | MatchSource::Postfix) => {
                if arms.len() > 1 {
                    self.condition(scrutinee);
                    if let Some(()) = self.threshold(scrutinee) {
                        self.record(
                            scrutinee,
                            arms.iter().find_map(|arm| self.controlled_input(arm.body)),
                        );
                    }
                }
                for arm in arms {
                    if let Some(guard) = arm.guard {
                        self.condition(guard);
                    }
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}
