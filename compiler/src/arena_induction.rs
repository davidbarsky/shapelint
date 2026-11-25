//! Checks the induction step for methods over an append-only arena.
//! Under the entry invariant every root in a local value belongs to this receiver.
//! Verify every source of those values, every use of the receiver, and each helper body.

use std::ops::ControlFlow;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{
    BinOpKind, BlockCheckMode, Expr, ExprKind, HirId, Mutability, PatKind, StructTailExpr, UnOp,
};
use rustc_middle::ty::adjustment::{Adjust, DerefAdjustKind};
use rustc_middle::ty::fast_reject::DeepRejectCtxt;
use rustc_middle::ty::{self, Ty, TyCtxt, TypeckResults};
use rustc_span::{Symbol, sym};

use crate::standard::{self, OptionOrResult};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Role {
    Storage,
    Memo,
    Empty,
    Read,
    Append,
    Lookup,
    Remember,
}

fn role(tcx: TyCtxt<'_>, def: DefId) -> Option<Role> {
    let path = [Symbol::intern("shapelint_tool"), Symbol::intern("arena")];
    let mut attrs = tcx.get_attrs_by_path(def, &path);
    let items = attrs.next()?.meta_item_list()?;
    let [item] = items.as_slice() else {
        return None;
    };
    if attrs.next().is_some() {
        return None;
    }
    Some(match item.ident()?.name.as_str() {
        "storage" => Role::Storage,
        "memo" => Role::Memo,
        "empty" => Role::Empty,
        "read" => Role::Read,
        "append" => Role::Append,
        "lookup" => Role::Lookup,
        "remember" => Role::Remember,
        _ => return None,
    })
}

pub(crate) fn proves_step(
    tcx: TyCtxt<'_>,
    def: DefId,
    requirements: impl Fn(DefId) -> Option<()>,
) -> Option<()> {
    let local = def.as_local()?;
    let owner = tcx.inherent_impl_of_assoc(def)?;
    let owner = tcx
        .type_of(owner)
        .instantiate_identity()
        .skip_normalization();
    let ty::Adt(adt, args) = *owner.kind() else {
        return None;
    };
    if !adt.is_struct() {
        return None;
    }
    let mut stores = adt
        .non_enum_variant()
        .fields
        .iter()
        .filter(|field| role(tcx, field.did) == Some(Role::Storage));
    let field = stores.next()?;
    if stores.next().is_some() {
        return None;
    }
    let ty::Adt(_, storage_args) = *field.ty(tcx, args).skip_normalization().kind() else {
        return None;
    };
    let root = storage_args.types().next()?;
    let ty::Adt(id, args) = *root.kind() else {
        return None;
    };
    if id.is_union() {
        return None;
    }
    // An ID is an opaque token. Unpacking one cannot introduce another root.
    for field in id.all_fields() {
        let ty = field.ty(tcx, args).skip_normalization();
        match *ty.kind() {
            ty::Adt(adt, _) if Some(adt.did()) == tcx.lang_items().phantom_data() => {}
            _ => scalar(ty)?,
        }
    }
    let signature = tcx.fn_sig(def).instantiate_identity().skip_binder();
    let output = signature.output();
    let ty::Adt(return_adt, args) = *output.kind() else {
        return None;
    };
    let supported_output = match tcx.get_diagnostic_name(return_adt.did()) {
        Some(sym::Result) => args.type_at(0) == root,
        Some(sym::Option) if args.type_at(0).is_unit() => true,
        _ => output == root,
    };
    if !supported_output || !signature.inputs().iter().skip(1).any(|ty| *ty == root) {
        return None;
    }
    let mut methods = vec![local];
    let mut checked = FxHashSet::default();
    while let Some(method) = methods.pop() {
        if checked.insert(method) {
            let (body, expr) = Body::method(tcx, method, adt.did(), root)?;
            let mut pending = vec![expr];
            while let Some(expr) = pending.pop() {
                body.step(expr, &mut pending, &mut methods)?;
            }
        }
    }
    closed_calls(tcx, def, field.did, requirements)
}

struct Body<'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    root: Ty<'tcx>,
    environment: ty::TypingEnv<'tcx>,
    receiver: HirId,
}

fn scalar(ty: Ty<'_>) -> Option<()> {
    match ty.kind() {
        ty::Uint(_) | ty::Int(_) | ty::Bool | ty::Char => Some(()),
        _ => None,
    }
}

impl<'tcx> Body<'tcx> {
    fn method(
        tcx: TyCtxt<'tcx>,
        def: LocalDefId,
        owner: DefId,
        root: Ty<'tcx>,
    ) -> Option<(Self, &'tcx Expr<'tcx>)> {
        let implementation = tcx.inherent_impl_of_assoc(def.to_def_id())?;
        let self_ty = tcx
            .type_of(implementation)
            .instantiate_identity()
            .skip_normalization();
        if self_ty.ty_adt_def()?.did() != owner || !tcx.generics_of(def).own_params.is_empty() {
            return None;
        }
        let signature = tcx.fn_sig(def).instantiate_identity().skip_binder();
        let (receiver, inputs) = signature.inputs().split_first()?;
        let ty::Ref(_, receiver, _) = *receiver.kind() else {
            return None;
        };
        if receiver != self_ty || !signature.safety().is_safe() {
            return None;
        }
        let environment = ty::TypingEnv::post_analysis(tcx, def);
        for ty in inputs {
            if ty.needs_drop(tcx, environment) {
                return None;
            }
            match *ty.kind() {
                ty::Adt(..) if *ty == root => {}
                ty::Adt(adt, _)
                    if adt.is_enum() && adt.variants().iter().all(|v| v.fields.is_empty()) => {}
                _ => scalar(*ty)?,
            }
        }
        let body = tcx.hir_body_owned_by(def);
        let PatKind::Binding(_, receiver, _, None) = body.params.first()?.pat.kind else {
            return None;
        };
        let scope = Self {
            tcx,
            typeck: tcx.typeck(def),
            environment,
            root: tcx.erase_and_anonymize_regions(root),
            receiver,
        };
        Some((scope, body.value))
    }

    fn binding(&self, expr: &Expr<'_>) -> Option<HirId> {
        let ExprKind::Path(ref path) = expr.kind else {
            return None;
        };
        let Res::Local(binding) = self.typeck.qpath_res(path, expr.hir_id) else {
            return None;
        };
        Some(binding)
    }

    fn builtin_adjustments(&self, expr: &Expr<'_>) -> Option<()> {
        for adjustment in self.typeck.expr_adjustments(expr) {
            match adjustment.kind {
                Adjust::Deref(DerefAdjustKind::Builtin)
                | Adjust::Borrow(_)
                | Adjust::NeverToAny => {}
                _ => return None,
            }
        }
        Some(())
    }

    fn self_field(&self, expr: &Expr<'_>) -> Option<DefId> {
        let ExprKind::Field(base, _) = expr.kind else {
            return None;
        };
        if self.binding(base) != Some(self.receiver) {
            return None;
        }
        self.builtin_adjustments(base)?;
        let adt = self
            .typeck
            .expr_ty_adjusted(base)
            .peel_refs()
            .ty_adt_def()?;
        if Some(adt) != self.typeck.expr_ty(base).peel_refs().ty_adt_def() {
            return None;
        }
        Some(
            adt.non_enum_variant()
                .fields
                .get(self.typeck.field_index(expr.hir_id))?
                .did,
        )
    }

    // A counter is a scalar field, or a member of a separate record of scalars.
    fn counter(&self, expr: &Expr<'_>) -> Option<DefId> {
        scalar(self.typeck.expr_ty(expr))?;
        let ExprKind::Field(base, _) = expr.kind else {
            return None;
        };
        let field = match self.self_field(expr) {
            Some(field) => field,
            None => {
                self.builtin_adjustments(base)?;
                let field = self.self_field(base)?;
                let ty::Adt(adt, args) = *self.typeck.expr_ty(base).kind() else {
                    return None;
                };
                if !adt.is_struct()
                    || Some(adt) == self.root.ty_adt_def()
                    || !adt
                        .all_fields()
                        .all(|f| scalar(f.ty(self.tcx, args).skip_normalization()).is_some())
                {
                    return None;
                }
                field
            }
        };
        role(self.tcx, field).is_none().then_some(field)
    }

    fn comparison(
        &self,
        op: BinOpKind,
        expr: &Expr<'_>,
        left: &Expr<'_>,
        right: &Expr<'_>,
    ) -> Option<()> {
        let tcx = self.tcx;
        let ty = self.typeck.expr_ty(left);
        if ty != self.typeck.expr_ty(right) {
            return None;
        }
        match op {
            BinOpKind::Eq
            | BinOpKind::Ne
            | BinOpKind::Gt
            | BinOpKind::Lt
            | BinOpKind::Ge
            | BinOpKind::Le => (),
            _ => return None,
        }
        if scalar(ty).is_some() {
            return Some(());
        }
        let ty::Adt(adt, args) = *ty.kind() else {
            return None;
        };
        if tcx.is_diagnostic_item(sym::Option, adt.did()) {
            return scalar(args.type_at(0));
        }
        if tcx.erase_and_anonymize_regions(ty) != self.root {
            return None;
        }
        let def = self.typeck.type_dependent_def_id(expr.hir_id)?;
        let Ok(Some(instance)) = ty::Instance::try_resolve(
            tcx,
            self.environment,
            def,
            self.typeck.node_args(expr.hir_id),
        ) else {
            return None;
        };
        if !tcx.is_builtin_derived(tcx.impl_of_assoc(instance.def_id())?) {
            return None;
        }
        Some(())
    }

    fn standard_method(
        &self,
        def: DefId,
        receiver: &Expr<'_>,
        args: &[Expr<'_>],
        output: Ty<'tcx>,
    ) -> Option<()> {
        let tcx = self.tcx;
        let ty = self.typeck.expr_ty(receiver).peel_refs();
        let name = tcx.item_name(def);
        match (standard::method_owner(tcx, def), name.as_str(), args) {
            // Ord::max returns one of its operands, both of which the caller checks.
            (_, "max", _)
                if tcx
                    .trait_of_assoc(def)
                    .is_some_and(|id| tcx.is_diagnostic_item(sym::Ord, id)) =>
            {
                let ty::Adt(adt, args) = *ty.kind() else {
                    return None;
                };
                if !tcx.is_diagnostic_item(sym::Option, adt.did()) {
                    return None;
                }
                scalar(args.type_at(0))
            }
            // An alias or a lifetime conversion may give the result the arena's ID type.
            _ if DeepRejectCtxt::relate_infer_infer(tcx).types_may_unify(output, self.root) => None,
            (Some(OptionOrResult::Option), "as_ref" | "ok_or", _) => Some(()),
            (
                Some(OptionOrResult::Option),
                "map",
                [
                    Expr {
                        kind: ExprKind::Closure(_),
                        ..
                    },
                ],
            ) => Some(()),
            (_, "checked_add" | "saturating_add" | "isolate_highest_one", _)
                if ty.is_integral()
                    && tcx.inherent_impl_of_assoc(def).is_some()
                    && tcx.crate_name(def.krate) == sym::core =>
            {
                Some(())
            }
            _ => None,
        }
    }

    fn try_call(&self, def: DefId, expr: &Expr<'_>, args: &[Expr<'_>]) -> Option<()> {
        let tcx = self.tcx;
        let [arg] = args else { return None };
        let ty::Adt(source, args) = *self.typeck.expr_ty(arg).kind() else {
            return None;
        };
        let error = match tcx.get_diagnostic_name(source.did()) {
            Some(sym::Option) => None,
            Some(sym::Result) => Some(args.type_at(1)),
            _ => return None,
        };
        let output = self.typeck.expr_ty(expr);
        if DeepRejectCtxt::relate_infer_infer(tcx).types_may_unify(output, self.root) {
            return None;
        }
        if Some(def) == tcx.lang_items().branch_fn() {
            return Some(());
        }
        let ty::Adt(target, args) = *output.kind() else {
            return None;
        };
        if Some(def) != tcx.lang_items().from_residual_fn() || source != target {
            return None;
        }
        if let Some(error) = error
            && args.type_at(1) != error
        {
            return None;
        }
        Some(())
    }

    fn step(
        &self,
        expr: &'tcx Expr<'tcx>,
        pending: &mut Vec<&'tcx Expr<'tcx>>,
        methods: &mut Vec<LocalDefId>,
    ) -> Option<()> {
        let tcx = self.tcx;
        self.builtin_adjustments(expr)?;
        let ty = self.typeck.expr_ty(expr);
        if ty.needs_drop(tcx, self.environment) {
            return None;
        }
        let root = ty.ty_adt_def() == self.root.ty_adt_def();
        match expr.kind {
            ExprKind::MethodCall(_, receiver, args, _) => {
                let def = self.typeck.type_dependent_def_id(expr.hir_id)?;
                self.builtin_adjustments(receiver)?;
                if self.binding(receiver) == Some(self.receiver) {
                    methods.push(def.as_local()?);
                } else if let Some(field) = self.self_field(receiver)
                    && let Some(field_role) = role(tcx, field)
                {
                    def.as_local()?;
                    match (field_role, role(tcx, def)?) {
                        (Role::Storage, Role::Read | Role::Append)
                        | (Role::Memo, Role::Lookup | Role::Remember) => {}
                        _ => return None,
                    }
                    let owner = tcx.inherent_impl_of_assoc(def)?;
                    let ty = tcx
                        .type_of(owner)
                        .instantiate_identity()
                        .skip_normalization();
                    if ty.ty_adt_def()? != self.typeck.expr_ty(receiver).ty_adt_def()? {
                        return None;
                    }
                    let sig = tcx.fn_sig(def).instantiate_identity().skip_binder();
                    if !sig.safety().is_safe() {
                        return None;
                    }
                    let ty::Ref(_, _, Mutability::Not) = sig.inputs().first()?.kind() else {
                        return None;
                    };
                } else {
                    self.standard_method(def, receiver, args, ty)?;
                    pending.push(receiver);
                }
                pending.extend(args);
                return Some(());
            }
            ExprKind::Path(ref path) => {
                return match self.typeck.qpath_res(path, expr.hir_id) {
                    Res::Local(id) if id != self.receiver => Some(()),
                    Res::Def(DefKind::AssocConst { .. }, def)
                        if tcx.erase_and_anonymize_regions(ty) == self.root
                            && role(tcx, def) == Some(Role::Empty) =>
                    {
                        Some(())
                    }
                    Res::Def(DefKind::Ctor(..) | DefKind::Variant, _) if !root => Some(()),
                    _ => None,
                };
            }
            ExprKind::Call(callee, args) => {
                let ExprKind::Path(ref path) = callee.kind else {
                    return None;
                };
                let Res::Def(kind, def) = self.typeck.qpath_res(path, callee.hir_id) else {
                    return None;
                };
                match kind {
                    DefKind::Ctor(..) if !root => {}
                    _ => self.try_call(def, expr, args)?,
                }
                pending.extend(args);
                return Some(());
            }
            ExprKind::Closure(closure) => {
                let body = tcx.hir_body(closure.body);
                let [parameter] = body.params else {
                    return None;
                };
                let PatKind::Binding(_, id, _, None) = parameter.pat.kind else {
                    return None;
                };
                let ExprKind::Field(base, _) = body.value.kind else {
                    return None;
                };
                if self.binding(base) != Some(id) {
                    return None;
                }
                pending.push(body.value);
                return Some(());
            }
            ExprKind::Assign(place, value, _) => {
                self.counter(place)?;
                pending.push(value);
                return Some(());
            }
            ExprKind::Field(..) if self.counter(expr).is_some() => return Some(()),
            ExprKind::Struct(_, _, StructTailExpr::None) if !root => {}
            ExprKind::Unary(UnOp::Deref, value) if self.typeck.expr_ty(value).is_ref() => {}
            ExprKind::Binary(op, left, right) => {
                if self.typeck.type_dependent_def_id(expr.hir_id).is_some() {
                    self.comparison(op.node, expr, left, right)?;
                }
            }
            ExprKind::Block(block, _) if block.rules == BlockCheckMode::DefaultBlock => {}
            ExprKind::Tup(_)
            | ExprKind::Field(..)
            | ExprKind::AddrOf(_, Mutability::Not, _)
            | ExprKind::Let(_)
            | ExprKind::If(..)
            | ExprKind::Match(..)
            | ExprKind::Lit(_)
            | ExprKind::DropTemps(_)
            | ExprKind::Ret(_) => {}
            _ => return None,
        }
        intravisit::walk_expr(&mut Children(pending), expr).continue_value()
    }
}

struct Children<'a, 'tcx>(&'a mut Vec<&'tcx Expr<'tcx>>);

impl<'tcx> Visitor<'tcx> for Children<'_, 'tcx> {
    type Result = ControlFlow<()>;

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) -> Self::Result {
        self.0.push(expr);
        ControlFlow::Continue(())
    }

    fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) -> Self::Result {
        if let PatKind::Deref(_) = pat.kind {
            return ControlFlow::Break(());
        }
        intravisit::walk_pat(self, pat)
    }
}

// Resolve leaf calls in the original method's typing environment, including closures
// handed to an external iterator or collection. A raw function pointer has no such body.
fn closed_calls(
    tcx: TyCtxt<'_>,
    def: DefId,
    field: DefId,
    requirements: impl Fn(DefId) -> Option<()>,
) -> Option<()> {
    let environment = ty::TypingEnv::post_analysis(tcx, def);
    let backends = [
        Symbol::intern("shapelint_tool"),
        Symbol::intern("arena_backends"),
    ];
    let backends: FxHashSet<_> = tcx
        .get_attrs_by_path(field, &backends)
        .filter_map(|attr| attr.meta_item_list())
        .flatten()
        .filter_map(|item| item.ident().map(|id| id.name))
        .collect();
    let mut pending = vec![(
        def,
        tcx.erase_and_anonymize_regions(ty::GenericArgs::identity_for_item(tcx, def)),
    )];
    let mut visited = FxHashMap::default();
    let mut drop_types = FxHashSet::default();
    while let Some((def, args)) = pending.pop() {
        if !def.is_local() {
            match tcx.crate_name(def.krate) {
                sym::core | sym::std | sym::alloc => continue,
                name if backends.contains(&name) => continue,
                _ => return None,
            }
        }
        let local = def.expect_local();
        // Changing instantiations can make this graph infinite.
        match visited.insert(def, args) {
            Some(previous) if previous == args => continue,
            Some(_) => return None,
            None => {}
        }
        requirements(def)?;
        let body = tcx.hir_maybe_body_owned_by(local)?;
        let typeck = tcx.typeck(tcx.typeck_root_def_id(def).expect_local());
        let mut calls = Calls {
            tcx,
            typeck,
            environment,
            args,
            pending: &mut pending,
            drop_types: &mut drop_types,
        };
        for param in body.params {
            calls.drops(typeck.pat_ty(param.pat))?;
        }
        calls.visit_expr(body.value).continue_value()?;
    }
    Some(())
}

struct Calls<'tcx, 'a> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    environment: ty::TypingEnv<'tcx>,
    args: ty::GenericArgsRef<'tcx>,
    pending: &'a mut Vec<(DefId, ty::GenericArgsRef<'tcx>)>,
    drop_types: &'a mut FxHashSet<Ty<'tcx>>,
}

impl<'tcx> Calls<'tcx, '_> {
    fn drops(&mut self, ty: Ty<'tcx>) -> Option<()> {
        let ty = ty::EarlyBinder::bind(self.tcx, ty)
            .instantiate(self.tcx, self.args)
            .skip_normalization();
        if self.drop_types.contains(&ty) {
            return Some(());
        }
        let mut pending = vec![ty];
        let mut local_types = FxHashMap::default();
        while let Some(ty) = pending.pop() {
            if !self.drop_types.insert(ty) || !ty.needs_drop(self.tcx, self.environment) {
                continue;
            }
            match *ty.kind() {
                ty::Tuple(fields) => pending.extend(fields.iter()),
                ty::Array(element, _) | ty::Slice(element) => pending.push(element),
                ty::Closure(_, args) => pending.push(args.as_closure().tupled_upvars_ty()),
                ty::Adt(adt, args) => {
                    if let Some(destructor) = adt.destructor(self.tcx) {
                        self.pending.push((destructor.did, args));
                    }
                    if adt.did().is_local() {
                        // A recursive field may instantiate the same type with growing arguments.
                        if let Some(previous) = local_types.insert(adt.did(), ty)
                            && previous != ty
                        {
                            return None;
                        }
                        pending.extend(
                            adt.all_fields()
                                .map(|field| field.ty(self.tcx, args).skip_normalization()),
                        );
                    } else {
                        // A library container may own its elements through a pointer.
                        pending.extend(args.types());
                    }
                }
                _ => return None,
            }
        }
        Some(())
    }

    fn target(&mut self, def: DefId, args: ty::GenericArgsRef<'tcx>) -> Option<()> {
        match self.tcx.def_kind(def) {
            DefKind::Fn | DefKind::AssocFn | DefKind::Closure => {}
            DefKind::Ctor(..) | DefKind::AssocConst { .. } => return Some(()),
            _ => return None,
        }
        let args = ty::EarlyBinder::bind(self.tcx, args)
            .instantiate(self.tcx, self.args)
            .skip_normalization();
        let args = self.tcx.erase_and_anonymize_regions(args);
        let Ok(Some(instance)) = ty::Instance::try_resolve(self.tcx, self.environment, def, args)
        else {
            return None;
        };
        let ty::InstanceKind::Item(def) = instance.def else {
            return None;
        };
        self.pending.push((def, instance.args));
        Some(())
    }
}

impl<'tcx> Visitor<'tcx> for Calls<'tcx, '_> {
    type Result = ControlFlow<()>;

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) -> Self::Result {
        let ty = self.typeck.expr_ty(expr);
        let mut adjusted = ty;
        for adjustment in self.typeck.expr_adjustments(expr) {
            if let Adjust::Deref(DerefAdjustKind::Overloaded(deref)) = adjustment.kind
                && self
                    .target(
                        deref.method_call(self.tcx),
                        self.tcx.mk_args(&[adjusted.into()]),
                    )
                    .is_none()
            {
                return ControlFlow::Break(());
            }
            adjusted = adjustment.target;
        }
        if (!expr.is_syntactic_place_expr() || !self.typeck.expr_ty_adjusted(expr).is_ref())
            && self.drops(ty).is_none()
        {
            return ControlFlow::Break(());
        }
        match *ty.peel_refs().kind() {
            ty::FnDef(def, args) => {
                if self.target(def, args.skip_binder()).is_none() {
                    return ControlFlow::Break(());
                }
            }
            ty::Closure(def, args) => {
                if self.target(def, args).is_none() {
                    return ControlFlow::Break(());
                }
            }
            ty::FnPtr(..) | ty::Dynamic(..) => return ControlFlow::Break(()),
            _ => {}
        }
        if let Some(def) = self.typeck.type_dependent_def_id(expr.hir_id)
            && self
                .target(def, self.typeck.node_args(expr.hir_id))
                .is_none()
        {
            return ControlFlow::Break(());
        }
        intravisit::walk_expr(self, expr)
    }
}
