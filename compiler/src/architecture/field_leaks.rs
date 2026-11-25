use std::cell::OnceCell;

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::{CtorOf, DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::pat_util::EnumerateAndAdjustIterator;
use rustc_hir::{
    Block, Body, Expr, ExprKind, HirId, Mutability, Node, Pat, PatKind, StmtKind, UnOp,
};
use rustc_middle::ty::{self, TyCtxt, TypeckResults};
use rustc_span::{BytePos, Span, sym};
use shapelint::{CompilerEvidence, LintError};

use crate::Located;
use crate::architecture::tangles::Tangles;
use crate::architecture::{Field, Site, local, owner, visible_sites};
use crate::diagnostics::{self, Sources};

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Exposure {
    Direct,
    Value,
    Shared,
    Mutable,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum Access {
    Read,
    Borrow,
    Call,
    Index,
    BorrowMut,
    Write,
}

impl Access {
    fn action(self) -> Option<&'static str> {
        match self {
            Self::Read => None,
            Self::Write => Some("writes the field"),
            Self::Borrow => Some("borrows the representation"),
            Self::BorrowMut => Some("borrows the field mutably"),
            Self::Index => Some("indexes the field"),
            Self::Call => Some("calls a method on the field"),
        }
    }
}

pub(crate) fn findings(
    tcx: TyCtxt<'_>,
    sources: &Sources,
    tangles: &Tangles,
) -> Result<Vec<Located>, LintError> {
    let mut wrappers = FxHashMap::default();
    for def in tcx.hir_body_owners() {
        if let Some(item) = tcx.opt_associated_item(def.to_def_id())
            && item.is_method()
            && item.container == ty::AssocContainer::InherentImpl
            && let Some(_) = diagnostics::source_span(tcx, def.to_def_id(), tcx.def_span(def))
            && let Some(method) = wrapper(tcx.typeck(def), tcx.hir_body_owned_by(def))
        {
            wrappers.insert(def, method);
        }
    }
    let mut working = FxHashSet::default();
    let mut outside = FxHashMap::default();
    for def in tcx.hir_body_owners() {
        let root = tcx.typeck_root_def_id(def.to_def_id()).expect_local();
        let caller = owner(tcx, def);
        let method = tcx
            .opt_associated_item(root.to_def_id())
            .filter(|item| item.is_method());
        let mut visitor = Uses {
            tcx,
            typeck: tcx.typeck(root),
            def,
            body: tcx.hir_body_owned_by(def),
            local_uses: OnceCell::new(),
            caller,
            method: method.filter(|_| !wrappers.contains_key(&root)),
            tangles,
            wrappers: &wrappers,
            working: &mut working,
            outside: &mut outside,
        };
        visitor.visit_body(tcx.hir_body_owned_by(def));
    }

    working.retain(|&def| {
        tcx.adt_def(def)
            .non_enum_variant()
            .fields
            .iter()
            .any(|field| {
                !outside.contains_key(&field.did.expect_local())
                    && meaningful(tcx, field.did.expect_local()).is_some()
            })
    });
    let mut findings = Vec::new();
    let mut suppressions = FxHashMap::default();
    for (field, sites) in outside {
        if !working.contains(&tcx.local_parent(field)) || meaningful(tcx, field).is_none() {
            continue;
        }
        let visible = visible_sites(
            tcx,
            sources,
            &mut suppressions,
            "field-leak",
            sites,
            |entry| entry.0,
        )?;
        let Some((&(first, action), rest)) = visible.split_first() else {
            continue;
        };
        let label = |site: Site, action: &str| {
            format!("{} {action}", diagnostics::item(tcx, site.def.to_def_id()))
        };
        let other_accesses = rest
            .iter()
            .map(|&(site, action)| site.related(tcx, sources, label(site, action)))
            .collect::<Result<_, _>>()?;
        findings.push(Located {
            def: first.def,
            item_span: first.item_span(tcx),
            span: first.span,
            evidence: CompilerEvidence::FieldLeak {
                field: tcx.def_path_str(field),
                access: label(first, action),
                other_accesses,
            },
        });
    }
    findings.sort_by_key(|finding| (finding.span.lo(), finding.span.hi()));
    Ok(findings)
}

fn meaningful(tcx: TyCtxt<'_>, field: LocalDefId) -> Option<LocalDefId> {
    let ty = tcx
        .type_of(field)
        .instantiate_identity()
        .skip_normalization();
    match ty.ty_adt_def() {
        Some(adt) if adt.is_phantom_data() => None,
        Some(adt)
            if let Some(name) = tcx.get_diagnostic_name(adt.did())
                && name.as_str() == "PhantomPinned" =>
        {
            None
        }
        _ => Some(field),
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Origin {
    Field(LocalDefId),
    Tuple(usize),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct Projection {
    origin: Origin,
    exposure: Exposure,
}

impl Projection {
    fn direct(field: LocalDefId) -> Self {
        Self {
            origin: Origin::Field(field),
            exposure: Exposure::Direct,
        }
    }

    fn member(self, part: Self) -> Self {
        match self.exposure {
            Exposure::Mutable | Exposure::Shared => Self {
                exposure: self.exposure,
                ..part
            },
            Exposure::Direct | Exposure::Value => part,
        }
    }

    fn passed_as(self, ty: ty::Ty<'_>) -> Operation {
        if let Origin::Tuple(_) = self.origin {
            return Operation::Pass;
        }
        let access = match ty.kind() {
            ty::Ref(_, _, Mutability::Mut) => Access::BorrowMut,
            ty::Ref(_, _, Mutability::Not) => Access::Borrow,
            _ => Access::Read,
        };
        Operation::Use(access)
    }
}

enum Output {
    Return(Projection),
    Set(Projection),
    Callback {
        parameter: usize,
        arguments: Vec<Projection>,
    },
}

enum Wrapper {
    Accessor {
        tuples: Vec<Vec<Projection>>,
        output: Output,
    },
    Forwarder,
}

fn wrapper<'tcx>(typeck: &TypeckResults<'tcx>, body: &Body<'tcx>) -> Option<Wrapper> {
    let (receiver, parameters) = body.params.split_first()?;
    let PatKind::Binding(_, receiver, _, _) = receiver.pat.kind else {
        return None;
    };
    let ExprKind::Block(block, _) = body.value.kind else {
        return None;
    };
    let (statements, tail) = match block.expr {
        Some(tail) => (block.stmts, tail),
        None => {
            let (last, preceding) = block.stmts.split_last()?;
            let StmtKind::Semi(tail) = last.kind else {
                return None;
            };
            (preceding, tail)
        }
    };
    let mut projections = Projections {
        typeck,
        receiver,
        bindings: FxHashMap::default(),
        tuples: Vec::new(),
    };
    for statement in statements {
        let StmtKind::Let(binding) = statement.kind else {
            return None;
        };
        let PatKind::Binding(_, id, _, None) = binding.pat.kind else {
            return None;
        };
        let value = projections.of(binding.init?)?;
        projections.bindings.insert(id, value);
    }
    let parameter = |expr: &Expr<'_>| {
        let id = local(typeck, expr)?;
        parameters.iter().position(|param| param.pat.hir_id == id)
    };
    let tail = tail.peel_drop_temps();
    if tail.span.from_expansion() {
        return None;
    }
    if let ExprKind::MethodCall(_, target, args, _) = tail.kind
        && let Some(_) = projections.of(target)
        && args.len() == parameters.len()
        && args
            .iter()
            .zip(parameters)
            .all(|(arg, param)| local(typeck, arg) == Some(param.pat.hir_id))
    {
        return Some(Wrapper::Forwarder);
    }
    let output = match tail.kind {
        ExprKind::Assign(place, value, _) => {
            parameter(value)?;
            Output::Set(projections.of(place)?)
        }
        ExprKind::Call(callee, arguments) => {
            let parameter = parameter(callee)?;
            let arguments = arguments
                .iter()
                .map(|arg| projections.of(arg))
                .collect::<Option<_>>()?;
            Output::Callback {
                parameter,
                arguments,
            }
        }
        ExprKind::Ret(Some(value)) => Output::Return(projections.of(value)?),
        _ => Output::Return(projections.of(tail)?),
    };
    Some(Wrapper::Accessor {
        tuples: projections.tuples,
        output,
    })
}

struct Projections<'a, 'tcx> {
    typeck: &'a TypeckResults<'tcx>,
    receiver: HirId,
    bindings: FxHashMap<HirId, Projection>,
    tuples: Vec<Vec<Projection>>,
}

impl Projections<'_, '_> {
    fn of(&mut self, expr: &Expr<'_>) -> Option<Projection> {
        if expr.span.from_expansion() {
            return None;
        }
        match expr.kind {
            ExprKind::Field(receiver, _) if local(self.typeck, receiver) == Some(self.receiver) => {
                let field = Field::projected(self.typeck, receiver, expr.hir_id)?
                    .def
                    .as_local()?;
                let exposure = match self.typeck.expr_ty(expr).kind() {
                    ty::Ref(_, _, Mutability::Mut) => Exposure::Mutable,
                    ty::Ref(_, _, Mutability::Not) => Exposure::Shared,
                    _ => Exposure::Value,
                };
                Some(Projection {
                    origin: Origin::Field(field),
                    exposure,
                })
            }
            ExprKind::AddrOf(_, mutability, inner) => {
                let exposure = match mutability {
                    Mutability::Mut => Exposure::Mutable,
                    Mutability::Not => Exposure::Shared,
                };
                Some(Projection {
                    exposure,
                    ..self.of(inner)?
                })
            }
            ExprKind::Path(_) => self.bindings.get(&local(self.typeck, expr)?).copied(),
            ExprKind::Tup(parts) => {
                let parts = parts
                    .iter()
                    .map(|part| self.of(part))
                    .collect::<Option<_>>()?;
                let index = self.tuples.len();
                self.tuples.push(parts);
                Some(Projection {
                    origin: Origin::Tuple(index),
                    exposure: Exposure::Value,
                })
            }
            _ => None,
        }
    }
}

struct Uses<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: &'tcx TypeckResults<'tcx>,
    def: LocalDefId,
    body: &'tcx Body<'tcx>,
    local_uses: OnceCell<FxHashMap<HirId, Vec<BindingUse<'tcx>>>>,
    caller: Option<LocalDefId>,
    method: Option<ty::AssocItem>,
    tangles: &'a Tangles,
    wrappers: &'a FxHashMap<LocalDefId, Wrapper>,
    working: &'a mut FxHashSet<LocalDefId>,
    outside: &'a mut FxHashMap<LocalDefId, Vec<(Site, &'static str)>>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Operation {
    Use(Access),
    Pass,
    Set,
}

#[derive(Clone, Copy)]
enum UseSite<'tcx> {
    Expression(&'tcx Expr<'tcx>),
    Pattern(&'tcx Pat<'tcx>),
    Binding(HirId, BytePos),
    Finish(Operation),
}

struct BindingUse<'tcx> {
    expr: &'tcx Expr<'tcx>,
    after_write: Option<BytePos>,
}

impl<'tcx> Uses<'_, 'tcx> {
    fn record(&mut self, field: LocalDefId, span: Span, access: Access) {
        if span.is_dummy() {
            return;
        }
        let Some(span) = diagnostics::source_span(self.tcx, self.def.to_def_id(), span) else {
            return;
        };
        let owner = self.tcx.local_parent(field);
        if let Some(caller) = self.caller {
            if owner == caller {
                if let Some(_) = self.method {
                    self.working.insert(owner);
                }
                return;
            }
            if let Some(_) = self.tangles.common_component(caller, owner) {
                return;
            }
        }
        let sites = self.outside.entry(field).or_default();
        if let Some(action) = access.action() {
            sites.push((
                Site {
                    def: self.def,
                    span,
                },
                action,
            ));
        }
    }

    fn binding_uses(&self, id: HirId) -> &[BindingUse<'tcx>] {
        struct Locals<'a, 'tcx> {
            tcx: TyCtxt<'tcx>,
            typeck: &'a TypeckResults<'tcx>,
            uses: FxHashMap<HirId, Vec<BindingUse<'tcx>>>,
            writes: FxHashMap<HirId, BytePos>,
            restore: Vec<(HirId, Option<BytePos>)>,
        }
        impl<'tcx> Visitor<'tcx> for Locals<'_, 'tcx> {
            fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
                if let ExprKind::Assign(place, rhs, _) = expr.kind
                    && let Some(id) = local(self.typeck, place)
                {
                    self.visit_expr(rhs);
                    if let Node::Stmt(_) | Node::Block(_) = self.tcx.parent_hir_node(expr.hir_id) {
                        let previous = self.writes.insert(id, expr.span.lo());
                        self.restore.push((id, previous));
                    }
                    return;
                }
                if !expr.span.from_expansion()
                    && let Some(id) = local(self.typeck, expr)
                {
                    self.uses.entry(id).or_default().push(BindingUse {
                        expr,
                        after_write: self.writes.get(&id).copied(),
                    });
                }
                if let ExprKind::Closure(closure) = expr.kind {
                    self.visit_body(self.tcx.hir_body(closure.body));
                }
                intravisit::walk_expr(self, expr);
            }
            fn visit_block(&mut self, block: &'tcx Block<'tcx>) {
                let start = self.restore.len();
                intravisit::walk_block(self, block);
                let writes = self.restore.drain(start..).rev();
                for (id, previous) in writes {
                    match previous {
                        Some(position) => {
                            self.writes.insert(id, position);
                        }
                        None => {
                            self.writes.remove(&id);
                        }
                    }
                }
            }
        }
        self.local_uses
            .get_or_init(|| {
                let mut locals = Locals {
                    tcx: self.tcx,
                    typeck: self.typeck,
                    uses: FxHashMap::default(),
                    writes: FxHashMap::default(),
                    restore: Vec::new(),
                };
                locals.visit_body(self.body);
                locals.uses
            })
            .get(&id)
            .map_or(&[], Vec::as_slice)
    }

    fn trace(
        &mut self,
        span: Span,
        tuples: &[Vec<Projection>],
        mut pending: Vec<(UseSite<'tcx>, Projection)>,
    ) {
        let mut visited = FxHashSet::default();
        let mut finished = FxHashSet::default();
        let mut accesses: FxHashMap<LocalDefId, Access> = FxHashMap::default();
        while let Some((site, value)) = pending.pop() {
            let next = match site {
                UseSite::Finish(operation) => {
                    if !finished.insert((value, operation)) {
                        continue;
                    }
                    match value.origin {
                        Origin::Tuple(index) => {
                            pending.extend(
                                tuples[index].iter().map(|&part| (site, value.member(part))),
                            );
                        }
                        Origin::Field(field) => {
                            let access = match (operation, value.exposure) {
                                (Operation::Set, _) => Access::Write,
                                (_, Exposure::Value) => Access::Read,
                                (Operation::Use(access), _) => access,
                                (Operation::Pass, Exposure::Mutable) => Access::BorrowMut,
                                (Operation::Pass, Exposure::Shared) => Access::Borrow,
                                (Operation::Pass, Exposure::Direct) => Access::Read,
                            };
                            let strongest = accesses.entry(field).or_insert(Access::Read);
                            *strongest = (*strongest).max(access);
                        }
                    }
                    continue;
                }
                UseSite::Binding(id, assigned) => {
                    let ty = self.typeck.node_type(id);
                    if !ty.is_ref()
                        && let Origin::Field(_) = value.origin
                    {
                        UseSite::Finish(Operation::Use(Access::Read))
                    } else {
                        let before = pending.len();
                        let uses = self.binding_uses(id).iter().filter(|usage| {
                            assigned <= usage.expr.span.lo()
                                && usage.after_write.is_none_or(|last| last <= assigned)
                        });
                        pending.extend(uses.map(|usage| (UseSite::Expression(usage.expr), value)));
                        if before != pending.len() {
                            continue;
                        }
                        match value.origin {
                            Origin::Field(_) => UseSite::Finish(value.passed_as(ty)),
                            Origin::Tuple(_) => UseSite::Finish(Operation::Use(Access::Read)),
                        }
                    }
                }
                UseSite::Pattern(pat) => {
                    if !visited.insert((pat.hir_id, value)) {
                        continue;
                    }
                    match pat.kind {
                        PatKind::Tuple(parts, rest) if let Origin::Tuple(index) = value.origin => {
                            let members = &tuples[index];
                            let parts = parts.iter().enumerate_and_adjust(members.len(), rest);
                            for (index, pat) in parts {
                                if let PatKind::Wild = pat.kind {
                                    continue;
                                }
                                pending.push((UseSite::Pattern(pat), value.member(members[index])));
                            }
                            continue;
                        }
                        PatKind::Binding(_, id, _, subpattern) => {
                            if let Some(subpattern) = subpattern {
                                pending.push((UseSite::Pattern(subpattern), value));
                            }
                            UseSite::Binding(id, pat.span.lo())
                        }
                        PatKind::Ref(inner, ..)
                        | PatKind::Deref(inner)
                        | PatKind::Guard(inner, _) => UseSite::Pattern(inner),
                        PatKind::Or(alternatives) => {
                            pending.extend(
                                alternatives
                                    .iter()
                                    .map(|pat| (UseSite::Pattern(pat), value)),
                            );
                            continue;
                        }
                        _ => UseSite::Finish(Operation::Use(Access::Read)),
                    }
                }
                UseSite::Expression(expr) => {
                    if !visited.insert((expr.hir_id, value)) {
                        continue;
                    }
                    let passed = || UseSite::Finish(value.passed_as(self.typeck.expr_ty(expr)));
                    match self.tcx.parent_hir_node(expr.hir_id) {
                        Node::LetStmt(binding) if let PatKind::Wild = binding.pat.kind => passed(),
                        Node::LetStmt(binding) => UseSite::Pattern(binding.pat),
                        Node::Expr(parent) => match parent.kind {
                            ExprKind::Assign(place, ..) | ExprKind::AssignOp(_, place, _)
                                if place.hir_id == expr.hir_id =>
                            {
                                UseSite::Finish(Operation::Use(Access::Write))
                            }
                            ExprKind::Assign(place, ..)
                                if let Some(id) = local(self.typeck, place) =>
                            {
                                UseSite::Binding(id, parent.span.lo())
                            }
                            ExprKind::AddrOf(_, Mutability::Mut, _) => {
                                UseSite::Finish(Operation::Use(Access::BorrowMut))
                            }
                            ExprKind::Index(place, ..) if place.hir_id == expr.hir_id => {
                                UseSite::Finish(Operation::Use(Access::Index))
                            }
                            ExprKind::MethodCall(_, receiver, ..)
                                if expr.hir_id == receiver.hir_id =>
                            {
                                let method = self.typeck.type_dependent_def_id(parent.hir_id);
                                UseSite::Finish(Operation::Use(self.method_access(method, expr)))
                            }
                            ExprKind::Call(callee, [receiver, ..])
                                if receiver.hir_id == expr.hir_id
                                    && let ExprKind::Path(ref path) = callee.kind
                                    && let Res::Def(_, def) =
                                        self.typeck.qpath_res(path, callee.hir_id)
                                    && let Some(item) = self.tcx.opt_associated_item(def)
                                    && item.is_method() =>
                            {
                                UseSite::Finish(Operation::Use(self.method_access(Some(def), expr)))
                            }
                            ExprKind::Match(subject, arms, _) if expr.hir_id == subject.hir_id => {
                                pending.extend(
                                    arms.iter().map(|arm| (UseSite::Pattern(arm.pat), value)),
                                );
                                continue;
                            }
                            ExprKind::Let(binding) => UseSite::Pattern(binding.pat),
                            ExprKind::Field(..) if let Origin::Tuple(index) = value.origin => {
                                let slot = self.typeck.field_index(parent.hir_id).as_usize();
                                let part = value.member(tuples[index][slot]);
                                pending.push((UseSite::Expression(parent), part));
                                continue;
                            }
                            ExprKind::Field(..)
                            | ExprKind::Unary(UnOp::Deref, _)
                            | ExprKind::DropTemps(_)
                            | ExprKind::AddrOf(..) => UseSite::Expression(parent),
                            _ => passed(),
                        },
                        _ => passed(),
                    }
                }
            };
            pending.push((next, value));
        }
        for (field, access) in accesses {
            let access = match access {
                Access::Borrow => self.borrow(field),
                other => other,
            };
            self.record(field, span, access);
        }
    }

    fn method_access(&self, method: Option<DefId>, receiver: &Expr<'_>) -> Access {
        let tcx = self.tcx;
        if let Some(def) = method {
            let method = tcx
                .opt_associated_item(def)
                .and_then(|item| item.trait_item_def_id())
                .unwrap_or(def);
            if tcx.lang_items().clone_fn() == Some(method)
                || tcx.is_diagnostic_item(sym::to_owned_method, method)
            {
                return Access::Read;
            }
            if let Some(adt) = crate::standard::inherent_adt(tcx, def) {
                let name = tcx.item_name(def);
                if tcx.lang_items().string() == Some(adt.did())
                    && let "as_bytes" | "as_str" = name.as_str()
                {
                    return Access::Borrow;
                }
                match (tcx.get_diagnostic_name(adt.did()), name.as_str()) {
                    (Some(sym::Cell), "get") | (Some(sym::Atomic), "load") => return Access::Read,
                    (Some(sym::Vec), "as_slice")
                    | (Some(sym::Option), "as_ref" | "as_deref" | "as_slice") => {
                        return Access::Borrow;
                    }
                    _ => {}
                }
            }
            if let Some(trait_id) = tcx.trait_of_assoc(method)
                && (tcx.is_diagnostic_item(sym::AsRef, trait_id)
                    || tcx.is_diagnostic_item(sym::Borrow, trait_id)
                    || Some(trait_id) == tcx.lang_items().deref_trait())
            {
                return Access::Borrow;
            }
        }
        let ty = self.typeck.expr_ty_adjusted(receiver);
        if let ty::Ref(_, _, Mutability::Mut) = ty.kind() {
            return Access::BorrowMut;
        }
        if ty.peel_refs().is_scalar() {
            return Access::Read;
        }
        Access::Call
    }

    fn borrow(&self, field: LocalDefId) -> Access {
        let ty = self
            .tcx
            .type_of(field)
            .instantiate_identity()
            .skip_normalization();
        let mut nested = vec![ty];
        let mut visited = FxHashSet::default();
        while let Some(ty) = nested.pop() {
            let ty = ty.peel_refs();
            if !visited.insert(ty) {
                continue;
            }
            match ty.kind() {
                ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) | ty::Str => {}
                ty::Slice(element) | ty::Array(element, _) => nested.push(*element),
                ty::Tuple(elements) => nested.extend(elements.iter()),
                ty::Adt(adt, _) if self.tcx.lang_items().string() == Some(adt.did()) => {}
                ty::Adt(adt, args)
                    if adt.is_box()
                        || self.tcx.is_diagnostic_item(sym::Vec, adt.did())
                        || self.tcx.is_diagnostic_item(sym::Option, adt.did()) =>
                {
                    nested.push(args.type_at(0));
                }
                _ => return Access::Borrow,
            }
        }
        Access::Read
    }
}

impl<'tcx> Visitor<'tcx> for Uses<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        let call = match expr.kind {
            ExprKind::Field(receiver, ident) => {
                if let Some(field) = Field::projected(self.typeck, receiver, expr.hir_id)
                    .and_then(|field| field.def.as_local())
                {
                    self.trace(
                        ident.span,
                        &[],
                        vec![(UseSite::Expression(expr), Projection::direct(field))],
                    );
                }
                None
            }
            ExprKind::MethodCall(segment, _, args, _) => self
                .typeck
                .type_dependent_def_id(expr.hir_id)
                .map(|def| (def, segment.ident.span, args)),
            ExprKind::Call(callee, args) if let ExprKind::Path(ref path) = callee.kind => {
                match self.typeck.qpath_res(path, callee.hir_id) {
                    Res::Def(DefKind::Ctor(CtorOf::Struct, _), ctor) if ctor.is_local() => {
                        let adt = self.tcx.adt_def(self.tcx.parent(ctor));
                        let fields = adt.non_enum_variant().fields.iter().zip(args);
                        for (field, arg) in fields {
                            self.record(field.did.expect_local(), arg.span, Access::Read);
                        }
                        None
                    }
                    Res::Def(_, def) => Some((def, path.span(), args.get(1..).unwrap_or_default())),
                    _ => None,
                }
            }
            ExprKind::Struct(_, fields, _) => {
                if let Some(adt) = self.typeck.expr_ty(expr).ty_adt_def()
                    && adt.is_struct()
                    && adt.did().is_local()
                {
                    for field in fields {
                        let id = adt.non_enum_variant().fields
                            [self.typeck.field_index(field.hir_id)]
                        .did
                        .expect_local();
                        self.record(id, field.ident.span, Access::Read);
                    }
                }
                None
            }
            _ => None,
        };
        if let Some((method, span, args)) = call
            && let Some(Wrapper::Accessor { tuples, output }) =
                method.as_local().and_then(|id| self.wrappers.get(&id))
        {
            let initial = match output {
                Output::Return(value) => vec![(UseSite::Expression(expr), *value)],
                Output::Set(place) => vec![(UseSite::Finish(Operation::Set), *place)],
                Output::Callback {
                    parameter,
                    arguments,
                } => {
                    let callback = &args[*parameter].peel_drop_temps();
                    let params = match callback.kind {
                        ExprKind::Closure(closure) => self.tcx.hir_body(closure.body).params,
                        _ => &[],
                    };
                    let mut initial = Vec::new();
                    let arguments = arguments.iter().enumerate();
                    for (index, &value) in arguments {
                        if let Some(param) = params.get(index) {
                            initial.push((UseSite::Pattern(param.pat), value));
                        }
                        if params.is_empty() || value.exposure == Exposure::Mutable {
                            initial.push((UseSite::Finish(Operation::Pass), value));
                        }
                    }
                    initial
                }
            };
            self.trace(span, tuples, initial);
        }
        intravisit::walk_expr(self, expr);
    }

    fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
        if let PatKind::Struct(..) | PatKind::TupleStruct(..) = pat.kind
            && let Some(ty) = self.typeck.node_type_opt(pat.hir_id)
            && let Some(adt) = ty.peel_refs().ty_adt_def()
            && adt.is_struct()
            && adt.did().is_local()
        {
            let fields = &adt.non_enum_variant().fields;
            let typeck = self.typeck;
            let mut record = |pat, id, span| {
                self.trace(
                    span,
                    &[],
                    vec![(UseSite::Pattern(pat), Projection::direct(id))],
                );
            };
            match pat.kind {
                PatKind::Struct(_, parts, _) => {
                    for part in parts {
                        let id = fields[typeck.field_index(part.hir_id)].did.expect_local();
                        record(part.pat, id, part.ident.span);
                    }
                }
                PatKind::TupleStruct(_, parts, rest) => {
                    let parts = parts.iter().enumerate_and_adjust(fields.len(), rest);
                    for (index, pat) in parts {
                        let field = fields.raw[index].did.expect_local();
                        record(pat, field, pat.span);
                    }
                }
                _ => {}
            }
        }
        intravisit::walk_pat(self, pat);
    }
}
