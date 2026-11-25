use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalModId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Body, BodyId, Expr, ExprKind, HirId, Item, ItemKind, OwnerId, Path, QPath};
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use shapelint_driver::diagnostics;

#[derive(Clone, Copy)]
pub(crate) struct Site {
    pub owner: OwnerId,
    pub span: Span,
}

pub(crate) struct References<'tcx> {
    tcx: TyCtxt<'tcx>,
    // A const expression in a field type has its own body under the struct's HIR owner.
    body: Option<BodyId>,
    edges: FxHashMap<(LocalModId, LocalModId), Site>,
}

impl<'tcx> References<'tcx> {
    pub(crate) fn collect(tcx: TyCtxt<'tcx>) -> FxHashMap<(LocalModId, LocalModId), Site> {
        let mut refs = Self {
            tcx,
            body: None,
            edges: FxHashMap::default(),
        };
        tcx.hir_visit_all_item_likes_in_crate(&mut refs);
        refs.edges
    }

    fn record(&mut self, id: HirId, target: DefId, span: Span) {
        if span.is_dummy() || span.from_expansion() {
            return;
        }
        let Some(target) = target.as_local() else {
            return;
        };
        let from = self.tcx.parent_module(id);
        let to = self.tcx.parent_module_from_def_id(target);
        if from == to || from.is_top_level_module() || to.is_top_level_module() {
            return;
        }
        let key = (from, to);
        if let Some(site) = self.edges.get(&key)
            && (site.span.lo(), site.span.hi()) <= (span.lo(), span.hi())
        {
            return;
        }
        if let Some(span) = diagnostics::source_span(self.tcx, id.owner.to_def_id(), span) {
            self.edges.insert(
                key,
                Site {
                    owner: id.owner,
                    span,
                },
            );
        }
    }
}

impl<'tcx> Visitor<'tcx> for References<'tcx> {
    type NestedFilter = OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        match item.kind {
            ItemKind::Use(..) | ItemKind::ExternCrate(..) => {}
            _ => intravisit::walk_item(self, item),
        }
    }

    fn visit_body(&mut self, body: &Body<'tcx>) {
        // Items nested in this body are visited independently by the crate item walker.
        if self
            .tcx
            .parent_module(body.value.hir_id)
            .is_top_level_module()
        {
            return;
        }
        let enclosing = self.body.replace(body.id());
        intravisit::walk_body(self, body);
        self.body = enclosing;
    }

    fn visit_path(&mut self, path: &Path<'tcx>, id: HirId) {
        if let Res::Def(kind, def) = path.res
            && let Some(segment) = path.segments.last()
        {
            match kind {
                DefKind::Mod | DefKind::Use | DefKind::ExternCrate => {}
                _ => self.record(id, def, segment.ident.span),
            }
        }
        intravisit::walk_path(self, path);
    }

    fn visit_qpath(&mut self, path: &'tcx QPath<'tcx>, id: HirId, _: Span) {
        if let QPath::TypeRelative(_, segment) = path
            && !segment.ident.span.from_expansion()
        {
            let types = match self.body {
                Some(body) => Some(self.tcx.typeck_body(body)),
                None if self.tcx.has_typeck_results(id.owner.def_id) => {
                    Some(self.tcx.typeck(id.owner.def_id))
                }
                None => None,
            };
            if let Some(def) = types.and_then(|types| types.type_dependent_def_id(id)) {
                self.record(id, def, segment.ident.span);
            }
        }
        intravisit::walk_qpath(self, path, id);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match (self.body, expr.kind) {
            (Some(body), ExprKind::MethodCall(segment, ..))
                if !segment.ident.span.from_expansion() =>
            {
                if let Some(def) = self
                    .tcx
                    .typeck_body(body)
                    .type_dependent_def_id(expr.hir_id)
                {
                    self.record(expr.hir_id, def, segment.ident.span);
                }
            }
            (Some(body), ExprKind::Field(receiver, ident)) if !ident.span.from_expansion() => {
                let typeck = self.tcx.typeck_body(body);
                if let Some(receiver) = typeck.expr_ty_adjusted_opt(receiver)
                    && let Some(adt) = receiver.ty_adt_def()
                {
                    self.record(expr.hir_id, adt.did(), ident.span);
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}
