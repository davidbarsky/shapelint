mod field_leaks;
mod forwarded_fields;
mod tangles;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::{Expr, ExprKind, HirId};
use rustc_middle::ty::{self, Ty, TyCtxt, TypeckResults};
use rustc_span::{BytePos, Span};
use shapelint::{Label, LintError, Related};

use crate::diagnostics::{Located, Sources};

pub(crate) fn findings(tcx: TyCtxt<'_>, sources: &Sources) -> Result<Vec<Located>, LintError> {
    let tangles = tangles::Tangles::collect(tcx);
    let mut findings = tangles.findings(tcx, sources)?;
    findings.extend(field_leaks::findings(tcx, sources, &tangles)?);
    findings.extend(forwarded_fields::findings(tcx, sources)?);
    Ok(findings)
}

pub(crate) fn owner(tcx: TyCtxt<'_>, mut def: LocalDefId) -> Option<LocalDefId> {
    loop {
        match tcx.def_kind(def) {
            DefKind::Struct
            | DefKind::Enum
            | DefKind::Union
            | DefKind::Trait
            | DefKind::TraitAlias
            | DefKind::TyAlias
            | DefKind::Fn
            | DefKind::Const
            | DefKind::Static { nested: false, .. } => return Some(def),
            DefKind::Impl { .. } => {
                let ty = tcx.type_of(def).instantiate_identity().skip_normalization();
                return match ty.peel_refs().kind() {
                    ty::Adt(adt, _) => adt.did().as_local(),
                    ty::Dynamic(predicates, _) => {
                        predicates.principal_def_id().and_then(|id| id.as_local())
                    }
                    _ => None,
                }
                .or_else(|| tcx.impl_opt_trait_id(def)?.as_local());
            }
            DefKind::Variant
            | DefKind::Ctor(..)
            | DefKind::Field
            | DefKind::AssocFn
            | DefKind::AssocConst
            | DefKind::AssocTy
            | DefKind::Closure
            | DefKind::SyntheticCoroutineBody
            | DefKind::OpaqueTy
            | DefKind::Static { nested: true, .. }
            | DefKind::AnonConst => def = tcx.local_parent(def),
            _ => return None,
        }
    }
}

#[derive(Clone, Copy)]
pub(crate) struct Site {
    pub def: LocalDefId,
    pub span: Span,
}

impl Site {
    pub(crate) fn item_span(self, tcx: TyCtxt<'_>) -> Span {
        let owner = tcx.local_def_id_to_hir_id(self.def).owner;
        let enclosing = tcx.hir_span_with_body(owner.into()).source_callsite();
        let file = tcx.sess.source_map().lookup_source_file(self.span.lo());
        if file.contains(enclosing.lo()) && file.contains(enclosing.hi()) {
            enclosing
        } else {
            self.span
        }
    }

    pub(crate) fn related(
        self,
        tcx: TyCtxt<'_>,
        sources: &Sources,
        message: String,
    ) -> Result<Related, LintError> {
        let file = tcx.sess.source_map().lookup_source_file(self.span.lo());
        let related = Related {
            input: sources.input(&file)?,
            label: Label {
                span: shapelint::Span {
                    start: file.original_relative_byte_pos(self.span.lo()).0,
                    end: file.original_relative_byte_pos(self.span.hi()).0,
                },
                message,
            },
        };
        Ok(related)
    }
}

fn local(typeck: &TypeckResults<'_>, expr: &Expr<'_>) -> Option<HirId> {
    let ExprKind::Path(ref path) = expr.kind else {
        return None;
    };
    match typeck.qpath_res(path, expr.hir_id) {
        Res::Local(binding) => Some(binding),
        _ => None,
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
struct Field<'tcx> {
    owner: Ty<'tcx>,
    def: DefId,
}

impl<'tcx> Field<'tcx> {
    fn projected(
        typeck: &TypeckResults<'tcx>,
        receiver: &Expr<'_>,
        projection: HirId,
    ) -> Option<Self> {
        let owner = typeck.expr_ty_adjusted(receiver).peel_refs();
        let adt = owner.ty_adt_def()?;
        if !adt.is_struct() {
            return None;
        }
        let field = &adt.non_enum_variant().fields[typeck.opt_field_index(projection)?];
        Some(Self {
            owner,
            def: field.did,
        })
    }
}

fn visible_sites<T>(
    tcx: TyCtxt<'_>,
    sources: &Sources,
    suppressions: &mut FxHashMap<BytePos, shapelint::Suppressions>,
    rule: &str,
    mut sites: Vec<T>,
    location: impl Fn(&T) -> Site,
) -> Result<Vec<T>, LintError> {
    let source_map = tcx.sess.source_map();
    sites.sort_by_cached_key(|entry| {
        let site = location(entry);
        let file = source_map.lookup_source_file(site.span.lo());
        (
            file.name.prefer_local_unconditionally().to_string(),
            site.span.lo(),
            site.span.hi(),
        )
    });
    sites.dedup_by_key(|entry| {
        let site = location(entry);
        (site.span.lo(), site.span.hi())
    });
    let mut visible = Vec::new();
    for entry in sites {
        let site = location(&entry);
        let file = source_map.lookup_source_file(site.span.lo());
        let directives = match suppressions.entry(file.start_pos) {
            std::collections::hash_map::Entry::Occupied(index) => index.into_mut(),
            std::collections::hash_map::Entry::Vacant(index) => {
                index.insert(shapelint::rust_suppressions(&sources.input(&file)?)?)
            }
        };
        let line = |span: Span| {
            file.lookup_line(file.relative_position(span.lo()))
                .map_or(0, |index| index + 1)
        };
        if let None = directives.for_finding(rule, line(site.span), line(site.item_span(tcx))) {
            visible.push(entry);
        }
    }
    Ok(visible)
}
