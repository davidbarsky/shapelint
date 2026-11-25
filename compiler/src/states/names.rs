use crate::values::StoreValue;
use std::sync::Arc;

use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::DefId;
use rustc_index::IndexVec;
use rustc_middle::mir::{Body, Local, Place, ProjectionElem, VarDebugInfoContents};
use rustc_middle::ty::{self, Ty, TyCtxt};
use rustc_span::{Span, Symbol};

use crate::contracts::{Identity, Origin};
use crate::diagnostics::{ExpressionKind, OwnerSource, Sources};
use crate::states::places::{Paths, Places};

struct DebugName {
    name: Symbol,
    adt: Option<DefId>,
}

struct LocalName<'tcx> {
    span: Span,
    ty: Ty<'tcx>,
}

pub(crate) struct Names<'tcx, 's, 'g> {
    def: DefId,
    locals: IndexVec<Local, LocalName<'tcx>>,
    debug: Places<'tcx, 's>,
    labels: FxHashMap<Place<'tcx>, DebugName>,
    pub(crate) source: Arc<OwnerSource>,
    origins: FxHashMap<Place<'tcx>, (crate::values::OriginId<'g>, usize)>,
}

impl<'tcx, 's, 'g> Names<'tcx, 's, 'g> {
    pub(crate) fn try_new(
        tcx: TyCtxt<'tcx>,
        body: &Body<'tcx>,
        sources: &Sources,
        paths: &mut Paths<'tcx, 's>,
    ) -> Result<Self, crate::contracts::graph::CapacityError> {
        let def = body.source.def_id();
        let owner = tcx.local_def_id_to_hir_id(def.expect_local()).owner;
        let mut names = Self {
            def,
            locals: body
                .local_decls
                .iter()
                .map(|local| LocalName {
                    span: local.source_info.span,
                    ty: local.ty,
                })
                .collect(),
            debug: Places::default(),
            labels: FxHashMap::default(),
            source: sources.owner(tcx, owner),
            origins: FxHashMap::default(),
        };
        for variable in &body.var_debug_info {
            let VarDebugInfoContents::Place(place) = variable.value else {
                continue;
            };
            if let Some(label) = names.labels.get_mut(&place) {
                label.name = variable.name;
                continue;
            }
            let adt = match place.ty(&body.local_decls, tcx).ty.peel_refs().kind() {
                ty::Adt(adt, _) => Some(adt.did()),
                _ => None,
            };
            paths.insert(&mut names.debug, place, place)?;
            names.labels.insert(
                place,
                DebugName {
                    name: variable.name,
                    adt,
                },
            );
        }
        Ok(names)
    }
}

impl<'tcx, 's, 'g> Names<'tcx, 's, 'g> {
    pub(crate) fn origin(
        &mut self,
        tcx: TyCtxt<'tcx>,
        place: Place<'tcx>,
        paths: &Paths<'tcx, 's>,
        graph: &mut crate::contracts::graph::Graph<'g>,
    ) -> Result<(crate::values::OriginId<'g>, usize), crate::contracts::graph::CapacityError> {
        if let Some(origin) = self.origins.get(&place) {
            return Ok(*origin);
        }
        let local = &self.locals[place.local];
        let (name, value, adt) = match paths.ancestors(&self.debug, place).last() {
            Some(value) => {
                let DebugName { name, adt } = self.labels[value];
                (Some(name.to_string()), *value, adt)
            }
            None => {
                let expression = self.source.expressions.get(&local.span);
                let (value, ty) = match (expression, local.ty.kind(), &place.projection[..]) {
                    (
                        Some(expression),
                        ty::Tuple(types),
                        [ProjectionElem::Field(field, field_ty)],
                    ) if let ExpressionKind::Binary = expression.expression_kind
                        && field.index() == 0
                        && let [_, overflow] = types.as_slice()
                        && overflow.is_bool() =>
                    {
                        (place, *field_ty)
                    }
                    _ => (Place::from(place.local), local.ty),
                };
                let adt = match ty.peel_refs().kind() {
                    ty::Adt(adt, _) => Some(adt.did()),
                    _ => None,
                };
                (
                    expression.map(|expression| expression.text(tcx).to_owned()),
                    value,
                    adt,
                )
            }
        };
        let origin = Origin {
            def: self.def,
            name,
            adt,
            identity: match value.projection.len() {
                0 => Some(Identity {
                    origin: (self.def, value.local),
                    fields: Vec::new(),
                    calls: Vec::new(),
                }),
                _ => None,
            },
        };
        let origin = graph.intern_value(&origin)?;
        let result = (origin, value.projection.len());
        self.origins.insert(place, result);
        Ok(result)
    }
}
