use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::sym;

pub enum OptionOrResult {
    Option,
    Result,
}

pub fn method_owner(tcx: TyCtxt<'_>, def: DefId) -> Option<OptionOrResult> {
    let adt = inherent_adt(tcx, def)?;
    if tcx.is_diagnostic_item(sym::Option, adt.did()) {
        Some(OptionOrResult::Option)
    } else if tcx.is_diagnostic_item(sym::Result, adt.did()) {
        Some(OptionOrResult::Result)
    } else {
        None
    }
}

pub(crate) fn vec_push(tcx: TyCtxt<'_>, def: DefId) -> Option<()> {
    if tcx.opt_item_name(def)?.as_str() != "push" {
        return None;
    }
    tcx.is_diagnostic_item(sym::Vec, inherent_adt(tcx, def)?.did())
        .then_some(())
}

pub(crate) fn inherent_adt<'tcx>(tcx: TyCtxt<'tcx>, def: DefId) -> Option<ty::AdtDef<'tcx>> {
    let owner = tcx.inherent_impl_of_assoc(def)?;
    let ty::Adt(adt, _) = *tcx
        .type_of(owner)
        .instantiate_identity()
        .skip_normalization()
        .kind()
    else {
        return None;
    };
    Some(adt)
}
