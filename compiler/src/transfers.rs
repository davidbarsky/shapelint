use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::stable_hash::{StableHash, StableHasher};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};

pub use crate::contracts::{Encoding, Serialized};
pub use crate::states::borrowed_clones;

#[derive(Clone, Copy)]
pub enum Codec {
    Encode(Encoding),
    Decode(Encoding),
}

pub fn codec(tcx: TyCtxt<'_>, def: DefId) -> Option<Codec> {
    if def.is_local() || tcx.crate_name(def.krate).as_str() != "serde_json" {
        return None;
    }
    match tcx.item_name(def).as_str() {
        "to_value" => Some(Codec::Encode(Encoding::Value)),
        "to_string" | "to_string_pretty" => Some(Codec::Encode(Encoding::Text)),
        "to_vec" | "to_vec_pretty" => Some(Codec::Encode(Encoding::Bytes)),
        "from_value" => Some(Codec::Decode(Encoding::Value)),
        "from_str" => Some(Codec::Decode(Encoding::Text)),
        "from_slice" => Some(Codec::Decode(Encoding::Bytes)),
        _ => None,
    }
}

pub fn fingerprint<'tcx>(tcx: TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Fingerprint {
    tcx.with_stable_hashing_context(|mut context| {
        let mut hasher = StableHasher::new();
        tcx.erase_and_anonymize_regions(ty)
            .stable_hash(&mut context, &mut hasher);
        hasher.finish()
    })
}
