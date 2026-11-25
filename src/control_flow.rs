use crate::Related;

pub enum CompilerEvidence {
    SerializationDetour { origin: Related },
    BorrowedClone { uses: Vec<Related> },
    InvalidVariant { observed: String, required: String },
    UnencodedInvariant { guard: String, required: String },
}
