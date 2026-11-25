use crate::Related;

#[derive(Clone, Copy)]
pub enum CheckOutcome {
    AlwaysTrue,
    AlwaysFalse,
}

impl std::fmt::Display for CheckOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::AlwaysTrue => "always true",
            Self::AlwaysFalse => "always false",
        })
    }
}

pub enum CompilerEvidence {
    SerializationDetour { origin: Related },
    BorrowedClone { uses: Vec<Related> },
    InvalidVariant { observed: String, required: String },
    UnencodedInvariant { guard: String, required: String },
}
