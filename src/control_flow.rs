use crate::diagnostic::{Report, Sink};
use crate::{Config, Finding, Related, SourceInput, Span, suppress};

pub struct CompilerFinding {
    pub item: String,
    pub item_span: Span,
    pub span: Span,
    pub evidence: CompilerEvidence,
}

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
    PayloadPredicate { method: String },
    Fallback { method: String },
    SerializationDetour { origin: Related },
    BorrowedClone { uses: Vec<Related> },
    InvalidVariant { observed: String, required: String },
    UnencodedInvariant { guard: String, required: String },
}

/// Applies source suppression and diagnostic policy to compiler evidence.
///
/// Both the item and primary spans must be valid UTF-8 byte ranges in `input`.
/// An invalid range returns [`crate::LintError::InvalidSpan`] even if a suppression
/// covers the finding.
pub fn lint_compiler(
    input: &SourceInput,
    config: &Config,
    findings: &[CompilerFinding],
) -> Result<Vec<Finding>, crate::LintError> {
    let suppressions = suppress::rust_suppressions(input)?;
    let mut sink = Sink::new(input, config, &suppressions);
    for CompilerFinding {
        item,
        item_span,
        span,
        evidence,
    } in findings
    {
        input
            .as_ref()
            .get(std::ops::Range::from(*span))
            .ok_or_else(|| crate::LintError::InvalidSpan {
                name: input.name.to_string(),
                span: *span,
            })?;
        let (rule, report) = match evidence {
            CompilerEvidence::PayloadPredicate { method } => (
                "option-result-predicate",
                Report::new(
                    format!("`{method}` tests a variant that this branch immediately extracts"),
                    *span,
                    "the branch extracts the same local",
                )
                .help("Bind the payload or error in the pattern and use that binding in the branch."),
            ),
            CompilerEvidence::Fallback { method } => (
                "silent-default",
                Report::new(
                    format!("`{method}` replaces an error with a successful fallback"),
                    *span,
                    "this error becomes Ok",
                )
                .help("Use the original Result here to preserve the error. If this boundary always supplies a fallback, carry the plain payload in its API."),
            ),
            _ => continue,
        };
        sink.emit(rule, *item_span, item, report);
    }
    sink.finish()
}
