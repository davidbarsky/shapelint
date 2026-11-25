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
    ModuleCycle {
        members: Vec<String>,
        first_edge: String,
        return_path: Vec<Related>,
    },
    Tangle {
        members: Vec<String>,
        first_edge: String,
        return_path: Vec<Related>,
    },
    FieldLeak {
        field: String,
        access: String,
        other_accesses: Vec<Related>,
    },
    ForwardedField {
        callee: String,
        owner: String,
        field: String,
        call_count: usize,
        decision: Related,
        other_calls: Vec<Related>,
    },

    PayloadPredicate {
        method: String,
    },
    Fallback {
        method: String,
    },
    SerializationDetour {
        origin: Related,
    },
    BorrowedClone {
        uses: Vec<Related>,
    },
    InvalidVariant {
        observed: String,
        required: String,
    },
    UnencodedInvariant {
        guard: String,
        required: String,
    },
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
    let label_sites = |mut report: Report, sites: &[Related]| {
        for site in sites {
            if site.input.name == input.name {
                report = report.label(site.label.span, &site.label.message);
            } else {
                report = report.related(site.clone());
            }
        }
        report
    };
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
            CompilerEvidence::ModuleCycle { members, first_edge, return_path } => {
                let report = Report::new(
                    format!("Sibling modules {} form a dependency cycle", members.join(", ")),
                    *span,
                    first_edge,
                ).help("Follow the labeled references to find the owner of the shared item. Move a dependency to that owner to break the cycle, or baseline the cycle if both directions are intentional.");
                ("module-cycle", label_sites(report, return_path))
            }
            CompilerEvidence::Tangle { members, first_edge, return_path } => {
                let report = Report::new(
                    format!("{} depend on one another in a cycle", members.join(", ")),
                    *span,
                    first_edge,
                ).help("Move the operation that needs both sides into one caller, or keep the items together if they form one abstraction.");
                ("tangle", label_sites(report, return_path))
            }
            CompilerEvidence::FieldLeak { field, access, other_accesses } => {
                let report = Report::new(
                    format!("code outside the owning type operates on `{field}`"),
                    *span,
                    access,
                ).help("Move the operation that needs this field onto its owning type.");
                ("field-leak", label_sites(report, other_accesses))
            }
            CompilerEvidence::ForwardedField { callee, owner, field, call_count, decision, other_calls } => {
                let calls = match call_count {
                    1 => format!("the only call to `{callee}` supplies"),
                    count => format!("all {count} calls to `{callee}` supply"),
                };
                let report = Report::new(
                    format!("{calls} `{owner}::{field}`"),
                    *span,
                    "forwarded unchanged",
                ).help(format!("Consider passing `&{owner}` to `{callee}` and reading `{field}` there."));
                let report = label_sites(report, std::slice::from_ref(decision));
                ("forwarded-field", label_sites(report, other_calls))
            }
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
