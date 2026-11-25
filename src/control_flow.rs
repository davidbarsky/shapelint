use crate::diagnostic::{Report, Sink};
use crate::suppress;
use crate::{Config, Finding, Related, SourceInput, Span};

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
    SerializationDetour {
        origin: Related,
    },
    BorrowedClone {
        uses: Vec<Related>,
    },
    DiscardedValidation {
        condition: String,
        origin: Related,
    },
    InvalidatedValidation {
        condition: String,
        mutation: Related,
    },
    RedundantCheck {
        condition: String,
        outcome: CheckOutcome,
        established: String,
        origin: Option<Related>,
    },
    PayloadPredicate {
        method: String,
    },
    Fallback {
        method: String,
    },
    InvalidPrecondition {
        operation: String,
        requirement: String,
        origin: Option<Related>,
    },
    UnencodedPrecondition {
        owner: String,
        consumer: String,
        requirement: String,
        witness: String,
    },
    UnprovenPrecondition {
        explanation: String,
        operation: String,
        requirement: String,
        origin: Option<Related>,
    },
    AnalysisIncomplete {
        operation: String,
        origin: Related,
    },
    Duplicate {
        original: Related,
    },
    InvalidVariant {
        observed: String,
        required: String,
    },
    UnencodedInvariant {
        guard: String,
        required: String,
    },
    InconsistentConstruction {
        assumption: String,
        consumer: String,
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
            CompilerEvidence::SerializationDetour { origin } => ("serialization-detour", Report::new("a typed value is serialized and immediately reconstructed", *span, "deserializes back into the original type")
                .related(origin.clone())
                .note("The serialized value reaches this decoder without an intervening mutation or external operation.")
                .help("Pass the typed value directly unless this conversion deliberately normalizes data or tests a codec contract.")),
            CompilerEvidence::BorrowedClone { uses } => {
                let mut report = Report::new("this clone is used only through shared borrows", *span, "the original value can supply these reads")
                    .note("Recognized buffer or handle cloning feeds only modeled read operations; no automatic rewrite is applied.")
                    .help("Borrow the original value instead of creating a temporary clone.");
                for usage in uses { report = report.related(usage.clone()); }
                ("clone-only-to-borrow", report)
            }
            CompilerEvidence::DiscardedValidation { condition, origin } => ("discarded-validation", Report::new("an earlier validator already establishes this recovery condition", *span, condition)
                .related(origin.clone())
                .help("Return a value that carries the validated invariant and consume it without revalidation.")),
            CompilerEvidence::InvalidatedValidation { condition, mutation } => ("invalidated-validation", Report::new("a mutation invalidated the earlier validation", *span, format!("requires {condition} after the mutation"))
                .related(mutation.clone())
                .note("This identifies a lost guarantee, not proof that the operation fails.")
                .help("Establish the requirement after the mutation, or move the mutation before validation.")),
            CompilerEvidence::RedundantCheck { condition, outcome, established, origin } => {
                let mut report = Report::new("incoming facts already decide this check", *span, format!("{condition}: {outcome}"))
                    .note(established)
                    .help("Keep validation at the boundary that owns the requirement; preserve any evaluation effects when simplifying.");
                if let Some(origin) = origin {
                    report = report.related(origin.clone())
                        .note("This conclusion applies to this call. Other callers may still need the callee's check.");
                }
                ("redundant-check", report)
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
            CompilerEvidence::InvalidPrecondition { operation, requirement, origin: _ } => (
                "invalid-state-use", Report::new(operation, *span, requirement)
                    .help("Correct the construction or transition before this operation."),
            ),
            CompilerEvidence::UnencodedPrecondition { owner, consumer, requirement, witness } => (
                "unencoded-precondition",
                Report::new(format!("`{owner}` permits values that violate a consumer requirement"), *span, format!("requires {requirement}"))
                    .note(format!("Representable counterexample: {witness}"))
                    .note(format!("Required by {consumer}"))
                    .note("This compares representable fields with the consumer requirement; it does not prove a reachable violating call.")
                    .help("Own the relationship in a constructor with private fields or a narrower type."),
            ),
            CompilerEvidence::UnprovenPrecondition { explanation, operation, requirement, origin: _ } => (
                "unproven-precondition", Report::new(operation, *span, requirement)
                    .note(explanation)
                    .note("Shapelint has not established that this operation fails."),
            ),
            CompilerEvidence::AnalysisIncomplete { operation, origin } => (
                "analysis-incomplete",
                Report::new("shapelint could not analyze this check", *span, operation)
                    .related(origin.clone())
                    .note("This reports a limitation of shapelint, not a defect in this code."),
            ),
            CompilerEvidence::Duplicate { original } => (
                "duplicate-control-flow",
                Report::new("regions have matching typed control flow", *span, "appears to duplicate the implementation above")
                    .related(original.clone())
                    .note("Compared before MIR optimization, including execution, cleanup, and suspension edges.")
                    .help("Consider moving the shared operation into one implementation."),
            ),
            CompilerEvidence::InvalidVariant { observed, required } => (
                "invalid-variant-access",
                Report::new("variant extraction conflicts with the incoming MIR facts", *span, required)
                    .note(format!("Known incoming state: {observed}"))
                    .help("Handle the actual variant or correct the transition that produced it."),
            ),
            CompilerEvidence::UnencodedInvariant { guard, required } => (
                "unencoded-state-invariant",
                Report::new("a sibling-field guard does not establish the required variant", *span, required)
                    .note(format!("Guarded state: {guard}"))
                    .note("This is an inferred consumer assumption, not a declared domain invariant.")
                    .help("Put the payload in the state variant, or match the payload at the boundary."),
            ),
            CompilerEvidence::InconsistentConstruction { assumption, consumer } => (
                "inconsistent-state-construction",
                Report::new("returned fields contradict an observed consumer assumption", *span, assumption)
                    .note(format!("Consumer requiring this relationship: {consumer}"))
                    .note("The relationship is inferred from that consumer; this is not a proof of a reachable domain bug.")
                    .help("Unify construction and consumption around a type that encodes the relationship."),
            ),
        };
        let origin = match evidence {
            CompilerEvidence::InvalidPrecondition { origin, .. }
            | CompilerEvidence::UnprovenPrecondition { origin, .. } => origin.as_ref(),
            _ => None,
        };
        let report = match origin {
            Some(origin) => report.related(origin.clone()),
            None => report,
        };
        sink.emit(rule, *item_span, item, report);
    }
    sink.finish()
}
