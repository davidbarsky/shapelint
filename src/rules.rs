//! Lint rules and optional compiler coverage diagnostics.

use serde::Serialize;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum Kind {
    /// Identifies source evidence for the caller to interpret in context.
    Lint,
    /// Describes a limit of the compiler analysis when explicitly requested.
    AnalysisGap,
}

impl Kind {
    pub fn label(self) -> &'static str {
        match self {
            Kind::Lint => "lint",
            Kind::AnalysisGap => "analysis-gap",
        }
    }
}

/// Selects which rules to report or use for an exit-status gate.
///
/// [`Self::Lints`] includes every rule selected by [`Self::Mechanical`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuleSet {
    Lints,
    Mechanical,
    AnalysisGaps,
}

impl RuleSet {
    pub fn select(self, rule: &Rule) -> Option<&Rule> {
        match self {
            Self::Lints => (rule.kind() == Kind::Lint).then_some(rule),
            Self::Mechanical | Self::AnalysisGaps => (self == rule.set).then_some(rule),
        }
    }
}

pub struct Rule {
    pub id: &'static str,
    set: RuleSet,
    pub summary: &'static str,
}

impl Rule {
    pub fn kind(&self) -> Kind {
        match self.set {
            RuleSet::Lints | RuleSet::Mechanical => Kind::Lint,
            RuleSet::AnalysisGaps => Kind::AnalysisGap,
        }
    }
}

pub const RULES: &[Rule] = &[
    Rule {
        id: "module-cycle",
        set: RuleSet::Lints,
        summary: "sibling modules depend on one another through resolved item references (compiler driver)",
    },
    Rule {
        id: "tangle",
        set: RuleSet::Lints,
        summary: "types or free items depend on one another in a cycle (compiler driver only)",
    },
    Rule {
        id: "field-leak",
        set: RuleSet::Lints,
        summary: "code outside a type operates directly on its internal fields (compiler driver only)",
    },
    Rule {
        id: "forwarded-field",
        set: RuleSet::Lints,
        summary: "every call forwards the same field to a private function that uses it to decide how to handle another input (compiler driver only)",
    },
    Rule {
        id: "correlated-state",
        set: RuleSet::Lints,
        summary: "constructed fields preserve an implication not encoded by their types",
    },
    Rule {
        id: "serialization-detour",
        set: RuleSet::Lints,
        summary: "typed data is serialized and reconstructed without crossing a boundary",
    },
    Rule {
        id: "unused-capability",
        set: RuleSet::Lints,
        summary: "all known callers supply the same parameter alternative",
    },
    Rule {
        id: "clone-only-to-borrow",
        set: RuleSet::Lints,
        summary: "a recognized clone only feeds shared read operations",
    },
    Rule {
        id: "discarded-validation",
        set: RuleSet::Lints,
        summary: "a validator establishes a condition that downstream code checks again",
    },
    Rule {
        id: "test-only-production-path",
        set: RuleSet::Mechanical,
        summary: "test cfg or tests under src create a separate production path",
    },
    Rule {
        id: "unnecessary-fallibility",
        set: RuleSet::Lints,
        summary: "every modeled normal return is Ok (compiler driver only)",
    },
    Rule {
        id: "unnecessary-optionality",
        set: RuleSet::Lints,
        summary: "all callers of a private parameter supply the optional payload (compiler driver only)",
    },
    Rule {
        id: "invalidated-validation",
        set: RuleSet::Lints,
        summary: "a mutation invalidates a consumer guarantee (compiler driver only)",
    },
    Rule {
        id: "duplicated-state",
        set: RuleSet::Lints,
        summary: "private fields encode the same state (compiler driver only)",
    },
    Rule {
        id: "loop-invariant-check",
        set: RuleSet::Lints,
        summary: "a loop repeats a check with unchanged inputs (compiler driver only)",
    },
    Rule {
        id: "equivalent-implementation",
        set: RuleSet::Lints,
        summary: "pure acyclic implementations have equivalent typed results (compiler driver only)",
    },
    Rule {
        id: "redundant-check",
        set: RuleSet::Lints,
        summary: "incoming facts already determine a source check's outcome (compiler driver only)",
    },
    Rule {
        id: "invalid-state-use",
        set: RuleSet::Lints,
        summary: "known values violate a consumer precondition (compiler driver only)",
    },
    Rule {
        id: "unencoded-precondition",
        set: RuleSet::Lints,
        summary: "public fields permit a consumer-precondition violation (compiler driver only)",
    },
    Rule {
        id: "unproven-precondition",
        set: RuleSet::AnalysisGaps,
        summary: "an unresolved requirement, shown with --show-analysis-gaps (compiler driver only)",
    },
    Rule {
        id: "analysis-incomplete",
        set: RuleSet::AnalysisGaps,
        summary: "an unsupported check, shown with --show-analysis-gaps (compiler driver only)",
    },
    Rule {
        id: "duplicate-control-flow",
        set: RuleSet::Lints,
        summary: "regions have matching typed early MIR (compiler driver only)",
    },
    Rule {
        id: "invalid-variant-access",
        set: RuleSet::Lints,
        summary: "variant extraction conflicts with incoming MIR facts (compiler driver only)",
    },
    Rule {
        id: "unencoded-state-invariant",
        set: RuleSet::Lints,
        summary: "a sibling-field guard does not prove a required variant (compiler driver only)",
    },
    Rule {
        id: "inconsistent-state-construction",
        set: RuleSet::Lints,
        summary: "returned fields contradict an inferred consumer invariant (compiler driver only)",
    },
    // Derived from the review packet (C01–C27).
    Rule {
        id: "shallow-helper",
        set: RuleSet::Lints,
        summary: "function body is one small expression with no branching (C15, C21, C22)",
    },
    Rule {
        id: "check-passthrough",
        set: RuleSet::Lints,
        summary: "fallible check that returns Ok(()) or its own inputs: parse, don't validate (C05, C16, C17, C25, C26)",
    },
    Rule {
        id: "option-plumbing",
        set: RuleSet::Lints,
        summary: "Option and its type arguments recur in a signature or absence flows through a call chain (C17, C18, C19)",
    },
    Rule {
        id: "json-in-domain",
        set: RuleSet::Lints,
        summary: "generic JSON imported, stored, returned, or constructed outside a boundary",
    },
    Rule {
        id: "config-bag",
        set: RuleSet::Lints,
        summary: "deserialized config re-parsed at use time, or a flattened String map (C03, C04)",
    },
    Rule {
        id: "unit-fields",
        set: RuleSet::Lints,
        summary: "field names share a stem and use different unit suffixes (C14)",
    },
    Rule {
        id: "identity-string",
        set: RuleSet::Lints,
        summary: "identity-like names (topic, source, destination, *_id) typed as strings (C09)",
    },
    Rule {
        id: "byte-format",
        set: RuleSet::Lints,
        summary: "byte format hand-assembled from to_*_bytes() and concat() (C27)",
    },
    Rule {
        id: "optional-state",
        set: RuleSet::Lints,
        summary: "methods re-prove that an Option field is Some (C13)",
    },
    Rule {
        id: "blocking-rationale",
        set: RuleSet::Lints,
        summary: "spawn_blocking without a comment naming what blocks (C10)",
    },
    Rule {
        id: "duration-comment",
        set: RuleSet::Mechanical,
        summary: "large duration literal in config without a human-unit comment (C06)",
    },
    Rule {
        id: "mapped-srcs",
        set: RuleSet::Mechanical,
        summary: "mapped_srcs in a Buck/Bazel file (C07)",
    },
    // Google Rust style guide, mechanical subset.
    Rule {
        id: "for-chain",
        set: RuleSet::Mechanical,
        summary: "iterator chain in a for-loop header, or for_each (Google)",
    },
    Rule {
        id: "tuple-return",
        set: RuleSet::Lints,
        summary: "tuple return type or wide tuple destructuring: prefer named fields (Google)",
    },
    Rule {
        id: "std-trait-fn",
        set: RuleSet::Mechanical,
        summary: "a free parse_* function accepts text and returns Result or Option (Google)",
    },
    Rule {
        id: "glob-import",
        set: RuleSet::Mechanical,
        summary: "glob import outside the allowed cases (Google)",
    },
    Rule {
        id: "import-alias",
        set: RuleSet::Mechanical,
        summary: "named use-import alias: use qualified paths instead",
    },
    Rule {
        id: "super-path",
        set: RuleSet::Mechanical,
        summary: "super outside use super::* in tests: use crate-qualified paths",
    },
    Rule {
        id: "matches-macro",
        set: RuleSet::Mechanical,
        summary: "matches! hides variant handling: use explicit patterns",
    },
    Rule {
        id: "option-result-predicate",
        set: RuleSet::Lints,
        summary: "a branch tests a variant and immediately extracts it from the same local (compiler driver only)",
    },
    Rule {
        id: "boolean-state",
        set: RuleSet::Lints,
        summary: "domain state expressed as boolean fields, parameters, or returns",
    },
    Rule {
        id: "error-erasure",
        set: RuleSet::Lints,
        summary: "fallible result discarded instead of preserving the error",
    },
    Rule {
        id: "silent-default",
        set: RuleSet::Lints,
        summary: "an error is replaced by a successful fallback of the same Result type (compiler driver only)",
    },
    Rule {
        id: "implicit-dependency",
        set: RuleSet::Lints,
        summary: "thread/task-local or global mutable context hides a dependency",
    },
    Rule {
        id: "conversion-trait",
        set: RuleSet::Lints,
        summary: "bespoke representation conversion resembles a standard trait",
    },
    Rule {
        id: "single-impl-trait",
        set: RuleSet::Lints,
        summary: "trait has only one implementation in the supplied sources",
    },
    Rule {
        id: "parallel-api",
        set: RuleSet::Lints,
        summary: "entry points with related names appear in the same scope",
    },
    Rule {
        id: "collection-choice",
        set: RuleSet::Lints,
        summary: "a collection path names BTreeMap or BTreeSet",
    },
    Rule {
        id: "literal-test-cases",
        set: RuleSet::Lints,
        summary: "test loops over fixed cases instead of reporting each case separately",
    },
    Rule {
        id: "primitive-test-actions",
        set: RuleSet::Lints,
        summary: "primitive random draws are decoded into domain actions",
    },
    Rule {
        id: "hegel-local-case-budget",
        set: RuleSet::Mechanical,
        summary: "Hegel test attribute overrides the local case budget",
    },
    Rule {
        id: "arbitrary-bound",
        set: RuleSet::Lints,
        summary: "literal bound lacks a named domain or resource constraint",
    },
    Rule {
        id: "hegel-scattered-draws",
        set: RuleSet::Lints,
        summary: "Hegel test draws separate inputs instead of one typed case",
    },
    Rule {
        id: "hegel-input-branch",
        set: RuleSet::Lints,
        summary: "test branches with if on a generated input",
    },
    Rule {
        id: "hegel-assume",
        set: RuleSet::Lints,
        summary: "Hegel assumption discards inputs instead of constructing the domain",
    },
    Rule {
        id: "hegel-generator-filter",
        set: RuleSet::Lints,
        summary: "generator filtering may work against shrinking and discard useful inputs",
    },
    Rule {
        id: "hegel-random-operation",
        set: RuleSet::Lints,
        summary: "applying a generated operation makes additional random choices",
    },
    Rule {
        id: "hegel-fixed-seed",
        set: RuleSet::Mechanical,
        summary: "Hegel test configures a local seed or derandomization policy",
    },
    Rule {
        id: "hegel-health-check",
        set: RuleSet::Lints,
        summary: "health-check suppression needs measurement or generator redesign",
    },
    Rule {
        id: "hegel-sampled-invariant",
        set: RuleSet::Lints,
        summary: "sampled invariant may miss a safety violation between steps",
    },
    Rule {
        id: "hegel-rule-weight",
        set: RuleSet::Lints,
        summary: "manual rule weighting changes the histories explored",
    },
    Rule {
        id: "hegel-early-exit",
        set: RuleSet::Lints,
        summary: "history stops observing the system after a rejected operation",
    },
    Rule {
        id: "redundant-comment",
        set: RuleSet::Lints,
        summary: "comment restates adjacent code or carries TODO/section scaffolding",
    },
    Rule {
        id: "compatibility-scaffolding",
        set: RuleSet::Lints,
        summary: "a call in a compatibility-named or deprecated function, a deprecated alias, or an alternate serialized field name",
    },
    Rule {
        id: "unknown-allow",
        set: RuleSet::Mechanical,
        summary: "`shapelint: allow(...)` names a rule that doesn't exist",
    },
];
