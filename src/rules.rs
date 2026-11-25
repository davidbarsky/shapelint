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
        id: "test-only-production-path",
        set: RuleSet::Mechanical,
        summary: "test cfg or tests under src create a separate production path",
    },
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
        id: "arbitrary-bound",
        set: RuleSet::Lints,
        summary: "literal bound lacks a named domain or resource constraint",
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
