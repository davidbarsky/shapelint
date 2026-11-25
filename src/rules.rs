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
        id: "unknown-allow",
        set: RuleSet::Mechanical,
        summary: "`shapelint: allow(...)` names a rule that doesn't exist",
    },
];
