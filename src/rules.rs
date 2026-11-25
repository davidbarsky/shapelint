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
