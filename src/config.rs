use std::path::PathBuf;
use std::str::FromStr;

use crate::RuleSet;
use crate::suggest::{Code, suggest};

/// Numeric thresholds. Every rule always runs; these only move where it fires.
#[derive(Clone, Debug)]
pub struct Thresholds {
    /// shallow-helper: largest single-expression body (syntax nodes) still called shallow.
    pub shallow_max_nodes: usize,
    /// for-chain: chained method calls in a `for` header before it fires.
    pub for_chain_min_calls: usize,
    /// tuple-return: tuple width in a return type before it fires.
    pub tuple_return_min_width: usize,
    /// tuple-return: tuple width in a `let` destructuring before it fires.
    pub tuple_destructure_min_width: usize,
    /// byte-format: `to_*_bytes()` pieces in one `[..].concat()` before it fires.
    pub byte_format_min_pieces: usize,
    /// identity-string: identity-named string fields in one struct before it fires.
    pub identity_fields_min: usize,
    /// duration-comment: smallest duration (hours) that needs a human-unit comment.
    pub duration_comment_min_hours: usize,
    /// blocking-rationale: lines above `spawn_blocking` searched for a comment.
    pub blocking_comment_lines: usize,
    /// `with_source`: lines of the enclosing item included.
    pub source_lines: usize,
}

impl Default for Thresholds {
    fn default() -> Self {
        Thresholds {
            shallow_max_nodes: 40,
            for_chain_min_calls: 2,
            tuple_return_min_width: 3,
            tuple_destructure_min_width: 4,
            byte_format_min_pieces: 2,
            identity_fields_min: 2,
            duration_comment_min_hours: 1,
            blocking_comment_lines: 3,
            source_lines: 60,
        }
    }
}

/// Every key `.shapelint` accepts.
pub const CONFIG_KEYS: &[&str] = &[
    "exclude",
    "json-boundary",
    "shallow-max-nodes",
    "for-chain-min-calls",
    "tuple-return-min-width",
    "tuple-destructure-min-width",
    "byte-format-min-pieces",
    "identity-fields-min",
    "duration-comment-min-hours",
    "blocking-comment-lines",
    "source-lines",
];

/// Controls whether findings include their enclosing source item.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SourceMode {
    #[default]
    Omit,
    Include,
}

/// Matches a full source path as a glob, or a literal substring when no glob syntax is present.
/// Glob `*` and `?` do not cross directory separators; `**` spans directories.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathPattern {
    Substring(String),
    Glob(glob::Pattern),
}

impl FromStr for PathPattern {
    type Err = glob::PatternError;

    fn from_str(pattern: &str) -> Result<Self, Self::Err> {
        if pattern.contains(['*', '?', '[', ']']) {
            Ok(Self::Glob(pattern.parse()?))
        } else {
            Ok(Self::Substring(pattern.into()))
        }
    }
}

impl std::fmt::Display for PathPattern {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Substring(pattern) => pattern.fmt(formatter),
            Self::Glob(pattern) => pattern.fmt(formatter),
        }
    }
}

#[derive(Clone, Debug, Default)]
pub struct Config {
    /// Literal paths excluded by the CLI, relative to the `.shapelint` directory.
    /// The library's single-source `lint` function does not apply exclusions.
    pub exclude: Vec<PathBuf>,
    /// Case-sensitive path patterns exempt from `json-in-domain`.
    pub json_boundary: Vec<PathPattern>,
    /// Limits reporting to the selected rules.
    pub only: Option<RuleSet>,
    /// Controls whether the enclosing item's text is attached to each finding.
    pub with_source: SourceMode,
    pub t: Thresholds,
}

/// A problem in `.shapelint`, at a 1-based line. Invalid settings or patterns are ignored.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConfigWarning {
    pub line: usize,
    pub message: String,
}

pub struct ConfigParse {
    pub config: Config,
    pub warnings: Vec<ConfigWarning>,
}

impl Config {
    pub(crate) fn json_boundary(&self, path: &str) -> Option<&PathPattern> {
        self.json_boundary.iter().find(|pattern| match pattern {
            PathPattern::Substring(pattern) => path.contains(pattern),
            PathPattern::Glob(pattern) => pattern.matches_with(
                path,
                glob::MatchOptions {
                    case_sensitive: true,
                    require_literal_separator: true,
                    require_literal_leading_dot: false,
                },
            ),
        })
    }

    /// Parses `.shapelint` text: `key = value` lines, `#` starts a comment.
    pub fn parse(text: &str) -> ConfigParse {
        let mut config = Config::default();
        let mut warnings = Vec::new();
        let lines = (1..).zip(text.lines());
        for (number, raw) in lines {
            let line = match raw.split_once('#') {
                Some((line, _)) => line.trim(),
                None => raw.trim(),
            };
            if line.is_empty() {
                continue;
            }
            let warn = |message: String| ConfigWarning {
                line: number,
                message,
            };
            let Some((key, value)) = line.split_once('=') else {
                warnings.push(warn(format!(
                    "expected `key = value`, found {}",
                    Code(line)
                )));
                continue;
            };
            let (key, value) = (key.trim(), value.trim());
            if key == "exclude" {
                config.exclude.extend(
                    value
                        .split(',')
                        .map(str::trim)
                        .filter(|v| !v.is_empty())
                        .map(PathBuf::from),
                );
                continue;
            }
            if key == "json-boundary" {
                let patterns = value
                    .split(',')
                    .map(str::trim)
                    .filter(|value| !value.is_empty());
                for pattern in patterns {
                    match pattern.parse() {
                        Ok(pattern) => config.json_boundary.push(pattern),
                        Err(error) => warnings.push(warn(format!(
                            "invalid `json-boundary` pattern {}: {error}",
                            Code(pattern)
                        ))),
                    }
                }
                continue;
            }
            let t = &mut config.t;
            let slot = match key {
                "shallow-max-nodes" => &mut t.shallow_max_nodes,
                "for-chain-min-calls" => &mut t.for_chain_min_calls,
                "tuple-return-min-width" => &mut t.tuple_return_min_width,
                "tuple-destructure-min-width" => &mut t.tuple_destructure_min_width,
                "byte-format-min-pieces" => &mut t.byte_format_min_pieces,
                "identity-fields-min" => &mut t.identity_fields_min,
                "duration-comment-min-hours" => &mut t.duration_comment_min_hours,
                "blocking-comment-lines" => &mut t.blocking_comment_lines,
                "source-lines" => &mut t.source_lines,
                "disable" => {
                    warnings.push(warn("`disable` is not supported: every rule runs; change a threshold, or add `// shapelint: allow(<rule>)` at the site".into()));
                    continue;
                }
                other => {
                    let hint = match suggest(other, CONFIG_KEYS.iter().copied()) {
                        Some(k) => format!("; did you mean {}?", Code(k)),
                        None => String::new(),
                    };
                    warnings.push(warn(format!("unknown key {}{hint}", Code(other))));
                    continue;
                }
            };
            match value.parse() {
                Ok(n) => *slot = n,
                Err(_) => warnings.push(warn(format!(
                    "{} needs a whole number, found {}",
                    Code(key),
                    Code(value)
                ))),
            }
        }
        ConfigParse { config, warnings }
    }
}
