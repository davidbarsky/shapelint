//! shapelint: design linting and diagnostics for Rust, TOML, and Buck/Bazel files.
//!
//! This crate performs no filesystem, terminal, or environment access. Input is a
//! [`SourceInput`] (a name and its text) plus a [`Config`]; output is [`Finding`]s,
//! which [`render`] turns into text. The `shapelint` binary owns all I/O.

#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_lexer;
extern crate rustc_parse;
extern crate rustc_session;
extern crate rustc_span;

mod config;
mod control_flow;
mod diagnostic;
mod rules;
mod rust_syntax;
mod source;
mod suggest;
mod suppress;
mod text_rules;
mod text_syntax;

pub use config::{
    CONFIG_KEYS, Config, ConfigParse, ConfigWarning, PathPattern, SourceMode, Thresholds,
};
pub use control_flow::{CheckOutcome, CompilerEvidence};
pub use diagnostic::{Finding, Footer, Label, Related, Style, render};
pub use rules::{Kind, RULES, Rule, RuleSet};
pub use source::{LintError, SourceInput, Span};
pub use suppress::{Suppressions, rust_suppressions};

/// File kinds shapelint understands, decided by name alone.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Language {
    Rust,
    Toml,
    Starlark,
}

impl Language {
    pub fn of(name: &str) -> Option<Language> {
        let file = match name.rsplit(['/', '\\']).next() {
            Some(file) => file,
            None => name,
        };
        if file.ends_with(".rs") {
            Some(Language::Rust)
        } else if file.ends_with(".toml") {
            Some(Language::Toml)
        } else if ["BUCK", "BUCK.v2", "TARGETS", "BUILD", "BUILD.bazel"].contains(&file)
            || file.ends_with(".bzl")
        {
            Some(Language::Starlark)
        } else {
            None
        }
    }
}

/// Parsing and visiting nested syntax consumes stack proportional to token count.
const STACK_BASE: usize = 8 << 20;
// Both profiles use the same prebuilt rustc parser for nested blocks.
const STACK_PER_TOKEN: usize = 4 << 10;

pub fn lint(input: &SourceInput, config: &Config) -> Result<Vec<Finding>, LintError> {
    let findings = lint_sources(std::slice::from_ref(input), config)?;
    Ok(findings.into_iter().flatten().collect())
}

pub fn lint_sources(
    inputs: &[SourceInput],
    config: &Config,
) -> Result<Vec<Vec<Finding>>, LintError> {
    let threads = std::thread::available_parallelism()
        .map_or(1, usize::from)
        .min(inputs.len().max(1));
    let chunk_size = inputs.len().div_ceil(threads).max(1);
    let analyses = std::thread::scope(|scope| {
        let handles: Vec<_> = inputs
            .chunks(chunk_size)
            .map(|chunk| {
                scope.spawn(move || {
                    chunk
                        .iter()
                        .map(|input| analyze(input, config))
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        handles
            .into_iter()
            .flat_map(|handle| match handle.join() {
                Ok(results) => results,
                Err(panic) => std::panic::resume_unwind(panic),
            })
            .collect::<Result<Vec<_>, _>>()
    })?;
    Ok(analyses)
}

fn analyze(input: &SourceInput, config: &Config) -> Result<Vec<Finding>, LintError> {
    let Some(language) = Language::of(&input.name) else {
        return Ok(Vec::new());
    };
    if language != Language::Rust {
        return lint_here(input, config, language);
    }
    // The lexer is iterative, so counting tokens is safe at any depth.
    let tokens = rustc_lexer::tokenize(input.as_ref(), rustc_lexer::FrontmatterAllowed::No).count();
    let stack_bytes = STACK_BASE.saturating_add(tokens.saturating_mul(STACK_PER_TOKEN));
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .name("shapelint-parse".into())
            .stack_size(stack_bytes)
            .spawn_scoped(scope, || lint_here(input, config, language))
            .map_err(|source| LintError::NoStack {
                name: input.name.to_string(),
                stack_bytes,
                source,
            })?;
        // A panic here is a bug in shapelint; surface it unchanged.
        match worker.join() {
            Ok(analysis) => analysis,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    })
}

fn lint_here(
    input: &SourceInput,
    config: &Config,
    language: Language,
) -> Result<Vec<Finding>, LintError> {
    match language {
        Language::Rust => rust_syntax::parse(input, || {
            let suppressions = rust_suppressions(input)?;
            let mut sink = diagnostic::Sink::new(input, config, &suppressions);
            sink.report_unknown();
            sink.finish()
        })?,
        Language::Toml | Language::Starlark => {
            let tokens = text_syntax::lex(input.as_ref(), language);
            let suppressions = suppress::scan_hash_comments(input, &tokens)?;
            let mut sink = diagnostic::Sink::new(input, config, &suppressions);
            match language {
                Language::Toml => text_rules::lint_toml(&mut sink, &tokens, input, config),
                Language::Starlark => text_rules::lint_starlark(&mut sink, &tokens, input.as_ref()),
                Language::Rust => unreachable!(),
            }
            sink.report_unknown();
            sink.finish()
        }
    }
}
