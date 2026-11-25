#![feature(rustc_private)]

//! Generated tests over the whole linter, and the test-only models they compare against.
//! Oracles here never call shapelint code.

use hegel::generators::{self, BoxedPrintableGenerator, DefaultGenerator, Generator};
use hegel::{PrintableGenerator, TestCase};

#[derive(Debug, PartialEq, Eq)]
struct Position {
    line: usize,
    col: usize,
}
use shapelint::{Config, Finding, Footer, Kind, RULES, SourceInput, Span, Style, lint, render};

/// The review-packet fixtures: real-world shapes, including the cases the rules target.
const CORPUS: &[(&str, &str)] = &[
    (
        "fixtures/feedback/hegel_inputs/inputs.rs",
        include_str!("../fixtures/feedback/hegel_inputs/inputs.rs"),
    ),
    (
        "fixtures/feedback/hegel_policy/positive.rs",
        include_str!("../fixtures/feedback/hegel_policy/positive.rs"),
    ),
    (
        "fixtures/feedback/hegel_policy/negative.rs",
        include_str!("../fixtures/feedback/hegel_policy/negative.rs"),
    ),
    (
        "fixtures/feedback/hegel_policy/suppressed.rs",
        include_str!("../fixtures/feedback/hegel_policy/suppressed.rs"),
    ),
    (
        "code/cdc-worker/src/audit.rs",
        include_str!("../fixtures/review-packet/code/cdc-worker/src/audit.rs"),
    ),
    (
        "code/cdc-worker/src/messages/audit_events.rs",
        include_str!("../fixtures/review-packet/code/cdc-worker/src/messages/audit_events.rs"),
    ),
    (
        "code/cdc-worker/src/messages/audit_events/tests.rs",
        include_str!(
            "../fixtures/review-packet/code/cdc-worker/src/messages/audit_events/tests.rs"
        ),
    ),
    (
        "code/kafka/src/bin/topics.rs",
        include_str!("../fixtures/review-packet/code/kafka/src/bin/topics.rs"),
    ),
    (
        "code/cdc-worker/src/assembly.rs",
        include_str!("../fixtures/review-packet/code/cdc-worker/src/assembly.rs"),
    ),
    (
        "code/core/tests/src/audit_recovery.rs",
        include_str!("../fixtures/review-packet/code/core/tests/src/audit_recovery.rs"),
    ),
    (
        "schema/topics.toml",
        include_str!("../fixtures/review-packet/schema/topics.toml"),
    ),
    (
        "code/cdc-worker/BUCK",
        include_str!("../fixtures/review-packet/code/cdc-worker/BUCK"),
    ),
    (
        "fixtures/feedback/api/collections.rs",
        include_str!("../fixtures/feedback/api/collections.rs"),
    ),
    (
        "fixtures/feedback/api/compatibility.rs",
        include_str!("../fixtures/feedback/api/compatibility.rs"),
    ),
    (
        "fixtures/feedback/api/conversions.rs",
        include_str!("../fixtures/feedback/api/conversions.rs"),
    ),
    (
        "fixtures/feedback/api/parallel.rs",
        include_str!("../fixtures/feedback/api/parallel.rs"),
    ),
    (
        "fixtures/feedback/api/shallow.rs",
        include_str!("../fixtures/feedback/api/shallow.rs"),
    ),
    (
        "fixtures/feedback/bounds/arbitrary.rs",
        include_str!("../fixtures/feedback/bounds/arbitrary.rs"),
    ),
    (
        "fixtures/feedback/comments/redundant.rs",
        include_str!("../fixtures/feedback/comments/redundant.rs"),
    ),
    (
        "fixtures/feedback/comments/suppressed.rs",
        include_str!("../fixtures/feedback/comments/suppressed.rs"),
    ),
    (
        "fixtures/feedback/expressions/booleans.rs",
        include_str!("../fixtures/feedback/expressions/booleans.rs"),
    ),
    (
        "fixtures/feedback/expressions/defaults.rs",
        include_str!("../fixtures/feedback/expressions/defaults.rs"),
    ),
    (
        "fixtures/feedback/expressions/dependencies.rs",
        include_str!("../fixtures/feedback/expressions/dependencies.rs"),
    ),
    (
        "fixtures/feedback/expressions/errors.rs",
        include_str!("../fixtures/feedback/expressions/errors.rs"),
    ),
    (
        "fixtures/feedback/expressions/json.rs",
        include_str!("../fixtures/feedback/expressions/json.rs"),
    ),
    (
        "fixtures/feedback/expressions/matches.rs",
        include_str!("../fixtures/feedback/expressions/matches.rs"),
    ),
    (
        "fixtures/feedback/expressions/predicates.rs",
        include_str!("../fixtures/feedback/expressions/predicates.rs"),
    ),
    (
        "fixtures/feedback/expressions/suppressed.rs",
        include_str!("../fixtures/feedback/expressions/suppressed.rs"),
    ),
    (
        "fixtures/feedback/tests/fixture_loop.rs",
        include_str!("../fixtures/feedback/tests/fixture_loop.rs"),
    ),
    (
        "fixtures/feedback/tests/literal_cases.rs",
        include_str!("../fixtures/feedback/tests/literal_cases.rs"),
    ),
    (
        "fixtures/feedback/workspace/ambiguous_a.rs",
        include_str!("../fixtures/feedback/workspace/ambiguous_a.rs"),
    ),
    (
        "fixtures/feedback/workspace/ambiguous_b.rs",
        include_str!("../fixtures/feedback/workspace/ambiguous_b.rs"),
    ),
    (
        "fixtures/feedback/workspace/ambiguous_impl.rs",
        include_str!("../fixtures/feedback/workspace/ambiguous_impl.rs"),
    ),
    (
        "fixtures/feedback/workspace/generic.rs",
        include_str!("../fixtures/feedback/workspace/generic.rs"),
    ),
    (
        "fixtures/feedback/workspace/impl.rs",
        include_str!("../fixtures/feedback/workspace/impl.rs"),
    ),
    (
        "fixtures/feedback/workspace/negative.rs",
        include_str!("../fixtures/feedback/workspace/negative.rs"),
    ),
    (
        "fixtures/feedback/workspace/qualified_paths.rs",
        include_str!("../fixtures/feedback/workspace/qualified_paths.rs"),
    ),
    (
        "fixtures/feedback/workspace/qualified_super.rs",
        include_str!("../fixtures/feedback/workspace/qualified_super.rs"),
    ),
    (
        "fixtures/feedback/workspace/second_impl.rs",
        include_str!("../fixtures/feedback/workspace/second_impl.rs"),
    ),
    (
        "fixtures/feedback/workspace/suppressed.rs",
        include_str!("../fixtures/feedback/workspace/suppressed.rs"),
    ),
    (
        "fixtures/feedback/workspace/trait.rs",
        include_str!("../fixtures/feedback/workspace/trait.rs"),
    ),
];

fn char_boundaries(text: &str) -> Vec<usize> {
    text.char_indices()
        .map(|(i, _)| i)
        .chain(std::iter::once(text.len()))
        .collect()
}

/// 1-based line and column of `offset`, computed independently of the linter.
fn line_col(text: &str, offset: usize) -> Position {
    let before = &text[..offset];
    let line = before.matches('\n').count() + 1;
    let col = offset - before.rfind('\n').map_or(0, |i| i + 1) + 1;
    Position { line, col }
}

fn valid_span(text: &str, span: Span) -> Result<(), &'static str> {
    if span.start > span.end {
        return Err("start is after end");
    }
    if (span.end as usize) > text.len() {
        return Err("end is outside the source");
    }
    if !text.is_char_boundary(span.start as usize) {
        return Err("start is not a character boundary");
    }
    if !text.is_char_boundary(span.end as usize) {
        return Err("end is not a character boundary");
    }
    Ok(())
}

/// Everything a consumer relies on: spans in bounds and on char boundaries, positions
/// matching the primary span, unique fingerprints, and rendering that doesn't panic.
fn assert_well_formed(input: &SourceInput, findings: &[Finding]) {
    let text: &str = input.as_ref();
    let mut fingerprints = rustc_hash::FxHashSet::default();
    for f in findings {
        if f.kind == Kind::Lint {
            assert!(
                f.footers.iter().any(|footer| match footer {
                    Footer::Help { message } | Footer::Suggestion { message, .. } =>
                        !message.is_empty(),
                    Footer::Note { .. } => false,
                }),
                "{} needs guidance for interpreting its evidence",
                f.rule
            );
        }
        if let Err(reason) = valid_span(text, f.primary.span) {
            panic!("{}: primary {:?}: {reason}", f.rule, f.primary.span);
        }
        if let Err(reason) = valid_span(text, f.item_span) {
            panic!("{}: item {:?}: {reason}", f.rule, f.item_span);
        }
        for label in &f.labels {
            if let Err(reason) = valid_span(text, label.span) {
                panic!("{}: label {:?}: {reason}", f.rule, label.span);
            }
        }
        for footer in &f.footers {
            if let Footer::Suggestion { span, .. } = footer {
                if let Err(reason) = valid_span(text, *span) {
                    panic!("{}: suggestion {span:?}: {reason}", f.rule);
                }
            }
        }
        assert_eq!(
            Position {
                line: f.line,
                col: f.col
            },
            line_col(text, f.primary.span.start as usize),
            "{}",
            f.rule
        );
        assert!(
            fingerprints.insert(f.fingerprint.clone()),
            "duplicate fingerprint for {} at {}:{}",
            f.rule,
            f.line,
            f.col
        );
    }
    let _ = render(findings, input, Style::Plain);
}

#[derive(Debug)]
struct CorpusCut {
    name: &'static str,
    text: &'static str,
    cut: usize,
}

impl DefaultGenerator for CorpusCut {
    type Generator = BoxedPrintableGenerator<'static, Self>;

    fn default_generator() -> Self::Generator {
        hegel::compose!(|tc| {
            let (name, text) = tc.draw(generators::sampled_from(CORPUS.to_vec()));
            let cut = tc.draw(generators::sampled_from(char_boundaries(text)));
            Self { name, text, cut }
        })
        .boxed_printable()
    }
}

#[derive(Debug)]
struct JunkCase {
    name: &'static str,
    text: &'static str,
    at: usize,
    fragments: Vec<&'static str>,
    free_text: String,
}

impl DefaultGenerator for JunkCase {
    type Generator = BoxedPrintableGenerator<'static, Self>;

    fn default_generator() -> Self::Generator {
        hegel::compose!(|tc| {
            let (name, text) = tc.draw(generators::sampled_from(CORPUS.to_vec()));
            let at = tc.draw(generators::sampled_from(char_boundaries(text)));
            let pieces = [
                "{",
                "}",
                "(",
                ")",
                "\"",
                "'",
                "r#\"",
                "//",
                "/*",
                "*/",
                "#",
                "\n",
                "fn ",
                "impl ",
                "Option<",
                "Ok(",
                ";",
                ",",
                "é",
                "shapelint: allow(",
                "= 7200000",
            ];
            let fragments =
                tc.draw(generators::vecs(generators::sampled_from(pieces.to_vec())).max_size(8));
            let free_text = tc.draw(generators::text().max_size(12));
            Self {
                name,
                text,
                at,
                fragments,
                free_text,
            }
        })
        .boxed_printable()
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum UnitStem {
    Ts,
    Ttl,
    Delay,
    Age,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum UnitSuffix {
    Millis,
    Micros,
    Nanos,
    Seconds,
    ShortSeconds,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum UnitOptionality {
    Required,
    Optional,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct UnitField {
    stem: UnitStem,
    suffix: UnitSuffix,
    optionality: UnitOptionality,
}

#[derive(Debug)]
struct UnitFieldsCase {
    fields: Vec<UnitField>,
}

impl DefaultGenerator for UnitFieldsCase {
    type Generator = BoxedPrintableGenerator<'static, Self>;

    fn default_generator() -> Self::Generator {
        generators::vecs(generators::default::<UnitField>())
            .map(|fields| Self { fields })
            .boxed_printable()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, hegel::DefaultGenerator)]
enum ParameterType {
    OptionU8,
    OptionString,
    PlainU8,
    Callback,
    Str,
}

#[derive(Debug)]
struct OptionGroupsCase {
    types: Vec<ParameterType>,
}

impl DefaultGenerator for OptionGroupsCase {
    type Generator = BoxedPrintableGenerator<'static, Self>;

    fn default_generator() -> Self::Generator {
        generators::vecs(generators::default::<ParameterType>())
            .map(|types| Self { types })
            .boxed_printable()
    }
}

#[derive(Debug)]
struct UnknownAllowCase {
    id: &'static str,
    at: usize,
    letter: char,
    edit: TypoEdit,
}

impl UnknownAllowCase {
    fn typo(id: &str, at: usize, letter: char, edit: TypoEdit) -> String {
        let mut typo: Vec<char> = id.chars().collect();
        match edit {
            TypoEdit::Delete => match typo.get(at) {
                Some(_) => {
                    typo.remove(at);
                }
                None => typo.insert(at, letter),
            },
            TypoEdit::Insert => typo.insert(at, letter),
            TypoEdit::Replace => match typo.get_mut(at) {
                Some(character) => *character = letter,
                None => typo.insert(at, letter),
            },
            TypoEdit::Swap => match at
                .checked_add(1)
                .and_then(|next| typo.get(next).map(|_| next))
            {
                Some(next) => typo.swap(at, next),
                None => typo.insert(at, letter),
            },
        }
        typo.into_iter().collect()
    }
}

impl DefaultGenerator for UnknownAllowCase {
    type Generator = BoxedPrintableGenerator<'static, Self>;

    fn default_generator() -> Self::Generator {
        hegel::compose!(|tc| {
            let ids: Vec<&'static str> = RULES
                .iter()
                .map(|rule| rule.id)
                .chain(std::iter::once("all"))
                .collect();
            let id = tc.draw(generators::sampled_from(ids.clone()));
            let at = tc.draw(generators::integers::<usize>().max_value(id.len()));
            let letter = tc.draw(generators::sampled_from(
                "abcdefghijklmnopqrstuvwxyz-_".chars().collect::<Vec<_>>(),
            ));
            let edit = tc.draw(generators::default::<TypoEdit>());
            let case = Self {
                id,
                at,
                letter,
                edit,
            };
            let typo = Self::typo(case.id, case.at, case.letter, case.edit);
            match (typo.is_empty(), ids.contains(&typo.as_str())) {
                (false, false) => case,
                _ => tc.reject(),
            }
        })
        .boxed_printable()
    }
}

#[derive(Debug)]
struct AllowCommentCase {
    name: &'static str,
    text: &'static str,
    target: usize,
}

impl DefaultGenerator for AllowCommentCase {
    type Generator = BoxedPrintableGenerator<'static, Self>;

    fn default_generator() -> Self::Generator {
        hegel::compose!(|tc| {
            let rust_corpus: Vec<(&'static str, &'static str)> = CORPUS
                .iter()
                .copied()
                .filter(|(name, text)| name.ends_with(".rs") && !text.contains("spawn_blocking"))
                .collect();
            let (name, text) = tc.draw(generators::sampled_from(rust_corpus));
            let before = lint(
                &SourceInput::try_new(name, text).expect("test source fits in u32"),
                &Config::default(),
            )
            .expect("small");
            let target = match before.len() {
                0 => tc.reject(),
                _ => tc.draw(generators::integers::<usize>().max_value(before.len() - 1)),
            };
            Self { name, text, target }
        })
        .boxed_printable()
    }
}

#[hegel::test(print_blob = true)]
fn lint_is_total_on_every_truncation(tc: TestCase) {
    let CorpusCut { name, text, cut } = tc.draw(generators::default::<CorpusCut>());
    let input = SourceInput::try_new(name, &text[..cut]).expect("test source fits in u32");
    let findings = match lint(&input, &Config::default()) {
        Ok(findings) => findings,
        Err(shapelint::LintError::Parse { .. }) => return,
        Err(error) => panic!("{error}"),
    };
    assert_well_formed(&input, &findings);
}

#[hegel::test(print_blob = true)]
fn lint_is_total_after_inserting_junk(tc: TestCase) {
    let JunkCase {
        name,
        text,
        at,
        fragments,
        free_text,
    } = tc.draw(generators::default::<JunkCase>());
    let junk = format!("{}{free_text}", fragments.concat());
    let input = SourceInput::try_new(name, format!("{}{junk}{}", &text[..at], &text[at..]))
        .expect("test source fits in u32");
    let findings = match lint(&input, &Config::default()) {
        Ok(findings) => findings,
        Err(shapelint::LintError::Parse { .. }) => return,
        Err(error) => panic!("{error}"),
    };
    assert_well_formed(&input, &findings);
}

#[hegel::test(print_blob = true)]
fn findings_are_deterministic(tc: TestCase) {
    let CorpusCut { name, text, cut } = tc.draw(generators::default::<CorpusCut>());
    let input = SourceInput::try_new(name, &text[..cut]).expect("test source fits in u32");
    let key = |f: &Finding| {
        (
            f.rule,
            f.message.clone(),
            f.primary.clone(),
            f.labels.clone(),
            f.footers.clone(),
            f.fingerprint.clone(),
        )
    };
    match (
        lint(&input, &Config::default()),
        lint(&input, &Config::default()),
    ) {
        (Ok(first), Ok(second)) => assert_eq!(
            first.iter().map(key).collect::<Vec<_>>(),
            second.iter().map(key).collect::<Vec<_>>()
        ),
        (
            Err(shapelint::LintError::Parse { name: first }),
            Err(shapelint::LintError::Parse { name: second }),
        ) => assert_eq!(first, second),
        result => panic!("inconsistent analysis: {result:?}"),
    }
}

/// Field names from labels: the text up to the first `:` of each labelled span.
fn label_names(input: &SourceInput, finding: &Finding) -> Vec<String> {
    let mut spans: Vec<Span> = finding.labels.iter().map(|l| l.span).collect();
    spans.push(finding.primary.span);
    spans.sort();
    spans
        .iter()
        .map(|s| input.as_ref()[s.start as usize..s.end as usize].to_string())
        .filter(|t| t.contains(':'))
        .filter_map(|t| t.split_once(':').map(|(name, _)| name.trim().to_string()))
        .collect()
}

/// Model for unit-fields: stems grouped in first-appearance order; a group is reported
/// when it has two or more fields and at least one is optional.
#[hegel::test(print_blob = true)]
fn unit_fields_match_model(tc: TestCase) {
    let UnitFieldsCase {
        fields: generated_fields,
    } = tc.draw(generators::default::<UnitFieldsCase>());
    let mut fields: Vec<(String, String, UnitOptionality)> = Vec::new();
    for UnitField {
        stem,
        suffix,
        optionality,
    } in generated_fields
    {
        let stem = match stem {
            UnitStem::Ts => "ts",
            UnitStem::Ttl => "ttl",
            UnitStem::Delay => "delay",
            UnitStem::Age => "age",
        };
        let suffix = match suffix {
            UnitSuffix::Millis => "_ms",
            UnitSuffix::Micros => "_us",
            UnitSuffix::Nanos => "_ns",
            UnitSuffix::Seconds => "_secs",
            UnitSuffix::ShortSeconds => "_s",
        };
        let name = format!("{stem}{suffix}");
        match fields.iter().find(|(n, _, _)| *n == name) {
            Some(_) => {}
            None => fields.push((name, stem.to_string(), optionality)),
        }
    }
    let body: String = fields
        .iter()
        .map(|(n, _, opt)| match opt {
            UnitOptionality::Optional => format!("    {n}: Option<i64>,\n"),
            UnitOptionality::Required => format!("    {n}: i64,\n"),
        })
        .collect();
    let input = SourceInput::try_new("src/lib.rs", format!("struct T {{\n{body}}}\n"))
        .expect("test source fits in u32");

    let mut stems: Vec<(String, Vec<String>, Option<()>)> = Vec::new();
    for (name, stem, optional) in &fields {
        match stems.iter_mut().find(|(s, _, _)| s == stem) {
            Some((_, names, any_optional)) => {
                names.push(name.clone());
                match optional {
                    UnitOptionality::Optional => *any_optional = Some(()),
                    UnitOptionality::Required => {}
                }
            }
            None => stems.push((
                stem.clone(),
                vec![name.clone()],
                match optional {
                    UnitOptionality::Optional => Some(()),
                    UnitOptionality::Required => None,
                },
            )),
        }
    }
    let expected: Vec<Vec<String>> = stems
        .into_iter()
        .filter_map(
            |(_, names, any_optional)| match (names.len(), any_optional) {
                (2.., Some(())) => Some(names),
                _ => None,
            },
        )
        .collect();

    let findings = lint(&input, &Config::default()).expect("small");
    let actual: Vec<Vec<String>> = findings
        .iter()
        .filter(|f| f.rule == "unit-fields")
        .map(|f| label_names(&input, f))
        .collect();
    assert_eq!(actual, expected);
}

/// Model for option-plumbing groups: `Option<_>` parameter types (excluding callbacks),
/// grouped in first-appearance order; every group of two or more is reported.
#[hegel::test(print_blob = true)]
fn option_groups_match_model(tc: TestCase) {
    let OptionGroupsCase { types } = tc.draw(generators::default::<OptionGroupsCase>());
    let params: Vec<(String, ParameterType)> = types
        .iter()
        .enumerate()
        .map(|(i, parameter_type)| (format!("p{i}"), *parameter_type))
        .collect();
    let signature: Vec<String> = params
        .iter()
        .map(|(name, parameter_type)| {
            let ty = match parameter_type {
                ParameterType::OptionU8 => "Option<u8>",
                ParameterType::OptionString => "Option<String>",
                ParameterType::PlainU8 => "u8",
                ParameterType::Callback => "Option<fn()>",
                ParameterType::Str => "&str",
            };
            format!("{name}: {ty}")
        })
        .collect();
    let input = SourceInput::try_new(
        "src/lib.rs",
        format!("fn f({}) {{}}\n", signature.join(", ")),
    )
    .expect("test source fits in u32");

    let mut groups: Vec<(ParameterType, Vec<String>)> = Vec::new();
    for (name, parameter_type) in &params {
        match parameter_type {
            ParameterType::OptionU8 | ParameterType::OptionString => {
                match groups.iter_mut().find(|(ty, _)| ty == parameter_type) {
                    Some((_, names)) => names.push(name.clone()),
                    None => groups.push((*parameter_type, vec![name.clone()])),
                }
            }
            ParameterType::PlainU8 | ParameterType::Callback | ParameterType::Str => {}
        }
    }
    let expected: Vec<Vec<String>> = groups
        .into_iter()
        .filter(|(_, names)| match names.as_slice() {
            [_, _, ..] => true,
            [] | [_] => false,
        })
        .map(|(_, n)| n)
        .collect();

    let findings = lint(&input, &Config::default()).expect("small");
    let actual: Vec<Vec<String>> = findings
        .iter()
        .filter(|f| f.rule == "option-plumbing")
        .map(|f| label_names(&input, f))
        .collect();
    assert_eq!(actual, expected);
}

/// Unrestricted Damerau-Levenshtein distance (Lowrance-Wagner), the test model for suggestions.
fn damerau(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let max = a.len() + b.len();
    let mut last_row: std::collections::HashMap<char, usize> = std::collections::HashMap::new();
    let mut d = vec![vec![0usize; b.len() + 2]; a.len() + 2];
    d[0][0] = max;
    for i in 0..=a.len() {
        d[i + 1][0] = max;
        d[i + 1][1] = i;
    }
    for j in 0..=b.len() {
        d[0][j + 1] = max;
        d[1][j + 1] = j;
    }
    for i in 1..=a.len() {
        let mut last_match_col = 0;
        for j in 1..=b.len() {
            let i1 = match last_row.get(&b[j - 1]) {
                Some(&i1) => i1,
                None => 0,
            };
            let j1 = last_match_col;
            let cost = usize::from(a[i - 1] != b[j - 1]);
            if cost == 0 {
                last_match_col = j;
            }
            d[i + 1][j + 1] = (d[i][j] + cost)
                .min(d[i + 1][j] + 1)
                .min(d[i][j + 1] + 1)
                .min(d[i1][j1] + (i - i1 - 1) + 1 + (j - j1 - 1));
        }
        last_row.insert(a[i - 1], i);
    }
    d[a.len() + 1][b.len() + 1]
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum TypoEdit {
    Delete,
    Insert,
    Replace,
    Swap,
}

#[hegel::test(print_blob = true)]
fn unknown_allow_suggests_the_unique_close_rule(tc: TestCase) {
    let ids: Vec<&str> = RULES
        .iter()
        .map(|r| r.id)
        .chain(std::iter::once("all"))
        .collect();
    let UnknownAllowCase {
        id,
        at,
        letter,
        edit,
    } = tc.draw(generators::default::<UnknownAllowCase>());
    let typo = UnknownAllowCase::typo(id, at, letter, edit);

    let limit = (typo.chars().count() / 3).min(3);
    let close: Vec<&str> = ids
        .iter()
        .copied()
        .filter(|id| match limit {
            0 => false,
            _ => damerau(&typo, id) <= limit,
        })
        .collect();
    let expected = match close.as_slice() {
        [only] => Some((*only).to_owned()),
        _ => None,
    };

    let input = SourceInput::try_new(
        "src/lib.rs",
        format!("// shapelint: allow({typo})\nfn x() {{}}\n"),
    )
    .expect("test source fits in u32");
    let findings = lint(&input, &Config::default()).expect("small");
    let unknown: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.rule == "unknown-allow")
        .collect();
    assert_eq!(unknown.len(), 1, "{findings:?}");
    let suggested = unknown[0].footers.iter().find_map(|f| match f {
        Footer::Suggestion { replacement, .. } => Some(replacement.clone()),
        _ => None,
    });
    assert_eq!(suggested, expected, "typo `{typo}`");
}

/// An allow comment inserted above line L removes exactly the findings of that rule whose
/// primary label or enclosing item is in the following comment block or its adjacent item.
#[hegel::test(print_blob = true)]
fn allow_comment_suppresses_exactly_its_scope(tc: TestCase) {
    let AllowCommentCase {
        name,
        text,
        target: target_index,
    } = tc.draw(generators::default::<AllowCommentCase>());
    let before = lint(
        &SourceInput::try_new(name, text).expect("test source fits in u32"),
        &Config::default(),
    )
    .expect("small");
    let target = &before[target_index];
    let line = target.line;
    let line_start = text
        .split_inclusive('\n')
        .take(line as usize - 1)
        .map(str::len)
        .sum::<usize>();
    let edited = format!(
        "{}// shapelint: allow({})\n{}",
        &text[..line_start],
        target.rule,
        &text[line_start..]
    );

    let key = |f: &Finding| (f.rule, f.item.clone(), f.message.clone());
    let item_line = |f: &Finding| line_col(text, f.item_span.start as usize).line;
    let comments = text
        .lines()
        .skip(line as usize - 1)
        .take_while(|text| {
            let text = text.trim_start();
            text.starts_with("//") && !text.starts_with("///") && !text.starts_with("//!")
        })
        .count();
    let covered = line..=line + comments;
    let mut expected: Vec<_> = before
        .iter()
        .filter(|f| {
            match (
                f.rule == target.rule,
                covered.contains(&f.line) || covered.contains(&item_line(f)),
            ) {
                (true, true) => false,
                _ => true,
            }
        })
        .map(key)
        .collect();
    let mut after: Vec<_> = lint(
        &SourceInput::try_new(name, edited).expect("test source fits in u32"),
        &Config::default(),
    )
    .expect("small")
    .iter()
    .map(key)
    .collect();
    expected.sort();
    after.sort();
    assert_eq!(after, expected);
}

/// Parsing nested syntax must still return, and the
/// findings past the nesting must be the same as without it.
#[test]
fn deep_nesting_is_linted_without_overflow() {
    let n = 5000;
    let deep = format!(
        "fn parens() -> u8 {{ {}1{} }}\nfn blocks() {{ {}{} }}\nfn bangs(x: bool) -> bool {{ {}x }}\nfn low(v: u64) -> u64 {{ v & 0xff }}\n",
        "(".repeat(n),
        ")".repeat(n),
        "{".repeat(n),
        "}".repeat(n),
        "!".repeat(n)
    );
    let input = SourceInput::try_new("src/lib.rs", deep).expect("test source fits in u32");
    let findings =
        lint(&input, &Config::default()).expect("a 5000-level source fits the sized stack");
    let low: Vec<&str> = findings
        .iter()
        .filter(|f| f.item == "fn low")
        .map(|f| f.rule)
        .collect();
    assert_eq!(low, ["shallow-helper"]);
}
