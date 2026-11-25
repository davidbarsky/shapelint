#![feature(rustc_private)]

use hegel::{TestCase, generators};
use insta::assert_snapshot;

use shapelint::{Config, SourceInput, Style, lint, render};

fn check(name: &str, text: &str) -> String {
    let input = SourceInput::try_new(name, text).expect("test source fits in u32");
    let findings = lint(&input, &Config::default()).expect("test sources are small");
    render(&findings, &input, Style::Plain)
        .trim_end()
        .to_string()
}

#[test]
fn duration_comment() {
    let text = "[topic.config]\n\"retention.ms\" = \"2592000000\"\n# 7 days\n\"segment.ms\" = 604800000\n\"flush.ms\" = 500\nwindow_secs = 7200 # 2 hours\n";
    assert_snapshot!(check("schema/topics.toml", text), @r#"
    lint[duration-comment]: `retention.ms` is 2592000000 with no comment giving its unit
      ╭▸ schema/topics.toml:2:18
      │
    2 │ "retention.ms" = "2592000000"
      │                  ━━━━━━━━━━━━ 30 days (720 hours)
      ╰╴
    help: say the duration in human units
      ╭╴
    2 │ "retention.ms" = "2592000000" # 30 days (720 hours)
      ╰╴                              +++++++++++++++++++++
    "#);
}

#[test]
fn mapped_srcs() {
    let text = "rust_library(\n    name = \"x\",\n    mapped_srcs = {},  # mapped_srcs in a comment is ignored\n)\n";
    assert_snapshot!(check("code/x/BUCK", text), @"
    lint[mapped-srcs]: `mapped_srcs` remaps the source tree
      ╭▸ code/x/BUCK:3:5
      │
    3 │     mapped_srcs = {},  # mapped_srcs in a comment is ignored
      │     ━━━━━━━━━━━ remapped here
      │
      ╰ help: keep the standard layout and declare generated inputs explicitly
    ");
}

#[test]
fn hash_comment_allow() {
    let text = "# shapelint: allow(duration-comment) documented in the runbook\n\"retention.ms\" = \"2592000000\"\n";
    assert_snapshot!(check("schema/topics.toml", text), @"");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Literal {
    TomlBasic,
    TomlLiteral,
    TomlMultiline,
    TomlMultilineLiteral,
    StarlarkBasic,
    StarlarkSingle,
    StarlarkMultiline,
    StarlarkMultilineSingle,
    StarlarkRaw,
    EscapedDoubleQuote,
    EscapedSingleQuote,
    TomlLiteralBackslash,
}

#[derive(Debug, hegel::DefaultGenerator)]
enum Comment {
    InsideString,
    AfterAssignment,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct CommentCase {
    literal: Literal,
    comment: Comment,
}

struct SourceCase {
    path: &'static str,
    value: String,
    assignment: &'static str,
    rule: &'static str,
}

#[hegel::test]
fn only_real_hash_comments_suppress_diagnostics(tc: TestCase) {
    let CommentCase { literal, comment } = tc.draw(generators::default::<CommentCase>());
    let marker = "# shapelint: allow(duration-comment, mapped-srcs, imaginary-rule)";
    let SourceCase {
        path,
        value,
        assignment,
        rule,
    } = match literal {
        Literal::TomlBasic => SourceCase {
            path: "file.toml",
            value: format!("\"{marker}\""),
            assignment: "timeout_ms = 7200000",
            rule: "duration-comment",
        },
        Literal::TomlLiteral => SourceCase {
            path: "file.toml",
            value: format!("'{marker}'"),
            assignment: "timeout_ms = 7200000",
            rule: "duration-comment",
        },
        Literal::TomlMultiline => SourceCase {
            path: "file.toml",
            value: format!("\"\"\"\n{marker}\ntimeout_ms = 7200000\n\"\"\""),
            assignment: "timeout_ms = 7200000",
            rule: "duration-comment",
        },
        Literal::TomlMultilineLiteral => SourceCase {
            path: "file.toml",
            value: format!("'''\n{marker}\ntimeout_ms = 7200000\n'''"),
            assignment: "timeout_ms = 7200000",
            rule: "duration-comment",
        },
        Literal::StarlarkBasic => SourceCase {
            path: "BUILD",
            value: format!("\"{marker}\""),
            assignment: "mapped_srcs = {}",
            rule: "mapped-srcs",
        },
        Literal::StarlarkSingle => SourceCase {
            path: "BUILD",
            value: format!("'{marker}'"),
            assignment: "mapped_srcs = {}",
            rule: "mapped-srcs",
        },
        Literal::StarlarkMultiline => SourceCase {
            path: "BUILD",
            value: format!("\"\"\"\n{marker}\nmapped_srcs = {{}}\n\"\"\""),
            assignment: "mapped_srcs = {}",
            rule: "mapped-srcs",
        },
        Literal::StarlarkMultilineSingle => SourceCase {
            path: "BUILD",
            value: format!("'''\n{marker}\nmapped_srcs = {{}}\n'''"),
            assignment: "mapped_srcs = {}",
            rule: "mapped-srcs",
        },
        Literal::StarlarkRaw => SourceCase {
            path: "BUILD",
            value: format!("r\"{marker}\""),
            assignment: "mapped_srcs = {}",
            rule: "mapped-srcs",
        },
        Literal::EscapedDoubleQuote => SourceCase {
            path: "file.toml",
            value: format!("\"escaped \\\" {marker}\""),
            assignment: "timeout_ms = 7200000",
            rule: "duration-comment",
        },
        Literal::EscapedSingleQuote => SourceCase {
            path: "BUILD",
            value: format!("'escaped \\' {marker}'"),
            assignment: "mapped_srcs = {}",
            rule: "mapped-srcs",
        },
        Literal::TomlLiteralBackslash => SourceCase {
            path: "file.toml",
            value: format!("'{marker}\\'"),
            assignment: "timeout_ms = 7200000",
            rule: "duration-comment",
        },
    };
    let suffix = match comment {
        Comment::InsideString => String::new(),
        Comment::AfterAssignment => format!(" # shapelint: allow({rule})"),
    };
    let text = format!("value = {value}\n{assignment}{suffix}\n");
    let input = SourceInput::try_new(path, text).expect("small source");
    let findings = lint(&input, &Config::default()).expect("lint source");
    match comment {
        Comment::InsideString => {
            assert_eq!(findings.len(), 1, "{}: {findings:?}", input.as_ref());
            assert_eq!(findings[0].rule, rule);
            assert_eq!(
                &input.as_ref()[std::ops::Range::from(findings[0].item_span)],
                assignment
            );
        }
        Comment::AfterAssignment => assert_eq!(findings.len(), 0, "{findings:?}"),
    }
}

#[derive(Debug, hegel::DefaultGenerator)]
enum StarlarkText {
    String,
    LongerName,
    Comment,
    Comparison,
}

#[hegel::test]
fn mapped_srcs_requires_an_assignment(tc: TestCase) {
    let case = tc.draw(generators::default::<StarlarkText>());
    let text = match case {
        StarlarkText::String => "name = \"mapped_srcs\"",
        StarlarkText::LongerName => "unmapped_srcs = {}",
        StarlarkText::Comment => "# mapped_srcs = {}",
        StarlarkText::Comparison => "mapped_srcs == {}",
    };
    let input = SourceInput::try_new("BUILD", text).expect("small source");
    assert_eq!(
        lint(&input, &Config::default()).expect("lint source").len(),
        0
    );
}

#[derive(Debug, hegel::DefaultGenerator)]
enum TextLanguage {
    Toml,
    Starlark,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct TextCase {
    language: TextLanguage,
    text: String,
}

#[hegel::test]
fn arbitrary_text_has_valid_diagnostic_spans(tc: TestCase) {
    let TextCase { language, text } = tc.draw(generators::default::<TextCase>());
    let path = match language {
        TextLanguage::Toml => "file.toml",
        TextLanguage::Starlark => "BUILD",
    };
    let input = SourceInput::try_new(path, text).expect("small source");
    let findings = lint(&input, &Config::default()).expect("lint source");
    for finding in &findings {
        match input
            .as_ref()
            .get(std::ops::Range::from(finding.primary.span))
        {
            Some(_) => {}
            None => panic!("invalid span: {finding:?}"),
        }
    }
    render(&findings, &input, Style::Plain);
}

#[test]
fn rust_comments_report_unknown_rule_names() {
    let source = SourceInput::try_new(
        "lib.rs",
        "// shapelint: allow(imaginary-rule)\npub fn run() {}\n",
    )
    .expect("source is within the byte limit");
    let findings = lint(&source, &Config::default()).expect("source parses");
    let [finding] = findings.as_slice() else {
        panic!("expected one finding, got {findings:?}");
    };
    assert_eq!(finding.rule, "unknown-allow");
}
