#![feature(rustc_private)]

use shapelint::{Config, SourceInput, lint};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Directive {
    Stacked,
    Multiline,
    Trailing,
    Documentation,
}

#[hegel::test]
fn directives_follow_comment_blocks_without_leaking_from_trailing_comments(tc: hegel::TestCase) {
    let directive = tc.draw(hegel::generators::default::<Directive>());
    let prefix = match directive {
        Directive::Stacked => {
            "// shapelint: allow(boolean-state)\n// shapelint: allow(identity-string)\n// rationale\n"
        }
        Directive::Multiline => "/*\nshapelint: allow(boolean-state)\n*/\n",
        Directive::Trailing => {
            "const X: () = (); // shapelint: allow(boolean-state)\n// rationale\n"
        }
        Directive::Documentation => "/// shapelint: allow(boolean-state)\n",
    };
    let input = SourceInput::try_new(
        "src/lib.rs",
        format!("{prefix}pub struct State {{ pub ready: bool }}"),
    )
    .expect("fixture");
    let findings = lint(&input, &Config::default()).expect("valid source");
    let count = findings
        .iter()
        .filter(|finding| finding.rule == "boolean-state")
        .count();
    match directive {
        Directive::Stacked | Directive::Multiline => assert_eq!(count, 0),
        Directive::Trailing | Directive::Documentation => assert_eq!(count, 1),
    }
}

#[test]
fn malformed_rust_reports_a_parse_error_without_unwinding() {
    let input =
        SourceInput::try_new("src/lib.rs", "const TEXT: &str = \"unfinished").expect("fixture");
    let Err(shapelint::LintError::Parse { name }) = lint(&input, &Config::default()) else {
        panic!("expected a parse error");
    };
    assert_eq!(name, "src/lib.rs");
}

#[test]
fn shebang_does_not_shift_labels_or_prevent_linting() {
    let input = SourceInput::try_new(
        "script.rs",
        "#!/usr/bin/env rust-script\npub struct State { pub ready: bool }",
    )
    .expect("fixture");
    let findings = lint(&input, &Config::default()).expect("valid script");
    let finding = findings
        .iter()
        .find(|finding| finding.rule == "boolean-state")
        .expect("finding");
    assert_eq!(
        &input.as_ref()[std::ops::Range::from(finding.primary.span)],
        "bool"
    );
    assert_eq!(finding.line, 2);
}
