use hegel::{TestCase, generators};

use shapelint::{Config, Footer, Kind, SourceInput, lint};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ImportForm {
    Plain,
    Nested,
    SelfImport,
    Public,
    Local,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Alias {
    Named(u16),
    RawIdentifier,
    SameName,
    Anonymous,
    None,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct ImportCase {
    form: ImportForm,
    alias: Alias,
}

#[hegel::test]
fn named_aliases_require_qualified_paths(tc: TestCase) {
    let ImportCase { form, alias } = tc.draw(generators::default::<ImportCase>());
    let rename = match alias {
        Alias::Named(id) => format!(" as Alias{id}"),
        Alias::RawIdentifier => " as r#type".into(),
        Alias::SameName => " as Thing".into(),
        Alias::Anonymous => " as _".into(),
        Alias::None => String::new(),
    };
    let text = match form {
        ImportForm::Plain => format!("use example::Thing{rename};"),
        ImportForm::Nested => format!("use example::{{module::{{Thing{rename}}}, Other}};"),
        ImportForm::SelfImport => format!("use example::{{self{rename}, Other}};"),
        ImportForm::Public => format!("pub use example::Thing{rename};"),
        ImportForm::Local => format!("fn work() {{ use example::Thing{rename}; }}"),
    };
    let input = SourceInput::try_new("src/lib.rs", text).expect("small source");
    let findings = lint(&input, &Config::default()).expect("lint source");
    let aliases: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "import-alias")
        .collect();
    match alias {
        Alias::Named(_) | Alias::RawIdentifier | Alias::SameName => {
            assert_eq!(aliases.len(), 1, "{findings:?}");
            let finding = aliases[0];
            assert_eq!(finding.kind, Kind::Lint);
            assert_eq!(
                &input.as_ref()[std::ops::Range::from(finding.primary.span)],
                rename.trim()
            );
            assert_eq!(
                finding.footers,
                [Footer::Help {
                    message: "use qualified paths instead of renaming imports".into()
                }]
            );
        }
        Alias::Anonymous | Alias::None => assert_eq!(aliases.len(), 0, "{findings:?}"),
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Context {
    Production,
    TestModule,
    SpacedTestAttribute,
    TestFile,
    TestFunction,
    QualifiedTestFunction,
    NonTestAttribute,
    NotTest,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum SuperUse {
    Glob,
    NamedImport,
    GroupedGlob,
    NestedGlob,
    RepeatedParent,
    Expression,
    Type,
    Visibility,
    ImportVisibility,
    Macro,
    Qualified,
    String,
    Comment,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct SuperCase {
    context: Context,
    usage: SuperUse,
}

#[hegel::test]
fn super_is_only_allowed_in_test_parent_glob_imports(tc: TestCase) {
    let SuperCase { context, usage } = tc.draw(generators::default::<SuperCase>());
    let text = match usage {
        SuperUse::Glob => "use super /* parent */ :: *;",
        SuperUse::NamedImport => "use super::Thing;",
        SuperUse::GroupedGlob => "use super::{*};",
        SuperUse::NestedGlob => "use super::child::*;",
        SuperUse::RepeatedParent => "use super::super::Thing;",
        SuperUse::Expression => "fn work() { super::work(); }",
        SuperUse::Type => "type Thing = super::Thing;",
        SuperUse::Visibility => "pub(super) struct Thing;",
        SuperUse::ImportVisibility => "pub use super::*;",
        SuperUse::Macro => "quote! { super::Thing };",
        SuperUse::Qualified => "use crate::Thing;",
        SuperUse::String => "const TEXT: &str = \"use super::Thing;\";",
        SuperUse::Comment => "// use super::Thing;",
    };
    let (path, text) = match context {
        Context::Production => ("src/lib.rs", format!("mod production {{\n{text}\n}}")),
        Context::TestModule => (
            "src/lib.rs",
            format!("#[cfg(test)] mod tests {{\n{text}\n}}"),
        ),
        Context::SpacedTestAttribute => (
            "src/lib.rs",
            format!("#[cfg ( /* condition */ test )] mod tests {{\n{text}\n}}"),
        ),
        Context::TestFile => ("src/rules/tests.rs", text.to_owned()),
        Context::TestFunction => ("src/lib.rs", format!("#[test] fn check() {{\n{text}\n}}")),
        Context::QualifiedTestFunction => (
            "src/lib.rs",
            format!("#[tokio::test] async fn check() {{\n{text}\n}}"),
        ),
        Context::NonTestAttribute => (
            "src/lib.rs",
            format!("#[doc = \"cfg(test)\"] mod production {{\n{text}\n}}"),
        ),
        Context::NotTest => (
            "src/lib.rs",
            format!("#[cfg(not(test))] mod production {{\n{text}\n}}"),
        ),
    };
    let expected = match (context, usage) {
        (
            Context::TestModule
            | Context::SpacedTestAttribute
            | Context::TestFile
            | Context::TestFunction
            | Context::QualifiedTestFunction,
            SuperUse::Glob,
        ) => 0,
        (Context::Production | Context::NonTestAttribute | Context::NotTest, SuperUse::Glob) => 1,
        (_, SuperUse::Qualified | SuperUse::String | SuperUse::Comment) => 0,
        (_, SuperUse::RepeatedParent) => 2,
        (
            _,
            SuperUse::NamedImport
            | SuperUse::GroupedGlob
            | SuperUse::NestedGlob
            | SuperUse::Expression
            | SuperUse::Type
            | SuperUse::Visibility
            | SuperUse::ImportVisibility
            | SuperUse::Macro,
        ) => 1,
    };
    let input = SourceInput::try_new(path, text).expect("small source");
    let findings = lint(&input, &Config::default()).expect("lint source");
    match (usage, expected) {
        (SuperUse::Glob, 0) => assert_eq!(
            findings
                .iter()
                .filter(|finding| finding.rule == "glob-import")
                .count(),
            0,
            "{findings:?}"
        ),
        _ => {}
    }
    let supers: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "super-path")
        .collect();
    assert_eq!(supers.len(), expected, "{}: {findings:?}", input.as_ref());
    for finding in supers {
        assert_eq!(finding.kind, Kind::Lint);
        assert_eq!(
            &input.as_ref()[std::ops::Range::from(finding.primary.span)],
            "super"
        );
    }
}

#[test]
fn test_parent_glob_does_not_exempt_attribute_paths() {
    let input = SourceInput::try_new(
        "src/lib.rs",
        "#[cfg(test)] mod tests { #[super::attribute] use super::*; }",
    )
    .expect("small source");
    let findings = lint(&input, &Config::default()).expect("lint source");
    let findings: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "super-path")
        .collect();
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "super-path");
    assert_eq!(
        &input.as_ref()[..findings[0].primary.span.start as usize],
        "#[cfg(test)] mod tests { #["
    );
    assert_eq!(
        &input.as_ref()[std::ops::Range::from(findings[0].primary.span)],
        "super"
    );
}

#[test]
fn import_like_text_in_literals_and_comments_is_ignored() {
    let input = SourceInput::try_new(
        "src/lib.rs",
        "// use example::Thing as Alias;\nconst TEXT: &str = \"use example::Thing as Alias;\";\n",
    )
    .expect("small source");
    let findings = lint(&input, &Config::default()).expect("lint source");
    assert_eq!(findings.len(), 0, "{findings:?}");
}

#[test]
fn imports_can_be_suppressed_at_the_use_item() {
    let input = SourceInput::try_new("src/lib.rs", "// shapelint: allow(import-alias, super-path) compatibility export\nuse super::Thing as Alias;\n").expect("small source");
    let findings = lint(&input, &Config::default()).expect("lint source");
    assert_eq!(findings.len(), 0, "{findings:?}");
}

#[derive(Debug, hegel::DefaultGenerator)]
enum TestPredicate {
    Test,
    AllTest,
    AnyTest,
    AnyTestOnly,
    Nested,
    Negated,
    DoubleNegated,
    DeMorgan,
    FeatureNamedTest,
    EmptyAll,
    EmptyAny,
    TrailingCommas,
}

#[hegel::test]
fn cfg_must_exclude_production_to_allow_parent_globs(tc: TestCase) {
    let predicate = tc.draw(generators::default::<TestPredicate>());
    let (predicate, expected) = match predicate {
        TestPredicate::Test => ("test", 0),
        TestPredicate::AllTest => ("all(test, unix)", 0),
        TestPredicate::AnyTest => ("any(test, unix)", 2),
        TestPredicate::AnyTestOnly => ("any(test, test)", 0),
        TestPredicate::Nested => ("all(any(unix, windows), test)", 0),
        TestPredicate::Negated => ("not(test)", 2),
        TestPredicate::DoubleNegated => ("not(not(test))", 0),
        TestPredicate::DeMorgan => ("not(any(not(test), unix))", 0),
        TestPredicate::FeatureNamedTest => ("feature = \"test\"", 2),
        TestPredicate::EmptyAll => ("all()", 2),
        TestPredicate::EmptyAny => ("any()", 0),
        TestPredicate::TrailingCommas => ("all(test, not(windows,),)", 0),
    };
    let input = SourceInput::try_new(
        "src/lib.rs",
        format!("#[cfg({predicate})] mod tests {{ use super::*; }}"),
    )
    .expect("small source");
    let findings = lint(&input, &Config::default()).expect("lint source");
    assert_eq!(
        findings
            .iter()
            .filter(|finding| finding.rule == "super-path" || finding.rule == "glob-import")
            .count(),
        expected,
        "{predicate}: {findings:?}"
    );
}

#[test]
fn function_local_globs_require_explicit_names() {
    let input = SourceInput::try_new("src/lib.rs", "fn main() { use std::collections::*; }")
        .expect("small source");
    let findings = lint(&input, &Config::default()).expect("lint source");
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "glob-import");
}
