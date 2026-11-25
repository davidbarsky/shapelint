#![feature(rustc_private)]

use shapelint::{Config, SourceInput, lint};

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum ScopeCase {
    OrdinaryOptionFilter,
    OrdinaryIteratorFactory,
    OrdinaryGeneratorNamedValue,
    UnrelatedContextType,
    WrappedContextType,
    DeterministicGeneratedOperation,
    UnrelatedDrawMethod,
    UnrelatedDrawFunction,
    ShadowedDrawReceiver,
    ShadowedAssumeReceiver,
    LoopShadowsInput,
    MatchShadowsReceiver,
    IfLetShadowsReceiver,
    TestNamedApply,
    NestedFunction,
    GeneratorClosure,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum PathStyle {
    Compact,
    Spaced,
    Commented,
}

#[hegel::test]
fn hegel_paths_ignore_spacing_and_comments(tc: hegel::TestCase) {
    let style = tc.draw(hegel::generators::default::<PathStyle>());
    let (context, generator) = match style {
        PathStyle::Compact => ("hegel::TestCase", "hegel::generators::integers::<u8>"),
        PathStyle::Spaced => ("hegel :: TestCase", "hegel :: generators :: integers::<u8>"),
        PathStyle::Commented => (
            "hegel::/*context*/TestCase",
            "hegel::generators/*domain*/::integers::<u8>",
        ),
    };
    let text = format!(
        "#[hegel::test] fn f(tc: {context}) {{ let a = tc.draw({generator}().filter(|x| *x != 0)); let b = tc.draw(g()); consume(a, b); }}"
    );
    let input = SourceInput::try_new("src/case.rs", text).expect("small test input");
    let findings = lint(&input, &Config::default()).expect("test input lints");
    let rules: Vec<_> = findings
        .iter()
        .filter_map(|finding| match finding.rule {
            "hegel-scattered-draws" | "hegel-generator-filter" => Some(finding.rule),
            _ => None,
        })
        .collect();
    assert_eq!(
        rules,
        ["hegel-generator-filter", "hegel-scattered-draws"],
        "{style:?}"
    );
}

#[hegel::test]
fn hegel_rules_require_evidence_in_the_current_scope(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<ScopeCase>());
    let text = match case {
        ScopeCase::OrdinaryOptionFilter => {
            "fn f() { let x = Option::<u8>::default().filter(|x| *x > 0); }"
        }
        ScopeCase::OrdinaryIteratorFactory => "fn f() { let x = text().filter(|c| *c != ' '); }",
        ScopeCase::OrdinaryGeneratorNamedValue => {
            "fn f(generator: Values) { let x = generator.filter(|x| x.keep()); }"
        }
        ScopeCase::UnrelatedContextType => {
            "impl Op { fn apply(&self, case: &NotATestCase) { consume(case); } }"
        }
        ScopeCase::WrappedContextType => {
            "#[hegel::test] fn f(tc: Wrapper<TestCase>) { tc.draw(a); tc.draw(b); }"
        }
        ScopeCase::DeterministicGeneratedOperation => {
            "#[derive(hegel::DefaultGenerator)] struct Op; impl Op { fn apply(&self) { paint::draw(shape); } }"
        }
        ScopeCase::UnrelatedDrawMethod => {
            "#[hegel::test] fn f(tc: TestCase) { canvas.draw(a); canvas.draw(b); }"
        }
        ScopeCase::UnrelatedDrawFunction => {
            "#[hegel::test] fn f(tc: TestCase) { draw(a); paint::draw(b); }"
        }
        ScopeCase::ShadowedDrawReceiver => {
            "#[hegel::test] fn f(tc: TestCase) { let x = tc.draw(g()); let tc = canvas; tc.draw(x); }"
        }
        ScopeCase::ShadowedAssumeReceiver => {
            "#[hegel::test] fn f(tc: TestCase) { let tc = solver; tc.assume(condition); }"
        }
        ScopeCase::LoopShadowsInput => {
            "#[hegel::test] fn f(tc: TestCase) { let input = tc.draw(g()); for input in flags { if input { work(); } } }"
        }
        ScopeCase::MatchShadowsReceiver => {
            "#[hegel::test] fn f(tc: TestCase) { match solver { Some(tc) => tc.assume(condition), None => {} } }"
        }
        ScopeCase::IfLetShadowsReceiver => {
            "#[hegel::test] fn f(tc: TestCase) { if let Some(tc) = solver { tc.assume(condition); } }"
        }
        ScopeCase::TestNamedApply => {
            "#[hegel::test] fn apply(tc: TestCase) { let case = tc.draw(g()); run(case); }"
        }
        ScopeCase::NestedFunction => {
            "#[hegel::test] fn f(tc: TestCase) { fn g(tc: TestCase) { let a = tc.draw(g()); let b = tc.draw(g()); } }"
        }
        ScopeCase::GeneratorClosure => {
            "#[hegel::test] fn f(tc: TestCase) { let g = hegel::compose!(|tc| { let a = tc.draw(g()); let b = tc.draw(g()); (a,b) }); let case = tc.draw(g); run(case); }"
        }
    };
    let input = SourceInput::try_new("src/case.rs", text).expect("small test input");
    let findings = lint(&input, &Config::default()).expect("test input lints");
    let unexpected: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule.starts_with("hegel-"))
        .collect();
    assert!(unexpected.is_empty(), "{case:?}: {unexpected:?}\n{text}");
}
