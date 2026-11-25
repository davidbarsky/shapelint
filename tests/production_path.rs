#![feature(rustc_private)]

use shapelint::{Config, SourceInput, lint};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Placement {
    TestCfg,
    ProductionCfg,
    NestedCfg,
    CfgAttribute,
    UnitTest,
    AsyncTest,
    IntegrationTest,
    PlatformCfg,
    MacroTokens,
    StringContents,
    SetupDuplication,
}

#[hegel::test]
fn test_configuration_and_placement_preserve_one_production_path(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Placement>());
    let (path, source, expected) = match case {
        Placement::TestCfg => ("src/lib.rs", "#[cfg(test)] fn helper() {}", 1),
        Placement::ProductionCfg => ("src/lib.rs", "#[cfg(not(test))] fn helper() {}", 1),
        Placement::NestedCfg => ("src/lib.rs", "#[cfg(any(unix, test))] fn helper() {}", 1),
        Placement::CfgAttribute => ("src/lib.rs", "#[cfg_attr(test, inline)] fn helper() {}", 1),
        Placement::UnitTest => ("src/lib.rs", "#[test] fn checks() {}", 1),
        Placement::AsyncTest => ("src/lib.rs", "#[tokio::test] async fn checks() {}", 1),
        Placement::IntegrationTest => ("tests/recovery.rs", "#[test] fn checks() {}", 0),
        Placement::PlatformCfg => ("src/lib.rs", "#[cfg(unix)] fn helper() {}", 0),
        Placement::MacroTokens => (
            "src/lib.rs",
            "macro_rules! example { () => { #[cfg(test)] fn example() {} }; }",
            0,
        ),
        Placement::StringContents => ("src/lib.rs", "const EXAMPLE: &str = \"#[cfg(test)]\";", 0),
        Placement::SetupDuplication => (
            "tests/recovery.rs",
            "#[test] fn first() { let setup = vec![1]; assert_eq!(setup.len(), 1); } #[test] fn second() { let setup = vec![1]; assert_eq!(setup.len(), 1); }",
            0,
        ),
    };
    let input = SourceInput::try_new(path, source).expect("fixture");
    let findings = lint(&input, &Config::default()).expect("valid source");
    let count = findings
        .iter()
        .filter(|finding| finding.rule == "test-only-production-path")
        .count();
    assert_eq!(count, expected, "{case:?}: {findings:?}");
}
