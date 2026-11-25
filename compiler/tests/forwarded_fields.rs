#![feature(rustc_private)]

mod support;

use std::ops::Range;

use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct Diagnostic {
    rule: String,
    message: String,
    primary: Label,
    labels: Vec<Label>,
    footers: Vec<Footer>,
}

#[derive(Debug, Deserialize)]
struct Label {
    span: Range<usize>,
}

#[derive(Debug, Deserialize)]
struct Footer {
    kind: String,
    message: String,
}

fn findings(text: &str) -> Vec<Diagnostic> {
    support::analyze(text, &[])
        .expect("analyze fixture")
        .lines()
        .map(|line| serde_json::from_str::<Diagnostic>(line).expect("diagnostic"))
        .filter(|finding| finding.rule == "forwarded-field")
        .collect()
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum SecondUse {
    Direct,
    Alias,
    Closure,
    Literal,
    Override,
    Arithmetic,
    DifferentField,
    DifferentType,
    DifferentInstantiation,
    Reassigned,
    Callback,
    GeneratedOverride,
    ConstructedOverride,
}

#[hegel::test]
fn every_use_must_forward_the_same_field(tc: hegel::TestCase) {
    let usage = tc.draw(hegel::generators::default::<SecondUse>());
    let second = match usage {
        SecondUse::Direct => "retry(job, policy.max)",
        SecondUse::Alias => "let first = policy.max; let limit = first; retry(job, limit)",
        SecondUse::Closure => "(|| retry(job, policy.max))()",
        SecondUse::Literal => "retry(job, 3)",
        SecondUse::Override => "retry(job, choice.unwrap_or(policy.max))",
        SecondUse::Arithmetic => "retry(job, policy.max + 1)",
        SecondUse::DifferentField => "retry(job, policy.min)",
        SecondUse::DifferentType => "retry(job, other.max)",
        SecondUse::DifferentInstantiation => "retry(job, wide.max)",
        SecondUse::Reassigned => {
            "let mut limit = policy.max; if let Some(n) = choice { limit = n; } retry(job, limit)"
        }
        SecondUse::Callback => "let f: fn(&mut Job, u32) = retry; f(job, policy.max)",
        SecondUse::ConstructedOverride => {
            "retry(job, Limits { max: choice.unwrap_or(policy.max), min: 0 }.max)"
        }
        SecondUse::GeneratedOverride => "macro_rules! go { () => { retry(job, 8) } } go!()",
    };
    let source = format!(
        r#"
        #![allow(unused)]
        pub struct Job {{ attempts: u32 }}
        impl Job {{ fn reschedule(&mut self) {{ self.attempts += 1; }} }}
        pub struct Limits<T> {{ max: u32, min: T }}
        pub struct Other {{ max: u32 }}
        fn retry(job: &mut Job, limit: u32) {{
            if job.attempts < limit {{ job.reschedule(); }}
        }}
        pub fn tick(job: &mut Job, policy: &Limits<u32>) {{ retry(job, policy.max); }}
        pub fn tick_again(job: &mut Job, policy: &Limits<u32>, wide: &Limits<u64>, other: &Other, choice: Option<u32>) {{
            {second}
        }}
    "#
    );
    let diagnostics = findings(&source);
    match (usage, diagnostics.as_slice()) {
        (SecondUse::Direct | SecondUse::Alias | SecondUse::Closure, [finding]) => {
            assert_eq!(
                finding.message,
                "all 2 calls to `retry` supply `Limits<u32>::max`"
            );
            assert_eq!(&source[finding.primary.span.clone()], "policy.max");
            let labels: Vec<_> = finding
                .labels
                .iter()
                .map(|label| &source[label.span.clone()])
                .collect();
            let argument = match usage {
                SecondUse::Alias => "limit",
                _ => "policy.max",
            };
            assert_eq!(labels, ["job.attempts < limit", argument]);
            let [help] = finding.footers.as_slice() else {
                panic!("{finding:?}")
            };
            assert_eq!(help.kind, "help");
            assert!(help.message.contains("`&Limits<u32>`"));
        }
        (
            SecondUse::Literal
            | SecondUse::Override
            | SecondUse::Arithmetic
            | SecondUse::DifferentField
            | SecondUse::DifferentType
            | SecondUse::DifferentInstantiation
            | SecondUse::Reassigned
            | SecondUse::Callback
            | SecondUse::GeneratedOverride
            | SecondUse::ConstructedOverride,
            [],
        ) => {}
        other => panic!("{other:?}"),
    }
}

#[test]
fn labels_the_decision_after_conversion_and_pattern_binding() {
    let source = r#"
        #![allow(dead_code)]
        pub struct Settings { hours: u64 }
        fn durations(text: &str, hours: u64) -> usize {
            let limit = u128::from(hours) * 3_600_000;
            let mut accepted = 0;
            for word in text.split_whitespace() {
                let Ok(amount) = word.replace('_', "").parse::<u128>() else { continue };
                let millis = if word.ends_with("ms") { amount } else { amount.saturating_mul(1000) };
                if millis < limit { continue; }
                accepted += 1;
            }
            accepted
        }
        pub fn check(text: &str, settings: &Settings) -> usize { durations(text, settings.hours) }
    "#;
    let diagnostics = findings(source);
    let [finding] = diagnostics.as_slice() else {
        panic!("{diagnostics:?}")
    };
    assert_eq!(&source[finding.primary.span.clone()], "settings.hours");
    let [decision] = finding.labels.as_slice() else {
        panic!("{finding:?}")
    };
    assert_eq!(&source[decision.span.clone()], "millis < limit");
}

#[test]
fn ignores_logging_forwarding_and_open_signatures() {
    let source = r#"
        #![allow(unused)]
        pub struct Settings { limit: u32, enabled: bool }
        pub struct Log;
        impl Log { fn record(&self, _: bool) {} }
        fn log_flag(log: &Log, flag: bool) { if flag { log.record(flag); } }
        fn log(n: u32, limit: u32) { println!("{limit}"); }
        fn print_comparison(n: u32, limit: u32) { println!("{}", n < limit); }
        fn relay(n: u32, limit: u32) { target(n, limit); }
        pub fn target(n: u32, limit: u32) -> bool { n < limit }
        extern "C" fn foreign(n: u32, limit: u32) -> bool { n < limit }
        fn unrelated(n: u32, limit: u32) -> bool { let copied = limit; copied < limit }
        fn constant(n: u32, limit: u32) -> bool { let number = { let _ = n; 11 }; limit > number }
        trait Check { fn allows(&self, n: u32, limit: u32) -> bool; }
        impl Check for Settings { fn allows(&self, n: u32, limit: u32) -> bool { n < limit } }
        pub fn check(n: u32, s: &Settings) {
            log_flag(&Log, s.enabled);
            log(n, s.limit); print_comparison(n, s.limit); relay(n, s.limit); target(n, s.limit);
            foreign(n, s.limit); unrelated(n, s.limit); constant(n, s.limit); s.allows(n, s.limit);
        }
    "#;
    let diagnostics = findings(source);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
}

#[test]
fn method_and_qualified_calls_agree_on_parameter_position() {
    let source = r#"
        pub struct Job { attempts: u32 }
        pub struct Settings { limit: u32 }
        impl Job { fn eligible(&self, limit: u32) -> bool { self.attempts < limit } }
        pub fn first(job: &Job, s: &Settings) -> bool { job.eligible(s.limit) }
        pub fn second(job: &Job, s: &Settings) -> bool { Job::eligible(job, s.limit) }
    "#;
    let diagnostics = findings(source);
    let [finding] = diagnostics.as_slice() else {
        panic!("{diagnostics:?}")
    };
    assert!(finding.message.contains("all 2 calls"), "{finding:?}");
    assert_eq!(&source[finding.primary.span.clone()], "s.limit");
    assert_eq!(finding.labels.len(), 2);
}

#[test]
fn skips_stale_aliases_inaccessible_records_and_independent_results() {
    let text = r#"
        #![allow(unused)]
        pub struct Policy { max: u32 }
        fn retry(n: u32, max: u32) -> bool { n < max }
        pub fn snapshot(n: u32, p: &mut Policy) -> bool { let saved = p.max; p.max = 0; retry(n, saved) }

        fn outside(n: u32, max: u32) -> bool { n < max }
        mod adapter {
            struct Secret { pub max: u32 }
            fn call(n: u32, policy: &Secret) -> bool { super::outside(n, policy.max) }
        }

        fn ignored(_: u32) -> u32 { 4 }
        struct Pair(u32, u32);
        fn helper(n: u32, limit: u32) -> bool { ignored(n) < limit }
        fn payload(n: u32, limit: u32) -> bool { let Pair(x, _) = Pair(4, n); x < limit }
        fn overwritten(mut n: u32, limit: u32) -> bool { n = 42; n < limit }
        fn print(n: u32, limit: u32) { match n < limit { value => println!("{value}") } }
        pub fn run(n: u32, p: &Policy) {
            helper(n, p.max); payload(n, p.max); overwritten(n, p.max); print(n, p.max);
        }
    "#;
    let diagnostics = findings(text);
    assert!(diagnostics.is_empty(), "{diagnostics:?}");
}

#[test]
fn labels_scalar_decisions_that_control_another_input() {
    let text = r#"
        #[derive(Clone, Copy)] pub enum Mode { Keep, Reset }
        pub struct Options { enabled: bool, mode: Mode, max: u32 }
        fn select(n: u32, mode: Mode) -> u32 { match mode { Mode::Keep => n, Mode::Reset => 0 } }
        fn process(n: &mut u32, enabled: bool) { if enabled { *n = 0; } }
        fn check(n: u32, enabled: bool) -> bool { n > 5 && enabled }
        fn handle(n: u32) -> u32 { n + 1 }
        fn apply(n: u32, enabled: bool) -> u32 { if enabled { handle(n) } else { 0 } }
        fn decrement(n: &mut u32, limit: u32) { if limit > 0 { *n -= 1; } }
        pub async fn run(n: &mut u32, options: &Options) {
            select(*n, options.mode); process(n, options.enabled); apply(*n, options.enabled);
            check(*n, options.enabled); decrement(n, options.max); eligible(*n, options.max).await;
        }
        async fn eligible(n: u32, limit: u32) -> bool { n < limit }
    "#;
    let diagnostics = findings(text);
    let labels: Vec<_> = diagnostics
        .iter()
        .map(|finding| {
            let [decision] = finding.labels.as_slice() else {
                panic!("{finding:?}")
            };
            (
                &text[finding.primary.span.clone()],
                &text[decision.span.clone()],
            )
        })
        .collect();
    assert_eq!(
        labels,
        [
            ("options.mode", "mode"),
            ("options.enabled", "enabled"),
            ("options.enabled", "enabled"),
            ("options.enabled", "enabled"),
            ("options.max", "limit > 0"),
            ("options.max", "n < limit")
        ]
    );
}

#[test]
fn suppression_hides_one_site_without_removing_it_from_the_evidence() {
    let text = r#"
        pub struct Policy { max: u32 }
        fn eligible(n: u32, max: u32) -> bool { n < max }
        // shapelint: allow(forwarded-field) This boundary deliberately takes a scalar.
        pub fn first(n: u32, p: &Policy) -> bool { eligible(n, p.max) }
        pub fn second(n: u32, p: &Policy) -> bool { eligible(n, p.max) }
    "#;
    let diagnostics = findings(text);
    let [finding] = diagnostics.as_slice() else {
        panic!("{diagnostics:?}")
    };
    assert_eq!(
        finding.primary.span.start,
        text.rfind("p.max").expect("second call")
    );
    assert!(finding.message.contains("all 2 calls"), "{finding:?}");
    assert_eq!(finding.labels.len(), 1);
}

#[test]
fn accepts_immediate_copies_and_numeric_method_conversions() {
    let text = r#"
        pub struct Settings { hours: u32 }
        const DEFAULT: Settings = Settings { hours: 1 };
        fn long(millis: u64, hours: u32) -> bool {
            let hours: u64 = hours.into();
            let unit = 3_600_000;
            millis >= hours.saturating_mul(unit)
        }
        pub fn configured(millis: u64, settings: &mut Settings) -> bool {
            let saved = settings.hours;
            let limit = saved;
            long(millis, limit)
        }
        pub fn default_duration(millis: u64) -> bool { long(millis, DEFAULT.hours) }
    "#;
    let diagnostics = findings(text);
    let [finding] = diagnostics.as_slice() else {
        panic!("{diagnostics:?}")
    };
    assert_eq!(
        finding.message,
        "all 2 calls to `long` supply `Settings::hours`"
    );
    assert_eq!(&text[finding.primary.span.clone()], "limit");
    assert_eq!(finding.labels.len(), 2);
}
