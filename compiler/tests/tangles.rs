#![feature(rustc_private)]

mod support;

use std::ops::Range;

use serde::Deserialize;

#[derive(Debug, Deserialize)]
struct Finding {
    rule: String,
    message: String,
    primary: Label,
    labels: Vec<Label>,
}

#[derive(Debug, Deserialize)]
struct Label {
    message: String,
    span: Range<usize>,
}

fn tangles(text: &str) -> Vec<Finding> {
    support::analyze(text, &["--crate-name=app"])
        .expect("driver analysis")
        .lines()
        .map(|line| serde_json::from_str::<Finding>(line).expect("driver finding"))
        .filter(|finding| finding.rule == "tangle")
        .collect()
}

#[test]
fn the_parent_and_child_have_a_closed_witness_through_a_reexport() {
    let source = r#"
pub mod kernel {
    pub struct Tasks;
    pub use timers::Timers as Clock;
    impl Tasks {
        pub fn sleep(&self, _: &Clock) {}
    }
    pub mod timers {
        pub struct Timers;
        impl Timers {
            pub fn wake(&self, _: &super::Tasks) {}
        }
    }
}
"#;
    let findings = tangles(source);
    let [cycle] = findings.as_slice() else {
        panic!("{findings:?}")
    };
    let tasks = "app::kernel::Tasks";
    let timers = "app::kernel::timers::Timers";
    assert!(cycle.message.contains(&format!("{tasks}, {timers}")));
    assert_eq!(cycle.primary.message, format!("{tasks} uses {timers}"));
    assert_eq!(&source[cycle.primary.span.clone()], "Clock");
    let [closing] = cycle.labels.as_slice() else {
        panic!("{cycle:?}")
    };
    assert_eq!(closing.message, format!("{timers} uses {tasks}"));
    assert_eq!(&source[closing.span.clone()], "Tasks");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Alias {
    Direct,
    ExternalContainer,
    GenericAlias,
}

#[hegel::test]
fn references_follow_the_definition_of_a_type_alias(tc: hegel::TestCase) {
    let alias = tc.draw(hegel::generators::default::<Alias>());
    let definition = match alias {
        Alias::Direct => "pub type Links = B;",
        Alias::ExternalContainer => "pub type Links = Vec<B>;",
        Alias::GenericAlias => "pub type Many<T> = Vec<T>; pub type Links = Many<B>;",
    };
    let text = format!(
        "pub mod a {{ pub struct A(pub crate::b::Links); }}
         pub mod b {{ {definition} pub struct B(pub Box<crate::a::A>); }}"
    );
    let findings = tangles(&text);
    let [cycle] = findings.as_slice() else {
        panic!("{findings:?}")
    };
    assert!(
        cycle
            .message
            .contains("app::a::A, app::b::B, app::b::Links")
    );
    assert_eq!(&text[cycle.primary.span.clone()], "Links");
    assert_eq!(cycle.labels.len(), 2);
}

#[test]
fn declaring_an_impl_through_an_alias_adds_its_methods_to_the_type() {
    let text = r#"
pub struct A;
pub mod aliases {
    pub type Alias = crate::A;
    impl Alias {
        pub fn make() -> Self { Self }
    }
}
"#;
    let findings = tangles(text);
    assert!(findings.is_empty(), "{findings:?}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum TraitBody {
    Default,
    ForeignTypeOverride,
}

#[hegel::test]
fn trait_calls_on_a_foreign_type_retain_the_local_trait(tc: hegel::TestCase) {
    let body = tc.draw(hegel::generators::default::<TraitBody>());
    let declarations = match body {
        TraitBody::Default => {
            "pub trait Ext { fn step(&self) { crate::work::go(Vec::new()); } } impl Ext for Vec<u8> {}"
        }
        TraitBody::ForeignTypeOverride => {
            "pub trait Ext { fn step(&self); } impl Ext for Vec<u8> { fn step(&self) { crate::work::go(Vec::new()); } }"
        }
    };
    let text = format!(
        "{declarations} pub mod work {{ use crate::Ext; pub fn go(v: Vec<u8>) {{ v.step(); }} }}"
    );
    let findings = tangles(&text);
    let [cycle] = findings.as_slice() else {
        panic!("{findings:?}")
    };
    assert!(cycle.message.contains("app::Ext, app::work::go"));
    assert_eq!(&text[cycle.primary.span.clone()], "go");
    let [closing] = cycle.labels.as_slice() else {
        panic!("{cycle:?}")
    };
    assert_eq!(&text[closing.span.clone()], "step");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Dependency {
    SiblingTypes,
    MovedImpl,
    SameModule,
    OneWay,
    IndependentEdgesBetweenModules,
    ImportOnly,
    Generated,
    Suppressed,
}

#[hegel::test]
fn a_tangle_follows_the_items_that_use_each_other(tc: hegel::TestCase) {
    let example = tc.draw(hegel::generators::default::<Dependency>());
    let (source, expected) = match example {
        Dependency::SiblingTypes => (
            "pub mod a { pub struct A; impl A { pub fn see(_: &crate::b::B) {} } } pub mod b { pub struct B; impl B { pub fn see(_: &crate::a::A) {} } }",
            1,
        ),
        Dependency::MovedImpl => (
            "pub struct A; pub struct B; impl B { pub fn see(_: &A) {} } mod glue { impl crate::A { pub fn see(_: &crate::B) {} } }",
            1,
        ),
        Dependency::SameModule => (
            "pub struct A; pub struct B; impl A { pub fn see(_: &B) {} } impl B { pub fn see(_: &A) {} }",
            0,
        ),
        Dependency::OneWay => (
            "pub mod a { pub struct A; impl A { pub fn see(_: &crate::b::B) {} } } pub mod b { pub struct B; }",
            0,
        ),
        Dependency::IndependentEdgesBetweenModules => (
            "pub mod a { pub struct A; pub fn see(_: &crate::b::B) {} } pub mod b { pub struct B; pub fn see(_: &crate::a::A) {} }",
            0,
        ),
        Dependency::ImportOnly => (
            "#![allow(unused_imports)] pub mod a { use crate::b::B; pub struct A; } pub mod b { pub struct B; impl B { pub fn see(_: &crate::a::A) {} } }",
            0,
        ),
        Dependency::Generated => (
            "macro_rules! dep { () => { pub fn see(_: &crate::b::B) {} }; } pub mod a { pub struct A; impl A { dep!(); } } pub mod b { pub struct B; impl B { pub fn see(_: &crate::a::A) {} } }",
            0,
        ),
        Dependency::Suppressed => (
            "pub mod a { pub struct A; impl A {\n// shapelint: allow(tangle)\npub fn see(_: &crate::b::B) {} } } pub mod b { pub struct B; impl B { pub fn see(_: &crate::a::A) {} } }",
            0,
        ),
    };
    let findings = tangles(source);
    assert_eq!(findings.len(), expected, "{example:?}: {findings:?}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Ring {
    Seven,
    Eight,
    Open,
}

#[hegel::test]
fn a_large_recursive_family_in_one_module_exposes_its_ring(tc: hegel::TestCase) {
    let ring = tc.draw(hegel::generators::default::<Ring>());
    let mut source = String::from(
        r#"
pub struct A(pub Box<B>);
pub struct B(pub Box<C>);
pub struct C(pub Box<D>);
pub struct D(pub Box<E>);
pub struct E(pub Box<F>);
pub struct F(pub Box<G>);
"#,
    );
    let (tail, expected) = match ring {
        Ring::Seven => ("pub struct G(pub Box<A>);", 0),
        Ring::Eight => ("pub struct G(pub Box<H>); pub struct H(pub Box<A>);", 1),
        Ring::Open => ("pub struct G(pub Box<H>); pub struct H;", 0),
    };
    source.push_str(tail);
    let findings = tangles(&source);
    assert_eq!(findings.len(), expected, "{ring:?}: {findings:?}");
    for cycle in findings {
        assert_eq!(cycle.labels.len(), 7, "{cycle:?}");
        assert_eq!(&source[cycle.primary.span], "B");
    }
}
