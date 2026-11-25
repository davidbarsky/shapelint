#![feature(rustc_private)]

use insta::assert_snapshot;

use shapelint::{Config, SourceInput, Style, lint, render};

mod rust_rules;

fn check(name: &str, text: &str, config: &Config) -> String {
    let input = SourceInput::try_new(name, text).expect("test source fits in u32");
    let findings = lint(&input, config).expect("test sources are small");
    render(&findings, &input, Style::Plain)
        .trim_end()
        .to_string()
}

fn rules(text: &str) -> Vec<&'static str> {
    let input = SourceInput::try_new("src/lib.rs", text).expect("test source fits in u32");
    lint(&input, &Config::default())
        .expect("test sources are small")
        .iter()
        .map(|f| f.rule)
        .collect()
}

#[test]
fn shallow_helper() {
    assert_snapshot!(check("src/lib.rs", "fn low(v: u64) -> u64 {\n    v & 0xff\n}\nfn f() -> u64 { low(1) + low(2) }\n", &Config::default()), @"
    lint[shallow-helper]: `low` only wraps one expression
      ╭▸ src/lib.rs:1:4
      │
    1 │ fn low(v: u64) -> u64 {
      │    ━━━ one-expression helper
    2 │     v & 0xff
      │     ──────── the whole body
      │
      ├ note: 2 call site(s) in this file
      ╰ help: inline it at the call sites, unless the name states a domain concept or the function owns an invariant

    lint[shallow-helper]: `f` only wraps one expression
      ╭▸ src/lib.rs:4:4
      │
    4 │ fn f() -> u64 { low(1) + low(2) }
      │    ┯            ─────────────── the whole body
      │    │
      │    one-expression helper
      │
      ├ note: 0 call site(s) in this file
      ╰ help: inline it at the call sites, unless the name states a domain concept or the function owns an invariant
    ");
}

#[test]
fn shallow_helper_exemptions() {
    // Named in a serde attribute, used as a value, a constructor, or branching: not inlinable.
    let text = r#"
#[derive(Serialize)]
struct S { #[serde(serialize_with = "ser")] x: u64 }
fn ser(v: &u64) -> String { v.to_string() }
fn as_value(v: u8) -> u8 { v + 1 }
fn g(xs: Vec<u8>) -> Vec<u8> { let ys = xs.into_iter().map(as_value); ys.collect() }
impl S { fn make(x: u64) -> Self { Self { x } } }
fn branches(v: u8) -> u8 { if v > 1 { 1 } else { 0 } }
"#;
    assert!(
        !rules(text).contains(&"shallow-helper"),
        "{:?}",
        rules(text)
    );
}

#[test]
fn nested_free_functions_are_not_impl_methods() {
    let text = r#"
#[derive(Deserialize)]
struct Settings {
    value: Option<String>,
}

impl Settings {
    fn load(&self) {
        fn helper(value: &str) {
            let _ = value.parse::<u8>();
        }
        helper("1");
    }
}
"#;
    assert!(!rules(text).contains(&"config-bag"));
}

#[test]
fn check_passthrough_unit() {
    assert_snapshot!(check("src/lib.rs", r#"
fn validate_row(row: &Row) -> Result<(), E> {
    match (row.op, &row.before, &row.after) {
        (Op::Insert, None, Some(_)) | (Op::Delete, Some(_), None) => Ok(()),
        _ => Err(E),
    }
}
"#, &Config::default()), @"
    lint[check-passthrough]: `validate_row` checks its input and returns `Ok(())`
      ╭▸ src/lib.rs:2:4
      │
    2 │ fn validate_row(row: &Row) -> Result<(), E> {
      │    ━━━━━━━━━━━━ the check's result is discarded
    3 │     match (row.op, &row.before, &row.after) {
      │           ───────────────────────────────── matches a discriminator against Some/None shapes
    4 │         (Op::Insert, None, Some(_)) | (Op::Delete, Some(_), None) => Ok(()),
      │                                                                      ────── returns nothing learned
      │
      ├ help: return a type that records the check (`TryFrom`, `FromStr`, or a constructor), so callers can't keep the unchecked value
      ╰ help: make each legal shape an enum variant that carries exactly its fields
    ");
}

#[test]
fn check_passthrough_returns_inputs() {
    assert_snapshot!(check("src/lib.rs", r#"
fn ensure_sorted(xs: Vec<u8>) -> Result<Vec<u8>, E> {
    if !xs.is_sorted() { return Err(E); }
    Ok(xs)
}
fn caller(a: Vec<u8>, b: Vec<u8>) { ensure_sorted(a); ensure_sorted(b); }
"#, &Config::default()), @"
    lint[check-passthrough]: `ensure_sorted` checks its inputs and returns them unchanged
      ╭▸ src/lib.rs:2:4
      │
    2 │ fn ensure_sorted(xs: Vec<u8>) -> Result<Vec<u8>, E> {
      │    ━━━━━━━━━━━━━ callers keep the unrefined values
    3 │     if !xs.is_sorted() { return Err(E); }
    4 │     Ok(xs)
      │     ────── returns its inputs
      │
      ├ help: return a type that records the check (`TryFrom`, `FromStr`, or a constructor), so callers can't keep the unchecked value
      ╰ note: called 2 times in this file; each call repeats the check
    ");
}

#[test]
fn check_passthrough_commands_are_silent() {
    // `Ok(())` from a command is fine, including `&mut self` and async ones.
    let text = r#"
impl Cell { fn set(&mut self, v: u8) -> Result<(), E> { if v > 3 { return Err(E); } self.v = v; Ok(()) } }
async fn send(x: u8) -> Result<(), E> { if x == 0 { return Err(E); } Ok(()) }
"#;
    assert!(
        !rules(text).contains(&"check-passthrough"),
        "{:?}",
        rules(text)
    );
}

#[test]
fn check_passthrough_includes_mut_async_and_tests() {
    let text = r#"
impl V { fn validate(&mut self) -> Result<(), E> { if self.n == 0 { return Err(E); } Ok(()) } }
async fn verify(x: u8) -> Result<(), E> { if x == 0 { return Err(E); } Ok(()) }
#[test] fn check_it() -> Result<(), E> { if 1 == 2 { return Err(E); } Ok(()) }
"#;
    assert_eq!(
        rules(text)
            .iter()
            .filter(|r| **r == "check-passthrough")
            .count(),
        3,
        "{:?}",
        rules(text)
    );
}

#[test]
fn config_bag() {
    assert_snapshot!(check("src/bin/topics.rs", r#"
#[derive(Deserialize)]
struct Connector {
    tables: String,
    #[serde(flatten)]
    properties: BTreeMap<String, String>,
}
impl Connector {
    fn topics(&self) -> Vec<String> { self.tables.split(',').map(String::from).collect() }
    fn property(&self, t: &str) -> Option<&String> { self.properties.get(&format!("transforms.{t}")) }
}
"#, &Config::default()), @r#"
    lint[config-bag]: `Connector.properties` collects unmodeled keys into a flattened string map
      ╭▸ src/bin/topics.rs:6:5
      │
    6 │     properties: BTreeMap<String, String>,
      │     ━━━━━━━━━━ catch-all for config the type doesn't model
      │
      ╰ help: deserialize known keys into typed fields or variants; keep the map only for true extensions

    lint[config-bag]: `Connector::topics` re-parses deserialized config at use time
      ╭▸ src/bin/topics.rs:9:8
      │
    9 │     fn topics(&self) -> Vec<String> { self.tables.split(',').map(String::from).collect() }
      │        ━━━━━━ parses config after loading         ───── splits a string at use time
      │
      ╰ help: move this into deserialization (typed variants, compiled patterns) so bad config fails when it loads

    lint[shallow-helper]: `Connector::topics` only wraps one expression
      ╭▸ src/bin/topics.rs:9:8
      │
    9 │     fn topics(&self) -> Vec<String> { self.tables.split(',').map(String::from).collect() }
      │        ━━━━━━ one-expression helper   ────────────────────────────────────────────────── the whole body
      │
      ├ note: 0 call site(s) in this file
      ╰ help: inline it at the call sites, unless the name states a domain concept or the function owns an invariant

    lint[config-bag]: `Connector::property` re-parses deserialized config at use time
       ╭▸ src/bin/topics.rs:10:8
       │
    10 │     fn property(&self, t: &str) -> Option<&String> { self.properties.get(&format!("transforms.{t}")) }
       │        ━━━━━━━━ parses config after loading                               ───────────────────────── builds a lookup key at use time
       │
       ╰ help: move this into deserialization (typed variants, compiled patterns) so bad config fails when it loads

    lint[shallow-helper]: `Connector::property` only wraps one expression
       ╭▸ src/bin/topics.rs:10:8
       │
    10 │     fn property(&self, t: &str) -> Option<&String> { self.properties.get(&format!("transforms.{t}")) }
       │        ━━━━━━━━ one-expression helper                ─────────────────────────────────────────────── the whole body
       │
       ├ note: 0 call site(s) in this file
       ╰ help: inline it at the call sites, unless the name states a domain concept or the function owns an invariant
    "#);
}

#[test]
fn unit_fields_reports_each_stem() {
    let text = "struct T {\n    ts_ms: i64,\n    ts_us: Option<i64>,\n    ttl_ms: u64,\n    ttl_s: Option<u64>,\n}\n";
    assert_snapshot!(check("src/lib.rs", text, &Config::default()), @"
    lint[unit-fields]: `T` has fields for `ts` with different unit suffixes (`ts_ms`, `ts_us`)
      ╭▸ src/lib.rs:1:8
      │
    1 │ struct T {
      │        ━ 2 fields share the stem `ts`
    2 │     ts_ms: i64,
      │     ────────── required field
    3 │     ts_us: Option<i64>,
      │     ────────────────── optional field
      │
      ╰ help: Check how producers and consumers combine these fields. Parse alternative encodings into one typed value. Keep additive components distinct when both contribute.

    lint[unit-fields]: `T` has fields for `ttl` with different unit suffixes (`ttl_ms`, `ttl_s`)
      ╭▸ src/lib.rs:1:8
      │
    1 │ struct T {
      │        ━ 2 fields share the stem `ttl`
      ┆
    4 │     ttl_ms: u64,
      │     ─────────── required field
    5 │     ttl_s: Option<u64>,
      │     ────────────────── optional field
      │
      ╰ help: Check how producers and consumers combine these fields. Parse alternative encodings into one typed value. Keep additive components distinct when both contribute.
    ");
    let input = SourceInput::try_new("src/lib.rs", text).expect("test source fits in u32");
    let findings = lint(&input, &Config::default()).expect("small");
    assert_ne!(findings[0].fingerprint, findings[1].fingerprint);
}

#[test]
fn identity_string() {
    assert_snapshot!(check("src/lib.rs", r#"
struct AssemblyConfig { source: String, group_id: String, brokers: Vec<String> }
fn handle(records: &[u8], destination: &str) {}
"#, &Config::default()), @"
    lint[identity-string]: `AssemblyConfig` stores 2 identity values as plain strings (`source`, `group_id`)
      ╭▸ src/lib.rs:2:8
      │
    2 │ struct AssemblyConfig { source: String, group_id: String, brokers: Vec<String> }
      │        ┯━━━━━━━━━━━━━   ┬─────────────  ──────────────── string identity
      │        │                │
      │        │                string identity
      │        string identities
      │
      ╰ help: give each identity a newtype so they can't be swapped or mixed with other strings

    lint[identity-string]: `handle` takes identity values as plain strings (`destination`)
      ╭▸ src/lib.rs:3:27
      │
    3 │ fn handle(records: &[u8], destination: &str) {}
      │                           ━━━━━━━━━━━━━━━━━ string identity
      │
      ╰ help: give each identity a newtype so it can't be swapped with or mistaken for another string
    ");
}

#[test]
fn byte_format() {
    assert_snapshot!(check("src/lib.rs", r#"
fn key(id: u64, n: u64) -> Vec<u8> {
    [8_u64.to_be_bytes().as_slice(), &id.to_be_bytes(), b"x", &n.to_be_bytes()].concat()
}
"#, &Config::default()), @r#"
    lint[shallow-helper]: `key` only wraps one expression
      ╭▸ src/lib.rs:2:4
      │
    2 │ fn key(id: u64, n: u64) -> Vec<u8> {
      │    ━━━ one-expression helper
    3 │     [8_u64.to_be_bytes().as_slice(), &id.to_be_bytes(), b"x", &n.to_be_bytes()].concat()
      │     ──────────────────────────────────────────────────────────────────────────────────── the whole body
      │
      ├ note: 0 call site(s) in this file
      ╰ help: inline it at the call sites, unless the name states a domain concept or the function owns an invariant

    lint[byte-format]: byte format assembled by hand from 3 `to_*_bytes()` pieces
      ╭▸ src/lib.rs:3:81
      │
    3 │     [8_u64.to_be_bytes().as_slice(), &id.to_be_bytes(), b"x", &n.to_be_bytes()].concat()
      │            ┬──────────                   ┬──────────             ┬──────────    ━━━━━━ assembled here
      │            │                             │                       │
      │            piece                         piece                   piece
      │
      ╰ help: give the format a type with one encoder and reuse it (search for an existing one first)
    "#);
}

#[test]
fn optional_state() {
    assert_snapshot!(check("src/lib.rs", r#"
struct A { stamp: Option<Stamp> }
impl A {
    fn one(&self) -> Result<u8, E> { let Some(s) = self.stamp.as_ref() else { return Err(E) }; Ok(s.n) }
    fn two(&self) -> u8 { self.stamp.as_ref().expect("set in phase two").n }
}
"#, &Config::default()), @r#"
    lint[optional-state]: methods of `A` re-check that `self.stamp` is `Some`
      ╭▸ src/lib.rs:3:6
      │
    3 │ impl A {
      │      ━ optional state
    4 │     fn one(&self) -> Result<u8, E> { let Some(s) = self.stamp.as_ref() else { return Err(E) }; Ok(s.n) }
      │                                                    ─────────────────── checked again here
    5 │     fn two(&self) -> u8 { self.stamp.as_ref().expect("set in phase two").n }
      │                           ────────────────────────────────────────────── checked again here
      │
      ╰ help: model the phases as an enum, or pass the present value, so code that needs it can't run without it

    lint[shallow-helper]: `A::two` only wraps one expression
      ╭▸ src/lib.rs:5:8
      │
    5 │     fn two(&self) -> u8 { self.stamp.as_ref().expect("set in phase two").n }
      │        ┯━━                ──────────────────────────────────────────────── the whole body
      │        │
      │        one-expression helper
      │
      ├ note: 0 call site(s) in this file
      ╰ help: inline it at the call sites, unless the name states a domain concept or the function owns an invariant
    "#);
}

#[test]
fn blocking_rationale() {
    let text = r#"
async fn open() {
    let a = spawn_blocking(move || fetch());

    // fetch_metadata blocks on the broker.
    let b = spawn_blocking(move || fetch());
}
"#;
    assert_snapshot!(check("src/lib.rs", text, &Config::default()), @"
    lint[blocking-rationale]: `spawn_blocking` has no comment saying which call blocks
      ╭▸ src/lib.rs:3:13
      │
    3 │     let a = spawn_blocking(move || fetch());
      │             ━━━━━━━━━━━━━━ offloaded to a blocking thread
      │
      ╰ help: add a comment naming the blocking call, or drop the offload if nothing inside blocks
    ");
}

#[test]
fn fallible_constructors_can_be_named_new() {
    let text = r#"
struct Port(u16);
impl Port {
    pub fn new(value: u32) -> Result<Self, std::num::TryFromIntError> {
        let port = u16::try_from(value)?;
        Ok(Self(port))
    }
}
"#;
    assert_eq!(check("src/lib.rs", text, &Config::default()), "");
}

#[test]
fn for_chain_and_for_each() {
    assert_snapshot!(check("src/lib.rs", "fn f(xs: &[u8]) {\n    for x in xs.iter().copied().filter(|x| *x > 1) {}\n    xs.iter().for_each(|x| drop(x));\n    for x in xs.iter() {}\n}\n", &Config::default()), @"
    lint[for-chain]: `for` header builds a 3-call iterator chain
      ╭▸ src/lib.rs:2:33
      │
    2 │     for x in xs.iter().copied().filter(|x| *x > 1) {}
      │              ┬──────────────────┯━━━━━────────────
      │              │                  │
      │              │                  chain ends here
      │              iterator chain
      │
      ╰ help: bind the chain to a named variable, then loop over the variable

    lint[for-chain]: `for_each` used where a `for` loop would do
      ╭▸ src/lib.rs:3:15
      │
    3 │     xs.iter().for_each(|x| drop(x));
      │               ━━━━━━━━ for_each
      │
      ╰ help: use a `for` loop
    ");
}

#[test]
fn tuple_return_and_destructuring() {
    assert_snapshot!(check("src/lib.rs", "fn trio() -> (u8, String, char) { todo!() }\nfn g() { let (a, b, c, d) = quad(); }\nfn pair() -> (u8, String) { todo!() }\n", &Config::default()), @"
    lint[tuple-return]: `trio` returns a 3-tuple
      ╭▸ src/lib.rs:1:14
      │
    1 │ fn trio() -> (u8, String, char) { todo!() }
      │              ━━━━━━━━━━━━━━━━━━ 3-tuple
      │
      ╰ help: use a struct with named fields, or an enum if the parts are alternatives

    lint[tuple-return]: destructures a 4-tuple
      ╭▸ src/lib.rs:2:14
      │
    2 │ fn g() { let (a, b, c, d) = quad(); }
      │              ━━━━━━━━━━━━ 4 positional parts
      │
      ╰ help: use a struct with named fields, or an enum if the parts are alternatives
    ");
}

#[test]
fn std_trait_fn() {
    assert_snapshot!(check("src/lib.rs", "fn parse_operation(s: &str) -> Result<Operation, E> { todo!() }\n", &Config::default()), @"
    lint[std-trait-fn]: `parse_operation` takes `&str` and returns `Result<Operation, E>`
      ╭▸ src/lib.rs:1:4
      │
    1 │ fn parse_operation(s: &str) -> Result<Operation, E> { todo!() }
      │    ━━━━━━━━━━━━━━━ named parser
      │
      ╰ help: Use `FromStr` for the canonical text format of a type this crate owns. Keep a named parser for a specific radix or format. Check existing implementations before changing callers.
    ");
}

#[test]
fn glob_import() {
    assert_snapshot!(check("src/lib.rs", r#"
use std::collections::*;
pub use inner::*;
fn f() { use Kind::{First, Second}; }
#[cfg(test)]
mod tests { use super::*; }
"#, &Config::default()), @"
    lint[glob-import]: `use std::collections::*;` imports every public name
      ╭▸ src/lib.rs:2:23
      │
    2 │ use std::collections::*;
      │                       ━ glob
      │
      ╰ help: name the items you use; globs are allowed only for `use super::*` in tests and public re-exports

    lint[test-only-production-path]: test configuration changes the compiled implementation
      ╭▸ src/lib.rs:5:1
      │
    5 │ #[cfg(test)]
      │ ━━━━━━━━━━━━ test-dependent compilation
      │
      ╰ help: Keep one production implementation and place tests in a separate tests directory.
    ");
}

#[test]
fn suppression_comment_above_item() {
    let text = "// shapelint: allow(shallow-helper) names the wire format's mask\nfn low(v: u64) -> u64 { v & 0xff }\n";
    assert_snapshot!(check("src/lib.rs", text, &Config::default()), @"");
}

#[test]
fn unknown_allow_suggests_the_rule() {
    assert_snapshot!(check("src/lib.rs", "// shapelint: allow(shallow-helpr)\nfn low(v: u64) -> u64 { v & 0xff }\n", &Config::default()), @"
    lint[unknown-allow]: `shapelint: allow(shallow-helpr)` names a rule that doesn't exist
      ╭▸ src/lib.rs:1:21
      │
    1 │ // shapelint: allow(shallow-helpr)
      │                     ━━━━━━━━━━━━━ no rule named `shallow-helpr`
      ╰╴
    help: did you mean `shallow-helper`?
      ╭╴
    1 │ // shapelint: allow(shallow-helper)
      ╰╴                                +

    lint[shallow-helper]: `low` only wraps one expression
      ╭▸ src/lib.rs:2:4
      │
    2 │ fn low(v: u64) -> u64 { v & 0xff }
      │    ┯━━                  ──────── the whole body
      │    │
      │    one-expression helper
      │
      ├ note: 0 call site(s) in this file
      ╰ help: inline it at the call sites, unless the name states a domain concept or the function owns an invariant
    ");
}

#[test]
fn allow_in_a_string_is_not_a_comment() {
    let text = "fn msg() -> &'static str {\n    \"add // shapelint: allow(<rule>)\"\n}\n";
    assert!(!rules(text).contains(&"unknown-allow"), "{:?}", rules(text));
}
