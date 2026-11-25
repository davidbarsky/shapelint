#![feature(rustc_private)]

use insta::assert_snapshot;

use shapelint::{Config, SourceInput, Style, lint, render};

fn check(name: &str, text: &str, config: &Config) -> String {
    let input = SourceInput::try_new(name, text).expect("test source fits in u32");
    let findings = lint(&input, config).expect("test sources are small");
    render(&findings, &input, Style::Plain)
        .trim_end()
        .to_string()
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
