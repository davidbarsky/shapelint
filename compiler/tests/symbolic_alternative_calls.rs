#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum PrefixOrder {
    Forward,
    Reversed,
}

#[hegel::test]
fn shared_callable_prefixes_keep_dispatch_completion_and_recursive_contexts(tc: hegel::TestCase) {
    let order = tc.draw(hegel::generators::default::<PrefixOrder>());
    let prefix = match order {
        PrefixOrder::Forward => "if choose { first } else { second }",
        PrefixOrder::Reversed => "if choose { second } else { first }",
    };
    let source = format!(
        r#"
fn first(_:u32)->u32 {{ 0 }}
fn second(_:u32)->u32 {{ 0 }}
fn third(_:u32)->u32 {{ 0 }}
fn recursive(value:u32)->u32 {{
    if value == 0 {{ 0 }} else {{ recursive(value) }}
}}
fn prefix(choose:bool)->fn(u32)->u32 {{ {prefix} }}
fn extend(previous:fn(u32)->u32, choose:bool)->fn(u32)->u32 {{
    if choose {{ previous }} else {{ third }}
}}
fn extend_recursive(previous:fn(u32)->u32, choose:bool)->fn(u32)->u32 {{
    if choose {{ previous }} else {{ recursive }}
}}
fn apply(callback:fn(u32)->u32, value:u32)->u32 {{ callback(value) }}
pub fn known_bad(a:bool,b:bool)->u32 {{
    let shared = prefix(a);
    let longer = extend(shared,b);
    apply(shared,0);
    apply(longer,0)-1
}}
pub fn recursive_uncertain(a:bool,b:bool,c:bool,value:u32)->u32 {{
    let shared = prefix(a);
    let longer = extend(shared,b);
    let longest = extend_recursive(longer,c);
    apply(shared,value);
    apply(longer,value);
    apply(longest,value)-1
}}
pub fn recursive_base_bad(a:bool,b:bool,c:bool)->u32 {{
    let shared = prefix(a);
    let longer = extend(shared,b);
    let longest = extend_recursive(longer,c);
    apply(shared,0);
    apply(longer,0);
    apply(longest,0)-1
}}
"#
    );
    let output = support::analyze(&source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "invalid-state-use")
        .collect();
    let mut items: Vec<_> = findings
        .iter()
        .map(|finding| finding["item"].as_str().expect("item"))
        .collect();
    items.sort_unstable();
    assert_eq!(
        items,
        ["known_bad", "recursive_base_bad"],
        "{order:?}: {output}"
    );
}
