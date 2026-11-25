#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Path {
    RepeatedDirty,
    RepeatedBarrier,
    GuardedDirty,
    GuardedBarrier,
    RecursiveUnknown,
    RecursiveDirty,
    DistinctProtocols,
    SharedDirtyDiamond,
    SharedReadyDiamond,
    SameResourceArguments,
    DistinctResources,
}

#[hegel::test(print_blob = true)]
fn repeated_protocol_queries_preserve_guards_and_conservative_recursive_effects(
    tc: hegel::TestCase,
) {
    let path = tc.draw(hegel::generators::default::<Path>());
    let (helpers, body, expected) = match path {
        Path::RepeatedDirty => (
            "pub fn dirty(db:&Database){write(db)} pub fn shared(db:&Database){dirty(db);dirty(db)}",
            "shared(db);publish(db);shared(db);publish(db);",
            2,
        ),
        Path::RepeatedBarrier => (
            "pub fn flush(db:&Database){barrier(db)} pub fn shared(db:&Database){flush(db);flush(db)}",
            "write(db);shared(db);publish(db);write(db);shared(db);publish(db);",
            0,
        ),
        Path::GuardedDirty => (
            "",
            "if flag {write(db)} else {barrier(db)} if flag {publish(db)} else {publish(db)}",
            1,
        ),
        Path::GuardedBarrier => (
            "",
            "if flag {write(db)} else {barrier(db)} if flag {barrier(db);publish(db)} else {publish(db)}",
            0,
        ),
        Path::RecursiveUnknown => (
            "pub fn first(db:&Database,flag:bool){if flag{second(db,flag)}} pub fn second(db:&Database,flag:bool){if flag{first(db,flag)}else{barrier(db)}}",
            "write(db);first(db,flag);publish(db);write(db);second(db,flag);publish(db);",
            0,
        ),
        Path::RecursiveDirty => (
            "pub fn first(db:&Database,flag:bool){if flag{second(db,flag)}write(db)} pub fn second(db:&Database,flag:bool){if flag{first(db,flag)}write(db)}",
            "first(db,flag);publish(db);second(db,flag);publish(db);",
            2,
        ),
        Path::SharedDirtyDiamond => (
            "pub fn first(_: &Database){} pub fn second(_: &Database){}",
            "write(db);if flag{first(db)}else{second(db)} if flag{second(db)}else{first(db)} publish(db);",
            1,
        ),
        Path::SharedReadyDiamond => (
            "pub fn first(_: &Database){} pub fn second(_: &Database){}",
            "write(db);if flag{first(db)}else{second(db)} barrier(db);if flag{second(db)}else{first(db)} publish(db);",
            0,
        ),
        Path::SameResourceArguments => (
            "pub fn update(first:&Database,second:&Database){write(first);barrier(second)}",
            "write(db);update(db,db);publish(db);",
            0,
        ),
        Path::DistinctResources => (
            "pub fn update(first:&Database,second:&Database){write(first);barrier(second)}",
            "let other=Database;update(db,&other);publish(db);",
            1,
        ),
        Path::DistinctProtocols => (
            "#[shapelint::protocol(visibility,invalidate)] pub fn obscure(_: &Database){} #[shapelint::protocol(visibility,require)] pub fn observe(_: &Database){} pub fn flush(db:&Database){barrier(db)}",
            "write(db);obscure(db);flush(db);publish(db);observe(db);",
            1,
        ),
    };
    let source = format!(
        r#"
#![feature(register_tool)]
#![register_tool(shapelint)]
pub struct Database;
#[shapelint::protocol(durability,invalidate)] pub fn write(_: &Database){{}}
#[shapelint::protocol(durability,establish)] pub fn barrier(_: &Database){{}}
#[shapelint::protocol(durability,require)] pub fn publish(_: &Database){{}}
{helpers}
pub fn run(db:&Database,flag:bool){{let _=flag;{body}}}
"#
    );
    let output = support::analyze(&source, &[]).expect("protocol analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "protocol-bypass" && finding["item"] == "run"
        })
        .collect();
    assert_eq!(findings.len(), expected, "{path:?}: {output}");
}
