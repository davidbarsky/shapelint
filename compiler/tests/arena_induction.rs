mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Step {
    Append,
    ReplaceStore,
    HiddenReset,
    ForeignChild,
    DerefField,
    DerefOutsideOwner,
    ForgeResult,
    Callback,
    DropLocal,
    DropPayload,
    PrimitiveCallback,
    ExternalExecutor,
    UnsafeHelper,
    LeafRequirement,
    PrimitiveRequirement,
}

#[hegel::test]
fn recursive_arena_roots_follow_the_receiver(tc: hegel::TestCase) {
    let step = tc.draw(hegel::generators::default::<Step>());
    let body = match step {
        Step::Append
        | Step::PrimitiveRequirement
        | Step::PrimitiveCallback
        | Step::ExternalExecutor
        | Step::DropPayload => "self.nodes.publish(first)",
        Step::ReplaceStore => "{ self.nodes = Store::new(); first }",
        Step::HiddenReset => "{ self.reset(); first }",
        Step::ForeignChild => "self.second.read(first).0",
        Step::DerefField => "self.foreign.read(first).0",
        Step::DerefOutsideOwner => "self.outside.read(first).0",
        Step::ForgeResult => "Id(999)",
        Step::Callback => "(self.callback)(first)",
        Step::UnsafeHelper => "unsafe { self.from_bits() }",
        Step::DropLocal => "{ let _value = Trap; first }",
        Step::LeafRequirement => "{ None::<u8>.unwrap(); first }",
    };
    let append = match step {
        Step::PrimitiveRequirement => "None::<u8>.unwrap(); root",
        Step::PrimitiveCallback => "(self.0)(root)",
        Step::DropPayload => "let _ = self.1.take(); root",
        Step::ExternalExecutor => "Some(root).map(|x| { None::<u8>.unwrap(); x }); root",
        _ => "root",
    };
    let source = r#"
#![feature(register_tool)]
#![register_tool(shapelint_tool)]
#![allow(dead_code)]
#[derive(Clone, Copy, PartialEq, Eq)] pub struct Id(u32);
struct Trap;
impl Drop for Trap { fn drop(&mut self) { None::<u8>.unwrap(); } }
struct Store<R>(fn(R) -> R, std::cell::Cell<Option<Trap>>);
impl<R: Copy> Store<R> {
    fn new() -> Self { Store(|id| id, std::cell::Cell::new(Some(Trap))) }
    #[shapelint_tool::arena(read)]
    fn read(&self, root: R) -> (R, R) { (root, root) }
    #[shapelint_tool::arena(append)]
    fn publish(&self, root: R) -> R { APPEND }
}
pub struct Other { foreign: Store<Id>, pad: [(); 0], q: u8, r: u8, s: u8, outside: Store<Id> }
pub struct Forest {
    #[shapelint_tool::arena(storage)] nodes: Store<Id>,
    second: Store<Id>,
    proxy: Other,
    visits: usize,
    callback: fn(Id) -> Id,
}
impl std::ops::Deref for Forest { type Target = Other; fn deref(&self) -> &Other { &self.proxy } }
impl Forest {
    unsafe fn from_bits(&self) -> Id { Id(999) }
    fn reset(&mut self) { std::mem::swap(&mut self.nodes, &mut self.second); }
    pub fn descend(&mut self, root: Id, leaf: bool) -> Id {
        self.visits = self.visits.saturating_add(1);
        if leaf { return root; }
        let (left, right) = self.nodes.read(root);
        let first = self.descend(left, true);
        let next = BODY;
        if first == right { next } else { self.descend(next, true) }
    }
}
pub fn invoke(forest: &mut Forest, root: Id, leaf: bool) -> Id { forest.descend(root, leaf) }
"#
    .replace("APPEND", append)
    .replace("BODY", body);
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("driver analysis");
    let findings = output
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .collect::<Vec<_>>();
    let recursion = findings.iter().any(|finding| {
        finding["item"] == "invoke"
            && finding["primary"]["message"] == "recursive call requirements"
    });
    match step {
        Step::Append => assert!(!recursion, "{step:?}: {output}"),
        Step::LeafRequirement | Step::PrimitiveRequirement => {
            assert!(recursion, "{step:?}: {output}");
            assert!(
                findings
                    .iter()
                    .any(|f| f["rule"] == "invalid-variant-access"),
                "{step:?}: {output}"
            );
        }
        _ => assert!(recursion, "{step:?}: {output}"),
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Root {
    Scalar,
    DifferentLifetime,
    DifferentTypeArgument,
    NestedRoot,
}

#[hegel::test]
fn induction_uses_the_storage_fields_root_type(tc: hegel::TestCase) {
    let root = tc.draw(hegel::generators::default::<Root>());
    let (extra, hint) = match root {
        Root::Scalar => ("Id<'g, u32>", ""),
        Root::DifferentLifetime => ("Id<'h, u32>", ""),
        Root::DifferentTypeArgument => ("Id<'g, u64>", ""),
        Root::NestedRoot => ("Id<'g, u32>", ", Option<&'g Self>"),
    };
    let src = format!(
        r#"
#![feature(register_tool)]
#![register_tool(shapelint_tool)]
#![allow(dead_code)]
#[derive(Clone, Copy)] pub struct Id<'g, T>(u32, std::marker::PhantomData<fn(&'g T) -> &'g T>{hint});
struct Table<R>(std::marker::PhantomData<R>);
pub struct Tree<'g,'h> {{
    #[shapelint_tool::arena(storage)] table: Table<Id<'g, u32>>,
    marker: std::marker::PhantomData<&'h ()>,
}}
impl<'g,'h> Tree<'g,'h> {{
    pub fn walk(&mut self, root: Id<'g, u32>, extra: {extra}, leaf: bool) -> {extra} {{
        if leaf {{ return extra }}
        let result = self.walk(root, extra, true);
        self.walk(root, result, true)
    }}
}}
"#
    );
    let output = support::analyze(&src, &["--show-analysis-gaps"]).expect("analyze root types");
    let gaps = output
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .filter(|f| f["primary"]["message"] == "recursive call requirements")
        .count();
    match root {
        Root::Scalar => assert_eq!(gaps, 0, "{output}"),
        _ => assert!(gaps > 0, "{root:?}: {output}"),
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum PredicateStep {
    StoredChildren,
    ForeignChild,
    ForgedChild,
    FallibleRead,
}

#[hegel::test]
fn recursive_predicates_check_child_ids_and_preserve_both_outcomes(tc: hegel::TestCase) {
    let step = tc.draw(hegel::generators::default::<PredicateStep>());
    let (read, child) = match step {
        PredicateStep::StoredChildren => ("(root, root)", "right"),
        PredicateStep::ForeignChild => ("(root, root)", "self.other.children(root, accept).1"),
        PredicateStep::ForgedChild => ("(root, root)", "Id(999)"),
        PredicateStep::FallibleRead => ("if accept { None::<u8>.unwrap(); } (root, root)", "right"),
    };
    let source = format!(
        r#"
#![feature(register_tool)]
#![register_tool(shapelint_tool)]
#![allow(dead_code, unused_variables)]
#[derive(Clone, Copy)] pub struct Id(u32);
struct Store<R>(std::marker::PhantomData<R>);
impl<R: Copy> Store<R> {{
    #[shapelint_tool::arena(read)]
    fn children(&self, root: R, accept: bool) -> (R, R) {{ {read} }}
}}
pub struct Tree {{
    #[shapelint_tool::arena(storage)] nodes: Store<Id>,
    other: Store<Id>,
}}
impl Tree {{
    fn probe(&mut self, root: Id, recurse: bool, accept: bool) -> Option<()> {{
        if recurse {{
            let (left, right) = self.nodes.children(root, accept);
            self.probe(left, false, accept)?;
            self.probe({child}, false, accept)
        }} else if accept {{ Some(()) }} else {{ None }}
    }}
}}
pub fn observe(tree: &mut Tree, root: Id, recurse: bool, accept: bool, present: u8, missing: u8) -> u8 {{
    match tree.probe(root, recurse, accept) {{
        Some(()) => present - 1,
        None => missing - 1,
    }}
}}
"#
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analyze predicate");
    let findings = output
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .collect::<Vec<_>>();
    let gaps = findings
        .iter()
        .filter(|f| f["primary"]["message"] == "recursive call requirements")
        .count();
    match step {
        PredicateStep::StoredChildren => {
            assert_eq!(gaps, 0, "{output}");
            let requirements = findings
                .iter()
                .filter(|f| f["item"] == "observe" && f["rule"] == "unproven-precondition")
                .map(|f| f["primary"]["message"].as_str().expect("requirement"))
                .collect::<Vec<_>>();
            assert_eq!(
                requirements,
                ["requires present >= 1", "requires missing >= 1"],
                "{output}"
            );
        }
        PredicateStep::ForeignChild | PredicateStep::ForgedChild => {
            assert!(gaps > 0, "{step:?}: {output}")
        }
        PredicateStep::FallibleRead => {
            assert!(gaps > 0, "{output}");
            assert!(
                findings
                    .iter()
                    .any(|f| f["rule"] == "invalid-variant-access"),
                "{output}"
            );
        }
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ArenaSignature {
    UnitOptionAlias,
    RootPayload,
    UserOption,
    NestedResult,
    NoRootInput,
    SameError,
    ConvertedError,
}

#[hegel::test]
fn induction_checks_the_root_input_output_and_residual_conversion(tc: hegel::TestCase) {
    let signature = tc.draw(hegel::generators::default::<ArenaSignature>());
    let (input, output, answer) = match signature {
        ArenaSignature::UnitOptionAlias => ("Id", "Answer", "Some(())"),
        ArenaSignature::RootPayload => ("Id", "Option<Id>", "Some(root)"),
        ArenaSignature::UserOption => ("Id", "custom::Option<()>", "custom::Option(())"),
        ArenaSignature::NestedResult => ("Id", "Result<Option<()>, ()>", "Ok(Some(()))"),
        ArenaSignature::NoRootInput => ("u32", "Option<()>", "Some(())"),
        ArenaSignature::SameError => ("Id", "Result<Id, Source>", "Ok(self.read(root)?)"),
        ArenaSignature::ConvertedError => ("Id", "Result<Id, Target>", "Ok(self.read(root)?)"),
    };
    let source = format!(
        r#"
#![feature(register_tool)]
#![register_tool(shapelint_tool)]
#![allow(dead_code)]
#[derive(Clone, Copy)] pub struct Id(u32);
type Answer = Option<()>;
mod custom {{ pub struct Option<T>(pub T); }}
pub struct Source;
pub struct Target;
impl From<Source> for Target {{ fn from(_: Source) -> Self {{ Target }} }}
struct Store<R>(std::marker::PhantomData<R>);
pub struct Tree {{ #[shapelint_tool::arena(storage)] nodes: Store<Id> }}
impl Tree {{
    fn read(&self, root: Id) -> Result<Id, Source> {{
        if root.0 == 0 {{ Err(Source) }} else {{ Ok(root) }}
    }}
    pub fn probe(&self, root: {input}, leaf: bool) -> {output} {{
        if leaf {{ {answer} }} else {{ self.probe(root, true) }}
    }}
}}
"#
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analyze signature");
    let gaps = output
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .filter(|f| f["primary"]["message"] == "recursive call requirements")
        .count();
    match signature {
        ArenaSignature::UnitOptionAlias | ArenaSignature::SameError => {
            assert_eq!(gaps, 0, "{output}")
        }
        _ => assert!(gaps > 0, "{signature:?}: {output}"),
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum OptionalId {
    Input,
    Maximum,
    MaximumWithForgedInput,
    UnrelatedOption,
    CheckedAddition,
    QuestionMark,
    ProjectedPayload,
    HigherRankedPayload,
}

#[hegel::test]
fn standard_operations_cannot_mint_an_arena_id(tc: hegel::TestCase) {
    let id = tc.draw(hegel::generators::default::<OptionalId>());
    let (payload, field) = match id {
        OptionalId::ProjectedPayload => {
            ("PhantomData<<Owner as Payload>::Value>", "PhantomData<i32>")
        }
        OptionalId::HigherRankedPayload => (
            "PhantomData<fn(&'static u8)>",
            "PhantomData<for<'a> fn(&'a u8)>",
        ),
        _ => ("u32", "u32"),
    };
    let candidate = match id {
        OptionalId::Input => "root",
        OptionalId::Maximum => "root.max(root)",
        OptionalId::MaximumWithForgedInput => "root.max(41u32.checked_add(1))",
        OptionalId::UnrelatedOption => "let _small = 3u8.checked_add(4); root",
        OptionalId::CheckedAddition => "41u32.checked_add(1)",
        OptionalId::QuestionMark => "self.table.answer(root)?; root",
        OptionalId::ProjectedPayload | OptionalId::HigherRankedPayload => {
            "let forged = self.table.row(root).map(|row| row.field); forged"
        }
    };
    let source = format!(
        r#"
#![feature(register_tool)]
#![register_tool(shapelint_tool)]
#![allow(dead_code, unused_variables)]
use std::marker::PhantomData;
pub trait Payload {{ type Value; }}
pub struct Owner;
impl Payload for Owner {{ type Value = i32; }}
type Id = Option<{payload}>;
#[derive(Clone, Copy)] struct Row {{ field: {field} }}
struct Table<R>(PhantomData<R>, Option<()>, Option<Row>);
impl<R> Table<R> {{
    #[shapelint_tool::arena(read)]
    fn answer(&self, _: R) -> Option<()> {{ self.1 }}
    #[shapelint_tool::arena(read)]
    fn row(&self, _: R) -> Option<Row> {{ self.2 }}
}}
pub struct Tree {{ #[shapelint_tool::arena(storage)] table: Table<Id> }}
impl Tree {{
    fn candidate(&self, root: Id) -> Id {{ {candidate} }}
    pub fn probe(&self, root: Id, recurse: bool) -> Option<()> {{
        if recurse {{ self.probe(self.candidate(root), false) }} else {{ self.table.answer(root) }}
    }}
}}
"#
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analyze optional ID");
    let gaps = output
        .lines()
        .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
        .filter(|f| f["primary"]["message"] == "recursive call requirements")
        .count();
    match id {
        OptionalId::Input | OptionalId::Maximum | OptionalId::UnrelatedOption => {
            assert_eq!(gaps, 0, "{output}")
        }
        _ => assert!(gaps > 0, "{id:?}: {output}"),
    }
}

#[test]
fn an_unmodeled_dependency_inside_a_local_storage_method_keeps_the_gap() {
    let directory = tempfile::tempdir().expect("dependency directory");
    let lib = directory.path().join("backend.rs");
    std::fs::write(&lib, "pub fn accept<R>(r:R)->R { None::<u8>.unwrap(); r }")
        .expect("write dependency");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--crate-type=lib",
            "--crate-name=backend",
            "--edition=2024",
            "--emit=metadata",
            "--summary-output",
        ])
        .arg(directory.path().join("backend.json"))
        .arg("-o")
        .arg(directory.path().join("libbackend.rmeta"))
        .arg(lib)
        .output()
        .expect("build dependency");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let backend = format!(
        "backend={}",
        directory.path().join("libbackend.rmeta").display()
    );
    let src = r#"
#![feature(register_tool)]
#![register_tool(shapelint_tool)]
#![allow(dead_code)]
#[derive(Clone,Copy)] pub struct Id(u32);
struct Table<R>(std::marker::PhantomData<R>);
impl<R> Table<R> {
    #[shapelint_tool::arena(append)] fn publish(&self, value:R)->R { backend::accept(value) }
}
pub struct Tree { #[shapelint_tool::arena(storage)] table:Table<Id> }
impl Tree {
    pub fn walk(&mut self, root:Id, leaf:bool)->Id {
        if leaf {return root}
        let next = self.table.publish(root);
        self.walk(next, true)
    }
}"#;
    let output = support::analyze(src, &["--extern", &backend, "--show-analysis-gaps"])
        .expect("analyze consumer");
    assert!(
        output
            .lines()
            .map(|line| serde_json::from_str::<serde_json::Value>(line).unwrap())
            .any(|f| f["primary"]["message"] == "recursive call requirements"),
        "{output}"
    );
}
