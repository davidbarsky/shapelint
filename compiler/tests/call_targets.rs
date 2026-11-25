#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Invocation {
    Pointer,
    Callback,
    ReturnedPointer,
    CapturedClosure,
    GenericTrait,
    TraitObject,
    TraitObjectAlternatives,
    UnknownTraitObjectAlternative,
    TwoKnownTargets,
    UnknownAlternative,
    ReassignedPointer,
}

#[hegel::test]
fn call_requirements_follow_callable_values(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Invocation>());
    let (source, expected) = match case {
        Invocation::Pointer => (
            "fn decrement(value:u32)->u32{value-1} pub fn run()->u32{let f:fn(u32)->u32=decrement;f(0)}",
            1,
        ),
        Invocation::Callback => (
            "fn decrement(value:u32)->u32{value-1} fn apply(f:fn(u32)->u32,value:u32)->u32{f(value)} pub fn run()->u32{apply(decrement,0)}",
            1,
        ),
        Invocation::ReturnedPointer => (
            "fn decrement(value:u32)->u32{value-1} fn select()->fn(u32)->u32{decrement} pub fn run()->u32{select()(0)}",
            1,
        ),
        Invocation::CapturedClosure => (
            "fn apply<F:FnOnce(u32)->u32>(f:F,value:u32)->u32{f(value)} pub fn run()->u32{let amount=1;apply(|value|value-amount,0)}",
            1,
        ),
        Invocation::GenericTrait => (
            "trait Source{fn value()->u32;} struct Safe;struct Empty;impl Source for Safe{fn value()->u32{1}}impl Source for Empty{fn value()->u32{0}}fn decrement<S:Source>()->u32{S::value()-1}pub fn good()->u32{decrement::<Safe>()}pub fn bad()->u32{decrement::<Empty>()}",
            1,
        ),
        Invocation::TraitObject => (
            "trait Source{fn value(&self)->u32;}struct Empty;impl Source for Empty{fn value(&self)->u32{0}}fn decrement(source:&dyn Source)->u32{source.value()-1}pub fn run()->u32{decrement(&Empty)}",
            1,
        ),
        Invocation::TraitObjectAlternatives => (
            "trait Source{fn value(&self)->u32;}struct First;struct Second;impl Source for First{fn value(&self)->u32{0}}impl Source for Second{fn value(&self)->u32{0}}pub fn run(choose:bool)->u32{let source:&dyn Source=if choose{&First}else{&Second};source.value()-1}",
            1,
        ),
        Invocation::UnknownTraitObjectAlternative => (
            "pub trait Source{fn value(&self)->u32;}struct First;impl Source for First{fn value(&self)->u32{0}}pub fn run(choose:bool,other:&dyn Source)->u32{let source:&dyn Source=if choose{&First}else{other};source.value()-1}",
            0,
        ),
        Invocation::TwoKnownTargets => (
            "fn first()->u32{0}fn second()->u32{0}fn decrement(value:u32)->u32{value-1}pub fn run(choose:bool)->u32{let f:fn()->u32=if choose{first}else{second};decrement(f())}",
            1,
        ),
        Invocation::UnknownAlternative => (
            "fn decrement(value:u32)->u32{value-1}pub fn run(choose:bool,other:fn(u32)->u32)->u32{let f:fn(u32)->u32=if choose{decrement}else{other};f(0)}",
            0,
        ),
        Invocation::ReassignedPointer => (
            "fn decrement(value:u32)->u32{value-1}pub fn run(change:fn(&mut fn(u32)->u32))->u32{let mut f:fn(u32)->u32=decrement;change(&mut f);f(0)}",
            0,
        ),
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "invalid-state-use")
        .collect();
    assert_eq!(findings.len(), expected, "{case:?}: {output}");
    match case {
        Invocation::GenericTrait => assert_eq!(findings[0]["item"], "bad", "{output}"),
        _ => {}
    }
}

#[test]
fn an_unresolved_target_alternative_does_not_close_the_known_functions_callers() {
    let source = "fn render(value:u32,basis:Option<u32>)->u32{match basis{Some(basis)=>value.wrapping_add(basis),None=>value}} pub fn direct(value:u32)->u32{render(value,None)} pub fn indirect(choose:bool,other:fn(u32,Option<u32>)->u32)->u32{let f:fn(u32,Option<u32>)->u32=if choose{render}else{other};f(0,Some(1))}";
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unused-capability" && finding["item"] == "render"
        })
        .collect();
    assert!(findings.is_empty(), "{output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum StoredCallable {
    Static,
    Constant,
    Aggregate,
    Array,
}

#[hegel::test]
fn callable_initializers_remain_visible_when_returned_from_public_getters(tc: hegel::TestCase) {
    let storage = tc.draw(hegel::generators::default::<StoredCallable>());
    let declaration = match storage {
        StoredCallable::Static => {
            "static CALLBACK:fn(u32,Option<u32>)->u32=render;pub fn callback()->fn(u32,Option<u32>)->u32{CALLBACK}"
        }
        StoredCallable::Constant => {
            "const CALLBACK:fn(u32,Option<u32>)->u32=render;pub fn callback()->fn(u32,Option<u32>)->u32{CALLBACK}"
        }
        StoredCallable::Aggregate => {
            "static CALLBACK:(u32,fn(u32,Option<u32>)->u32)=(0,render);pub fn callback()->fn(u32,Option<u32>)->u32{CALLBACK.1}"
        }
        StoredCallable::Array => {
            "static CALLBACK:[fn(u32,Option<u32>)->u32;1]=[render];pub fn callback()->fn(u32,Option<u32>)->u32{CALLBACK[0]}"
        }
    };
    let source = format!(
        "fn render(value:u32,basis:Option<u32>)->u32{{match basis{{Some(basis)=>value.wrapping_add(basis),None=>value}}}}{declaration}pub fn run(value:u32)->u32{{render(value,None)}}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unused-capability" && finding["item"] == "render"
        })
        .collect();
    assert!(findings.is_empty(), "{storage:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Registration {
    Forwarded,
    Returned,
    Generic,
}

#[hegel::test]
fn callable_escape_survives_direct_helper_chains(tc: hegel::TestCase) {
    let registration = tc.draw(hegel::generators::default::<Registration>());
    let path = match registration {
        Registration::Forwarded => {
            "fn first(callback:fn(u32,Option<u32>)->u32){unsafe{register(callback)}}fn second(callback:fn(u32,Option<u32>)->u32){first(callback)}pub fn expose(){second(render)}"
        }
        Registration::Returned => {
            "fn callback()->fn(u32,Option<u32>)->u32{render}pub fn expose(){unsafe{register(callback())}}"
        }
        Registration::Generic => {
            "pub trait Registry{fn register(callback:fn(u32,Option<u32>)->u32);}pub fn expose<R:Registry>(){R::register(render)}"
        }
    };
    let declaration = match registration {
        Registration::Forwarded | Registration::Returned => {
            "unsafe extern \"Rust\"{fn register(callback:fn(u32,Option<u32>)->u32);}"
        }
        Registration::Generic => "",
    };
    let source = format!(
        "{declaration}fn render(value:u32,basis:Option<u32>)->u32{{match basis{{Some(basis)=>value.wrapping_add(basis),None=>value}}}}{path}pub fn run(value:u32)->u32{{render(value,None)}}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unused-capability" && finding["item"] == "render"
        })
        .collect();
    assert!(findings.is_empty(), "{registration:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum SharedCalls {
    Generic,
    Callback,
}

#[hegel::test]
fn repeated_diamonds_keep_distinct_invocation_results(tc: hegel::TestCase) {
    let calls = tc.draw(hegel::generators::default::<SharedCalls>());
    let source = match calls {
        SharedCalls::Generic => {
            "trait Value{fn value()->u32;}struct Empty;struct Safe;impl Value for Empty{fn value()->u32{0}}impl Value for Safe{fn value()->u32{1}}fn shared<T:Value>()->u32{T::value()}fn left<T:Value>()->u32{shared::<T>();shared::<T>()}fn right<T:Value>()->u32{shared::<T>();shared::<T>()}fn diamond<T:Value>()->u32{left::<T>();right::<T>()}pub fn bad()->u32{diamond::<Empty>()-1}pub fn good()->u32{diamond::<Safe>()-1}"
        }
        SharedCalls::Callback => {
            "fn empty()->u32{0}fn safe()->u32{1}fn shared(f:fn()->u32)->u32{f()}fn left(f:fn()->u32)->u32{shared(f);shared(f)}fn right(f:fn()->u32)->u32{shared(f);shared(f)}fn diamond(f:fn()->u32)->u32{left(f);right(f)}pub fn bad()->u32{diamond(empty)-1}pub fn good()->u32{diamond(safe)-1}"
        }
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "invalid-state-use")
        .collect();
    assert_eq!(findings.len(), 1, "{calls:?}: {output}");
    assert_eq!(findings[0]["item"], "bad", "{calls:?}: {output}");
}

#[test]
fn recursive_callable_results_do_not_become_definite_values() {
    let source = "fn empty()->u32{0}fn recurse(f:fn()->u32,again:bool)->u32{if again{recurse(f,again)}else{f()}}pub fn run(again:bool)->u32{recurse(empty,again)-1}";
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "invalid-state-use")
        .collect();
    assert!(findings.is_empty(), "{output}");
}

#[test]
fn shared_callback_contexts_keep_each_root_callers_location() {
    let source = "fn render(value:u32,basis:Option<u32>)->u32{match basis{Some(basis)=>value.wrapping_add(basis),None=>value}}fn apply(f:fn(u32,Option<u32>)->u32,value:u32)->u32{f(value,None)}pub fn first(value:u32)->u32{apply(render,value)}pub fn second(value:u32)->u32{apply(render,value)}";
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "unused-capability" && finding["item"] == "render"
        })
        .collect();
    assert_eq!(findings.len(), 1, "{output}");
    let related: Vec<_> = findings[0]["related"]
        .as_array()
        .expect("caller locations")
        .iter()
        .map(|related| related["label"]["message"].as_str().expect("caller name"))
        .collect();
    assert!(related.contains(&"check originates in `first`"), "{output}");
    assert!(
        related.contains(&"check originates in `second`"),
        "{output}"
    );
}

#[test]
fn a_recursive_query_does_not_poison_a_later_base_case() {
    let source = "fn recurse(value:u32)->u32{if value==0{0}else{recurse(value-1)}}fn shared(value:u32)->u32{recurse(value)}pub fn run()->u32{shared(1);shared(0)-1}";
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "invalid-state-use")
        .collect();
    assert_eq!(findings.len(), 1, "{output}");
    assert_eq!(findings[0]["item"], "run", "{output}");
}

#[test]
fn shared_pure_helpers_remain_equivalent() {
    let source = "fn leaf(a:u32,b:u32)->u32{if a<b{a}else{b}}fn left(a:u32,b:u32)->u32{leaf(a,b)}fn right(a:u32,b:u32)->u32{leaf(a,b)}pub fn first(a:u32,b:u32)->u32{left(a,b)}pub fn second(a:u32,b:u32)->u32{right(a,b)}";
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "equivalent-implementation" && finding["item"] == "second"
        })
        .collect();
    assert_eq!(findings.len(), 1, "{output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum RecursiveGraph {
    Direct,
    Mutual,
    Reversed,
    Specialized,
}

#[hegel::test]
fn recursive_obligations_keep_local_checks_and_base_case_guards(tc: hegel::TestCase) {
    let graph = tc.draw(hegel::generators::default::<RecursiveGraph>());
    let first = "fn first(value:u32,steps:u32)->u32{let value=need(value);if steps>0{second(value,steps-1)}else{value}}";
    let second = "fn second(value:u32,steps:u32)->u32{let value=need(value);if steps>0{first(value,steps-1)}else{value}}";
    let recursive = match graph {
        RecursiveGraph::Direct => "fn first(value:u32,steps:u32)->u32{let value=need(value);if steps>0{first(value,steps-1)}else{value}}".to_owned(),
        RecursiveGraph::Mutual => format!("{first}{second}"),
        RecursiveGraph::Reversed => format!("{second}{first}"),
        RecursiveGraph::Specialized => "trait Next{fn next(value:u32,steps:u32)->u32;}struct Again;impl Next for Again{fn next(value:u32,steps:u32)->u32{descend::<Again>(value,steps)}}fn descend<N:Next>(value:u32,steps:u32)->u32{let value=need(value);if steps>0{N::next(value,steps-1)}else{value}}fn first(value:u32,steps:u32)->u32{descend::<Again>(value,steps)}".to_owned(),
    };
    let roots = match graph {
        RecursiveGraph::Reversed => "pub fn good()->u32{first(2,0)}pub fn bad()->u32{first(0,2)}",
        RecursiveGraph::Direct | RecursiveGraph::Mutual | RecursiveGraph::Specialized => {
            "pub fn bad()->u32{first(0,2)}pub fn good()->u32{first(2,0)}"
        }
    };
    let source = format!(
        "fn need(value:u32)->u32{{value-1}}{recursive}{roots}pub fn uncertain(steps:u32)->u32{{first(2,steps)}}"
    );
    let directory = tempfile::tempdir().expect("source directory");
    let path = directory.path().join("recursive.rs");
    std::fs::write(&path, source).expect("write source");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args([
            "--format=json",
            "--show-analysis-gaps",
            "--crate-type=lib",
            "--edition=2024",
            "--emit=metadata",
        ])
        .arg("--out-dir")
        .arg(directory.path())
        .arg(path)
        .output()
        .expect("run analysis");
    assert!(
        output.status.success(),
        "{graph:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "{graph:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let output = String::from_utf8(output.stdout).expect("diagnostics");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let invalid: Vec<_> = findings
        .iter()
        .filter(|finding| finding["rule"] == "invalid-state-use" && finding["item"] == "bad")
        .collect();
    assert_eq!(invalid.len(), 1, "{graph:?}: {output}");
    let base_case: Vec<_> = findings
        .iter()
        .filter(|finding| {
            finding["item"] == "good"
                && (finding["rule"] == "invalid-state-use"
                    || finding["rule"] == "unproven-precondition"
                    || finding["rule"] == "analysis-incomplete")
        })
        .collect();
    assert!(base_case.is_empty(), "{graph:?}: {output}");
    let recursive: Vec<_> = findings
        .iter()
        .filter(|finding| {
            finding["item"] == "uncertain" && finding["rule"] == "analysis-incomplete"
        })
        .collect();
    assert_eq!(recursive.len(), 1, "{graph:?}: {output}");
    assert_eq!(
        recursive[0]["primary"]["message"], "recursive call requirements",
        "{graph:?}: {output}"
    );
}

#[test]
fn late_specialization_preserves_local_and_outgoing_requirements() {
    let source = "fn need(value:u32)->u32{value-1}trait Supply{fn value(value:u32)->u32;}struct Live;impl Supply for Live{fn value(value:u32)->u32{need(value)}}fn generic<S:Supply>(left:u32,right:u32)->u32{let local=left-1;S::value(right);local}pub fn local_bad()->u32{generic::<Live>(0,1)}pub fn outgoing_bad()->u32{generic::<Live>(1,0)}pub fn good()->u32{generic::<Live>(1,1)}";
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "invalid-state-use")
        .collect();
    let items: Vec<_> = findings
        .iter()
        .map(|finding| finding["item"].as_str().expect("item"))
        .collect();
    assert_eq!(items.len(), 2, "{output}");
    assert!(items.contains(&"local_bad"), "{output}");
    assert!(items.contains(&"outgoing_bad"), "{output}");
}

#[test]
fn zero_argument_static_callbacks_keep_their_consumers_requirement() {
    let source = "fn decrement(value:u32)->u32{value-1}fn target()->u32{decrement(0)}static CALLBACK:fn()->u32=target;pub fn run()->u32{CALLBACK()}";
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "invalid-state-use" && finding["item"] == "run"
        })
        .collect();
    assert_eq!(findings.len(), 1, "{output}");
}
