#![feature(rustc_private)]

mod support;

#[test]
fn follows_option_forwarding_to_the_absence_decision() {
    let source = r#"
fn consume(value: Option<u32>) -> u32 { match value { Some(value) => value, None => 0 } }
fn forward(value: Option<u32>) -> u32 { consume(value) }
pub fn entry(value: Option<u32>) -> u32 { forward(value) }
"#;
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| {
            finding["rule"] == "option-plumbing" && finding["item"] == "entry"
        })
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "missing forwarding-chain diagnostic: {output}"
    );
    assert_eq!(
        findings[0]["related"].as_array().expect("chain").len(),
        2,
        "{output}"
    );
}

#[test]
fn identifies_three_legal_states_in_a_four_state_representation() {
    let source = r#"
pub struct Origin { agent: Option<String>, truncated: bool }
impl Origin {
    pub fn missing() -> Self { Self { agent: None, truncated: false } }
    pub fn present(agent: String, truncated: bool) -> Self { Self { agent: Some(agent), truncated } }
    pub fn view(&self) -> (Option<&str>, bool) { (self.agent.as_deref(), self.truncated) }
}
"#;
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "correlated-state")
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "missing correlated-state diagnostic: {output}"
    );
    let label = findings[0]["primary"]["message"]
        .as_str()
        .expect("relation");
    assert!(
        label.contains("agent") && label.contains("truncated"),
        "{output}"
    );
}

#[test]
fn follows_a_typed_value_through_json_and_back() {
    let source = r#"
#![feature(rustc_private)]
extern crate serde_json;
pub fn copy(value: Vec<u8>) -> Vec<u8> {
    let encoded = serde_json::to_value(&value).unwrap();
    serde_json::from_value(encoded).unwrap()
}
"#;
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "serialization-detour")
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "missing serialization-detour diagnostic: {output}"
    );
    assert_eq!(
        findings[0]["related"]
            .as_array()
            .expect("serialization")
            .len(),
        1,
        "{output}"
    );
}

#[test]
fn finds_a_capability_that_no_production_caller_supplies() {
    let source = r#"
fn render(value: u32, basis: Option<u32>) -> u32 {
    match basis { Some(basis) => value.wrapping_add(basis), None => value }
}
pub fn first(value: u32) -> u32 { render(value, None) }
pub fn second(value: u32) -> u32 { render(value, None) }
"#;
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "unused-capability")
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "missing unused-capability diagnostic: {output}"
    );
    assert!(
        findings[0]["primary"]["message"]
            .as_str()
            .expect("parameter")
            .contains("basis"),
        "{output}"
    );
}

#[test]
fn identifies_a_clone_used_only_for_a_shared_borrow() {
    let source = r#"
pub fn size(value: &String) -> usize {
    let copy = value.clone();
    copy.len()
}
"#;
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "clone-only-to-borrow")
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "missing clone-only-to-borrow diagnostic: {output}"
    );
}

#[test]
fn connects_discarded_validation_to_repeated_recovery() {
    let source = r#"
fn validate(index: usize, len: usize) { if index >= len { panic!("out of bounds"); } }
pub fn read(values: &[u8], index: usize) -> u8 {
    validate(index, values.len());
    if index < values.len() { values[index] } else { 0 }
}
"#;
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "discarded-validation")
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "missing discarded-validation diagnostic: {output}"
    );
    assert!(
        !findings[0]["related"]
            .as_array()
            .expect("validation")
            .is_empty(),
        "{output}"
    );
}

#[test]
fn reports_a_path_that_bypasses_a_declared_barrier() {
    let source = r#"
#![feature(register_tool)]
#![register_tool(shapelint)]
pub struct Database;
#[shapelint::protocol(durability, invalidate)]
fn write(_: &Database) {}
#[shapelint::protocol(durability, establish)]
fn barrier(_: &Database) {}
#[shapelint::protocol(durability, require)]
fn publish(_: &Database) {}
pub fn run(db: &Database, flush: bool) {
    write(db);
    if flush { barrier(db); }
    publish(db);
}
"#;
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "protocol-bypass")
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "missing protocol-bypass diagnostic: {output}"
    );
    assert!(
        !findings[0]["related"]
            .as_array()
            .expect("write path")
            .is_empty(),
        "{output}"
    );
}

#[test]
fn reports_a_test_only_production_path_before_cfg_removes_it() {
    let source = r#"
pub fn recover(value: u32) -> u32 { value }
#[cfg(test)]
pub fn recover_for_test(value: u32) -> u32 { value }
"#;
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "test-only-production-path")
        .collect();
    assert_eq!(
        findings.len(),
        1,
        "missing test-only-production-path diagnostic: {output}"
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Exception {
    IndependentFields,
    MutatedFields,
    PublicCapability,
    VaryingCapability,
    EscapedFunction,
    UnknownCapability,
    ConsumedClone,
    MutableClone,
    CustomClone,
    ObservableIdentity,
    ObservedOriginalHandle,
    MutatedEncoding,
    ChangedValidation,
    DifferentValidation,
    EscapedEncoding,
    DifferentDecodedType,
    RenamedSerializer,
    HandledAbsence,
}

#[hegel::test]
fn uncertain_or_observable_alternatives_do_not_get_simplification_lints(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Exception>());
    let (rule, source) = match case {
        Exception::IndependentFields => (
            "correlated-state",
            "pub struct State { value: Option<u32>, ready: bool } impl State { pub fn new(value: Option<u32>, ready: bool) -> Self { Self { value, ready } } pub fn read(&self) -> (Option<u32>,bool) { (self.value,self.ready) } }",
        ),
        Exception::MutatedFields => (
            "correlated-state",
            "pub struct State { value: Option<u32>, ready: bool } impl State { pub fn new(value: u32, ready: bool) -> Self { Self { value: Some(value), ready } } pub fn missing() -> Self { Self { value: None, ready: false } } pub fn change(&mut self) { self.value=None; } pub fn read(&self) -> (Option<u32>,bool) { (self.value,self.ready) } }",
        ),
        Exception::PublicCapability => (
            "unused-capability",
            "pub fn run(value: Option<u32>) -> u32 { match value { Some(value) => value, None => 0 } } pub fn entry() -> u32 { run(None) }",
        ),
        Exception::VaryingCapability => (
            "unused-capability",
            "fn run(value: Option<u32>) -> u32 { match value { Some(value) => value, None => 0 } } pub fn first() -> u32 { run(None) } pub fn second() -> u32 { run(Some(1)) }",
        ),
        Exception::EscapedFunction => (
            "unused-capability",
            "fn run(value: Option<u32>) -> u32 { match value { Some(value) => value, None => 0 } } pub fn first() -> u32 { run(None) } pub fn escape() -> fn(Option<u32>) -> u32 { run }",
        ),
        Exception::UnknownCapability => (
            "unused-capability",
            "fn run(value: Option<u32>) -> u32 { match value { Some(value) => value, None => 0 } } pub fn first() -> u32 { run(None) } pub fn second(value: Option<u32>) -> u32 { run(value) }",
        ),
        Exception::ConsumedClone => (
            "clone-only-to-borrow",
            "pub fn run(value: &String) -> String { value.clone() }",
        ),
        Exception::MutableClone => (
            "clone-only-to-borrow",
            "pub fn run(value: &String) -> usize { let mut copy=value.clone(); copy.push('x'); copy.len() }",
        ),
        Exception::CustomClone => (
            "clone-only-to-borrow",
            "pub struct Value(pub usize); impl Clone for Value { fn clone(&self) -> Self { Self(self.0.wrapping_add(1)) } } impl Value { fn len(&self)->usize { self.0 } } pub fn run(value:&Value)->usize { let copy=value.clone(); copy.len() }",
        ),
        Exception::ObservableIdentity => (
            "clone-only-to-borrow",
            "pub fn run(value:&std::sync::Arc<String>)->usize { let copy=value.clone(); std::sync::Arc::strong_count(&copy) }",
        ),
        Exception::ObservedOriginalHandle => (
            "clone-only-to-borrow",
            "pub fn run(value:&std::sync::Arc<String>)->usize { let copy=value.clone(); let count=std::sync::Arc::strong_count(value); copy.len()+count }",
        ),
        Exception::MutatedEncoding => (
            "serialization-detour",
            "#![feature(rustc_private)] extern crate serde_json; pub fn run(value:Vec<u8>)->Vec<u8> { let mut encoded=serde_json::to_value(&value).unwrap(); encoded[0]=serde_json::Value::from(7); serde_json::from_value(encoded).unwrap() }",
        ),
        Exception::ChangedValidation => (
            "discarded-validation",
            "fn validate(index:usize,len:usize){ if index>=len {panic!()} } pub fn run(values:&[u8],index:usize,next:usize)->u8 {validate(index,values.len()); if next<values.len(){values[next]}else{0}}",
        ),
        Exception::DifferentValidation => (
            "discarded-validation",
            "fn validate(index:usize,len:usize){ if index>=len {panic!()} } pub fn run(values:&[u8],index:usize)->u8 {validate(index,values.len()); if index>0{values[index]}else{0}}",
        ),
        Exception::EscapedEncoding => (
            "serialization-detour",
            "#![feature(rustc_private)] extern crate serde_json; pub fn run(value:Vec<u8>,send:fn(&serde_json::Value))->Vec<u8> { let encoded=serde_json::to_value(&value).unwrap(); send(&encoded); serde_json::from_value(encoded).unwrap() }",
        ),
        Exception::DifferentDecodedType => (
            "serialization-detour",
            "#![feature(rustc_private)] extern crate serde_json; pub fn run(value:Vec<u8>)->Vec<u64> { let encoded=serde_json::to_value(&value).unwrap(); serde_json::from_value(encoded).unwrap() }",
        ),
        Exception::RenamedSerializer => (
            "serialization-detour",
            "fn to_value(value:u32)->u32 {value} fn from_value(value:u32)->u32 {value} pub fn run(value:u32)->u32 {from_value(to_value(value))}",
        ),
        Exception::HandledAbsence => (
            "option-plumbing",
            "fn consume(value:Option<u32>)->u32 {match value{Some(value)=>value,None=>0}} pub fn run(value:Option<u32>)->u32 {match value{Some(value)=>consume(Some(value)),None=>42}}",
        ),
    };
    let output = support::analyze(source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == rule)
        .collect();
    assert!(findings.is_empty(), "{case:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ProtocolPath {
    Established,
    WrongResource,
    Reinvalidated,
    ThroughHelper,
    ThroughBarrierHelper,
    UnknownCall,
    CorrelatedBarrier,
}

#[hegel::test]
fn protocol_guarantees_follow_resource_identity_and_local_helpers(tc: hegel::TestCase) {
    let path = tc.draw(hegel::generators::default::<ProtocolPath>());
    let (body, expected) = match path {
        ProtocolPath::Established => ("write(a); barrier(a); publish(a);", 0),
        ProtocolPath::WrongResource => ("write(a); barrier(b); publish(a);", 1),
        ProtocolPath::Reinvalidated => ("write(a); barrier(a); write(a); publish(a);", 1),
        ProtocolPath::ThroughHelper => ("helper(a); publish(a);", 1),
        ProtocolPath::ThroughBarrierHelper => ("write(a); flush(a); publish(a);", 0),
        ProtocolPath::UnknownCall => ("write(a); effect(a); publish(a);", 0),
        ProtocolPath::CorrelatedBarrier => (
            "if flag { write(a); } if flag { barrier(a); } publish(a);",
            0,
        ),
    };
    let source = format!(
        r#"
#![feature(register_tool)]
#![register_tool(shapelint)]
pub struct Database;
#[shapelint::protocol(durability, invalidate)] fn write(_: &Database) {{}}
#[shapelint::protocol(durability, establish)] fn barrier(_: &Database) {{}}
#[shapelint::protocol(durability, require)] fn publish(_: &Database) {{}}
pub fn helper(db:&Database) {{ write(db); }}
pub fn flush(db:&Database) {{ barrier(db); }}
pub fn run(a:&Database,b:&Database,effect:fn(&Database),flag:bool) {{ let _ = (b,effect,flag); {body} }}
"#
    );
    let output = support::analyze(&source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "protocol-bypass")
        .collect();
    assert_eq!(findings.len(), expected, "{path:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Review {
    OptionBoundary,
    Correlation,
    Serialization,
    Capability,
    Clone,
    Validation,
    Protocol,
    TestPath,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Boundary {
    Macro,
    Suppression,
}

#[hegel::test]
fn feedback_reviews_respect_macro_boundaries_and_suppression(tc: hegel::TestCase) {
    let (review, boundary) = tc.draw(hegel::generators::default::<(Review, Boundary)>());
    let (rule, source) = match review {
        Review::OptionBoundary => (
            "option-plumbing",
            "fn consume(value:Option<u32>)->u32 {match value{Some(value)=>value,None=>0}} pub fn entry(value:Option<u32>)->u32 {consume(value)}",
        ),
        Review::Correlation => (
            "correlated-state",
            "pub struct State { value:Option<u32>,ready:bool } impl State {pub fn missing()->Self{Self{value:None,ready:false}} pub fn present(value:u32,ready:bool)->Self{Self{value:Some(value),ready}} pub fn read(&self)->(Option<u32>,bool){(self.value,self.ready)}}",
        ),
        Review::Serialization => (
            "serialization-detour",
            "pub fn copy(value:Vec<u8>)->Vec<u8>{let encoded=serde_json::to_value(&value).unwrap();serde_json::from_value(encoded).unwrap()}",
        ),
        Review::Capability => (
            "unused-capability",
            "fn consume(value:Option<u32>)->u32 {match value{Some(value)=>value,None=>0}} pub fn entry()->u32 {consume(None)}",
        ),
        Review::Clone => (
            "clone-only-to-borrow",
            "pub fn size(value:&String)->usize {let copy=value.clone();copy.len()}",
        ),
        Review::Validation => (
            "discarded-validation",
            "fn validate(index:usize,len:usize){if index>=len{panic!()}} pub fn run(values:&[u8],index:usize)->u8{validate(index,values.len());if index<values.len(){values[index]}else{0}}",
        ),
        Review::Protocol => (
            "protocol-bypass",
            "pub struct Database; #[shapelint::protocol(durability,invalidate)] fn write(_: &Database){} #[shapelint::protocol(durability,require)] fn publish(_: &Database){} pub fn run(db:&Database){write(db);publish(db);}",
        ),
        Review::TestPath => (
            "test-only-production-path",
            "#[cfg(test)] pub fn helper(){}",
        ),
    };
    let source = match boundary {
        Boundary::Macro => {
            format!("macro_rules! generate {{ () => {{ {source} }}; }} generate!();")
        }
        Boundary::Suppression => {
            format!("// shapelint: allow({rule}) Retain this boundary.\n{source}")
        }
    };
    let source = format!(
        "#![feature(rustc_private,register_tool)]\n#![register_tool(shapelint)]\nextern crate serde_json;\n{source}"
    );
    let output = support::analyze(&source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == rule)
        .collect();
    assert!(findings.is_empty(), "{review:?}, {boundary:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Buffer {
    String,
    Bytes,
    Shared,
    LocalShared,
}

#[hegel::test]
fn shared_read_clones_follow_reborrows_and_standard_deref(tc: hegel::TestCase) {
    let buffer = tc.draw(hegel::generators::default::<Buffer>());
    let ty = match buffer {
        Buffer::String => "String",
        Buffer::Bytes => "Vec<u8>",
        Buffer::Shared => "std::sync::Arc<String>",
        Buffer::LocalShared => "std::rc::Rc<String>",
    };
    let source =
        format!("pub fn size(value: &{ty}) -> usize {{ let copy=value.clone(); copy.len() }}");
    let output = support::analyze(&source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "clone-only-to-borrow")
        .collect();
    assert_eq!(findings.len(), 1, "{buffer:?}: {output}");
}

#[test]
fn closure_guarantees_do_not_require_a_function_signature_query() {
    let source = "pub fn read(values:&[u8],index:usize)->u8 { let validate=|index:usize,len:usize| { if index>=len {panic!()} }; validate(index,values.len()); if index<values.len(){values[index]}else{0} }";
    let output = support::analyze(source, &[]).expect("closure analysis completes");
    for line in output.lines() {
        let finding: serde_json::Value = serde_json::from_str(line).expect("diagnostic");
        assert_ne!(finding["rule"], "invalid-state-use", "{output}");
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum InvalidProtocol {
    MissingAction,
    UnknownAction,
    DuplicateAction,
    FallibleEstablishment,
    OwnedResource,
}

#[hegel::test]
fn protocol_declarations_reject_ambiguous_transition_contracts(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<InvalidProtocol>());
    let (operation, expected) = match case {
        InvalidProtocol::MissingAction => (
            "#[shapelint::protocol(durability)] pub fn barrier(_: &Database) {}",
            "expected shapelint::protocol",
        ),
        InvalidProtocol::UnknownAction => (
            "#[shapelint::protocol(durability, maybe)] pub fn barrier(_: &Database) {}",
            "expected shapelint::protocol",
        ),
        InvalidProtocol::DuplicateAction => (
            "#[shapelint::protocol(durability, establish)] #[shapelint::protocol(durability, require)] pub fn barrier(_: &Database) {}",
            "exactly one transition",
        ),
        InvalidProtocol::FallibleEstablishment => (
            "#[shapelint::protocol(durability, establish)] pub fn barrier(_: &Database) -> Result<(), ()> { Err(()) }",
            "returns ()",
        ),
        InvalidProtocol::OwnedResource => (
            "#[shapelint::protocol(durability, establish)] pub fn barrier(_: Database) {}",
            "resource by reference",
        ),
    };
    let source = format!(
        "#![feature(register_tool)]\n#![register_tool(shapelint)]\npub struct Database;\n{operation}"
    );
    let directory = tempfile::tempdir().expect("fixture directory");
    let path = directory.path().join("protocol.rs");
    std::fs::write(&path, source).expect("fixture source");
    let output = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
        .args(["--crate-type=lib", "--edition=2024", "--emit=metadata"])
        .arg("--out-dir")
        .arg(directory.path())
        .arg(&path)
        .output()
        .expect("driver");
    let stderr = String::from_utf8(output.stderr).expect("compiler diagnostics");
    assert!(!output.status.success(), "{case:?}");
    assert!(stderr.contains(expected), "{case:?}: {stderr}");
    assert!(!stderr.contains("internal compiler error"), "{stderr}");
}
