#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Construction {
    Checked,
    Fallible,
    Unchecked,
    PublicField,
    Mutation,
    UnknownProducer,
    DerivedClone,
    BorrowedIteration,
    BorrowedChunks,
    OwnedIterator,
    BorrowedResult,
    ExtendedCopy,
}

#[hegel::test]
fn private_collection_bounds_require_every_producer_to_preserve_the_limit(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Construction>());
    struct Fixture {
        field: &'static str,
        constructor: &'static str,
        operations: &'static str,
        expected: usize,
    }
    let fixture = match case {
        Construction::Checked => Fixture {
            field: "value: String",
            constructor: "pub fn new(value:String)->Option<Self> { if value.len()<=u32::MAX as usize {Some(Self{value})}else{None} }",
            operations: "",
            expected: 0,
        },
        Construction::Fallible => Fixture {
            field: "value: String",
            constructor: "pub fn try_new(value:String)->Result<Self, ()> { if value.len()>u32::MAX as usize {return Err(())} Ok(Self{value}) }",
            operations: "",
            expected: 0,
        },
        Construction::DerivedClone => Fixture {
            field: "value: String",
            constructor: "pub fn new(value:String)->Option<Self> { if value.len()<=u32::MAX as usize {Some(Self{value})}else{None} }",
            operations: "pub fn copy(&self)->Self{self.clone()}",
            expected: 0,
        },
        Construction::BorrowedIteration => Fixture {
            field: "value: String",
            constructor: "pub fn new(value:String)->Option<Self> { if value.len()<=u32::MAX as usize {Some(Self{value})}else{None} }",
            operations: "pub fn scan(values:&[Self])->usize {values.iter().count()}",
            expected: 0,
        },
        Construction::BorrowedChunks => Fixture {
            field: "value: String",
            constructor: "pub fn new(value:String)->Option<Self> { if value.len()<=u32::MAX as usize {Some(Self{value})}else{None} }",
            operations: "pub fn scan(values:&[Self],size:std::num::NonZeroUsize)->usize {values.chunks(size.get()).map(|chunk|chunk.len()).sum()}",
            expected: 0,
        },
        Construction::OwnedIterator => Fixture {
            field: "value: String",
            constructor: "pub fn new(value:String)->Option<Self> { if value.len()<=u32::MAX as usize {Some(Self{value})}else{None} }",
            operations: "pub fn load(make:fn()->std::vec::IntoIter<Self>)->std::vec::IntoIter<Self>{make()}",
            expected: 1,
        },
        Construction::BorrowedResult => Fixture {
            field: "value: String",
            constructor: "pub fn new(value:String)->Option<Self> { if value.len()<=u32::MAX as usize {Some(Self{value})}else{None} }",
            operations: "pub fn borrowed(make:fn()->&'static Self)->&'static Self {make()}",
            expected: 0,
        },
        Construction::ExtendedCopy => Fixture {
            field: "value: String",
            constructor: "pub fn new(value:String)->Option<Self> { if value.len()<=u32::MAX as usize {Some(Self{value})}else{None} }",
            operations: "pub fn extended(&self,suffix:&str)->Self {let mut value=self.value.clone();value.push_str(suffix);Self{value}}",
            expected: 1,
        },
        Construction::Unchecked => Fixture {
            field: "value: String",
            constructor: "pub fn new(value:String)->Self {Self{value}}",
            operations: "",
            expected: 1,
        },
        Construction::PublicField => Fixture {
            field: "pub value: String",
            constructor: "pub fn new(value:String)->Option<Self> { if value.len()<=u32::MAX as usize {Some(Self{value})}else{None} }",
            operations: "",
            expected: 1,
        },
        Construction::Mutation => Fixture {
            field: "value: String",
            constructor: "pub fn new(value:String)->Option<Self> { if value.len()<=u32::MAX as usize {Some(Self{value})}else{None} }",
            operations: "pub fn replace(&mut self,value:String){self.value=value;}",
            expected: 1,
        },
        Construction::UnknownProducer => Fixture {
            field: "value: String",
            constructor: "pub fn new(value:String)->Option<Self> { if value.len()<=u32::MAX as usize {Some(Self{value})}else{None} }",
            operations: "pub fn load(make:fn()->Self)->Self{make()}",
            expected: 1,
        },
    };
    let Fixture {
        field,
        constructor,
        operations,
        expected,
    } = fixture;
    let source = format!(
        "#[derive(Clone)] pub struct Text{{{field}}} impl Text{{{constructor} {operations} pub fn remaining(&self)->usize{{u32::MAX as usize-self.value.len()}}}}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "unproven-precondition")
        .collect();
    assert_eq!(findings.len(), expected, "{case:?}: {output}");
}
