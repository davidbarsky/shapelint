#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Subject {
    Parameters,
    Receiver,
    NestedFields,
    Tuple,
    Variant,
    Call,
}

#[hegel::test]
fn obligations_use_source_names_and_values(tc: hegel::TestCase) {
    let subject = tc.draw(hegel::generators::default::<Subject>());
    let (source, expected) = match subject {
        Subject::Parameters => (
            "pub fn read(source: &[u8], start: usize, end: usize) -> &[u8] { &source[start..end] }",
            "start <= end",
        ),
        Subject::Receiver => (
            "pub struct Reader { data: Vec<u8> } impl Reader { pub fn read(&self, index: usize) -> u8 { self.data[index] } }",
            "index < self.data.len()",
        ),
        Subject::NestedFields => (
            "pub struct Span { start: usize, end: usize } pub struct Request { span: Span } pub fn read(source: &[u8], request: Request) -> &[u8] { &source[request.span.start..request.span.end] }",
            "request.span.start <= request.span.end",
        ),
        Subject::Tuple => (
            "pub fn read(source: &[u8], range: (usize, usize)) -> &[u8] { &source[range.0..range.1] }",
            "range.0 <= range.1",
        ),
        Subject::Variant => (
            "pub fn read(value: Option<u8>) -> u8 { value.unwrap() }",
            "value must be option::Option::Some",
        ),
        Subject::Call => (
            "fn choose(flag: bool) -> usize { if flag { 1 } else { 2 } } pub fn read(source: &[u8], flag: bool) -> u8 { source[choose(flag)] }",
            "(if flag == true { 1 } else { 2 }) < source.len()",
        ),
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("driver analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let messages: Vec<_> = findings
        .iter()
        .filter(|finding| finding["rule"] == "unproven-precondition")
        .map(|finding| finding["primary"]["message"].as_str().expect("label"))
        .collect();
    assert!(messages.contains(&expected), "{subject:?}: {findings:?}");
    assert!(!output.contains("field["), "{output}");
    assert!(!output.contains("argument "), "{output}");
    assert!(!output.contains("has variant 0"), "{output}");
    assert!(!output.contains("has variant 1"), "{output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Declaration {
    Visible,
    Suppressed,
}

#[hegel::test]
fn representation_findings_belong_to_the_type_and_keep_the_original_consumer(tc: hegel::TestCase) {
    let declaration = tc.draw(hegel::generators::default::<Declaration>());
    let directive = match declaration {
        Declaration::Visible => "",
        Declaration::Suppressed => "// shapelint: allow(unencoded-precondition)\n",
    };
    let source = format!(
        "{directive}pub struct Span {{ pub start: usize, pub end: usize }}
        fn consume(span: Span) -> usize {{ span.end - span.start }}
        pub fn wrapper(span: Span) {{ consume(span); }}
        pub fn other(span: Span) {{ consume(span); }}"
    );
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("driver analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let findings: Vec<_> = findings
        .iter()
        .filter(|finding| finding["rule"] == "unencoded-precondition")
        .collect();
    match declaration {
        Declaration::Visible => {
            assert_eq!(findings.len(), 1, "{findings:?}");
            let finding = findings[0];
            assert_eq!(finding["item"], "Span");
            assert_eq!(finding["line"], 1);
            assert_eq!(finding["primary"]["message"], "requires start <= end");
            let notes = finding["footers"].as_array().expect("footers");
            let Some(_) = notes.iter().find(|note| {
                note["message"]
                    .as_str()
                    .expect("message")
                    .contains("Required by `consume`")
            }) else {
                panic!("{finding}");
            };
        }
        Declaration::Suppressed => assert!(findings.is_empty(), "{findings:?}"),
    }
}

#[test]
fn closure_names_do_not_expose_compiler_disambiguators() {
    let source = "pub fn run() { let work = || { let start = 3; let end = 1; let _ = &\"abcd\"[start..end]; }; work(); }";
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("driver analysis");
    assert!(!output.contains("{closure#"), "{output}");
    assert!(output.contains("invalid-state-use"), "{output}");
}

#[test]
fn propagated_unknown_bounds_keep_operand_names_and_the_original_check() {
    let source = "fn consume(text: &str, offset: usize, length: usize) -> &str { &text[offset..offset + length] } pub fn run(text: &str, make: fn() -> usize) -> &str { let offset = make(); let length = make(); consume(text, offset, length) }";
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("driver analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let finding = findings
        .iter()
        .find(|finding| {
            finding["rule"] == "unproven-precondition"
                && finding["primary"]["message"] == "offset <= (offset + length)"
        })
        .expect("named comparison remains visible");
    assert_eq!(
        finding["related"][0]["label"]["message"],
        "check originates in `consume`"
    );
    let span = &finding["related"][0]["label"]["span"];
    let start = span["start"].as_u64().expect("start") as usize;
    let end = span["end"].as_u64().expect("end") as usize;
    assert_eq!(&source[start..end], "[offset..offset + length]");
    assert_ne!(
        finding["primary"]["message"],
        "could not prove the required comparison"
    );
    assert!(!output.contains("invalid-state-use"), "{output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum BoundaryNames {
    Both,
    Text,
    Endpoint,
    Neither,
}

#[hegel::test]
fn unknown_operands_are_explained_once_per_obligation(tc: hegel::TestCase) {
    let names = tc.draw(hegel::generators::default::<BoundaryNames>());
    let (source, expected) = match names {
        BoundaryNames::Both => (
            "pub fn read(text: &str, end: usize) -> &str { &text[..end] }",
            "end is a UTF-8 boundary in text",
        ),
        BoundaryNames::Text => (
            "pub fn read(text: &str, offset: usize) -> &str { let end = offset.wrapping_add(1); &text[..end] }",
            "end is a UTF-8 boundary in text",
        ),
        BoundaryNames::Endpoint => (
            "pub fn read(make: fn() -> &'static str, end: usize) -> &'static str { let text = make(); &text[..end] }",
            "end is a UTF-8 boundary in text",
        ),
        BoundaryNames::Neither => (
            "pub fn read(make: fn() -> &'static str) -> &'static str { let text = make(); let end = text.len(); &text[..end] }",
            "text.len() is a UTF-8 boundary in text",
        ),
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("driver analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let labels: Vec<_> = findings
        .iter()
        .filter(|finding| finding["rule"] == "unproven-precondition")
        .map(|finding| finding["primary"]["message"].as_str().expect("label"))
        .collect();
    match names {
        BoundaryNames::Neither => assert!(labels.is_empty(), "{labels:?}"),
        BoundaryNames::Both | BoundaryNames::Text | BoundaryNames::Endpoint => {
            assert!(labels.contains(&expected), "{names:?}: {labels:?}")
        }
    }
    assert!(
        !output.contains("a value the analysis could not determine"),
        "{output}"
    );
    assert!(!output.contains("unknown.len()"), "{output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Explanation {
    Comparison,
    Boundary,
    Variant,
    LostValue,
    ConditionalFailure,
}

#[hegel::test]
fn unresolved_checks_explain_what_prevents_a_proof(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Explanation>());
    let (source, explanation) = match case {
        Explanation::Comparison => (
            "pub fn run(values: &[u8], at: usize) -> u8 { values[at] }",
            "The known bounds and comparisons do not establish this requirement.",
        ),
        Explanation::Boundary => (
            "pub fn run(text: &str, end: usize) -> &str { if end <= text.len() { &text[..end] } else { text } }",
            "No UTF-8 boundary guarantee was established for this offset in this string.",
        ),
        Explanation::Variant => (
            "pub fn run(value: Option<u32>) -> u32 { value.unwrap() }",
            "The analysis has not established which enum variant reaches this operation.",
        ),
        Explanation::LostValue => (
            "fn read(text: &str) -> usize { let end = text.len() as u8 as usize; text[..end].len() } pub fn run(text: &str) -> usize { read(text) }",
            "At least one value used by this check could not be tracked through the analysis.",
        ),
        Explanation::ConditionalFailure => (
            "fn decrement(value: u32) -> u32 { value - 1 } pub fn run(enabled: bool) -> u32 { if enabled { decrement(0) } else { 0 } }",
            "This check fails on a path whose reachability has not been established.",
        ),
    };
    let output = support::analyze(source, &["--show-analysis-gaps"]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "unproven-precondition")
        .collect();
    let explained = findings.iter().find(|finding| {
        finding["footers"]
            .as_array()
            .expect("footers")
            .iter()
            .any(|footer| footer["message"] == explanation)
    });
    assert_ne!(explained, None, "{case:?}: {output}");
}
