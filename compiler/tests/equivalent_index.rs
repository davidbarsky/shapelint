#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum Body {
    Byte(u8),
    Word(u8),
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Functions {
    bodies: Vec<Body>,
}

#[hegel::test(print_blob = true)]
fn equivalent_implementations_keep_the_first_matching_signature_and_result(tc: hegel::TestCase) {
    let Functions { bodies } = tc.draw(hegel::generators::default::<Functions>());
    let bodies: Vec<_> = [Body::Byte(0), Body::Word(0)]
        .into_iter()
        .chain(bodies)
        .chain([Body::Byte(0), Body::Word(0), Body::Byte(0)])
        .collect();
    let mut source = String::new();
    let mut expected = Vec::new();
    let entries = bodies.iter().enumerate();
    for (index, body) in entries {
        let (ty, value) = match body {
            Body::Byte(value) => ("u8", value),
            Body::Word(value) => ("u16", value),
        };
        source.push_str(&format!("pub fn f_{index}() -> {ty} {{ {value} }}\n"));
        if let Some(original) = bodies[..index].iter().position(|other| other == body) {
            expected.push((format!("f_{index}"), format!("f_{original}")));
        }
    }
    let output = support::analyze(&source, &[]).expect("analysis");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .filter(|finding: &serde_json::Value| finding["rule"] == "equivalent-implementation")
        .collect();
    let mut actual = Vec::new();
    for finding in findings {
        let related = finding["related"]
            .as_array()
            .expect("matching implementation");
        let [original] = related.as_slice() else {
            panic!("one original implementation per diagnostic: {finding}");
        };
        let start = original["label"]["span"]["start"].as_u64().expect("start") as usize;
        let end = original["label"]["span"]["end"].as_u64().expect("end") as usize;
        let (_, declaration) = source[start..end]
            .split_once("fn ")
            .expect("function declaration");
        let (name, _) = declaration.split_once('(').expect("function parameters");
        actual.push((
            finding["item"].as_str().expect("item").to_owned(),
            name.to_owned(),
        ));
    }
    assert_eq!(actual, expected, "{bodies:?}: {output}");
}
