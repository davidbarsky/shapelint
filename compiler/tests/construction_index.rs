#![feature(rustc_private)]

mod support;

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Producer {
    Checked,
    Mutated,
    Unchecked,
    Unknown,
    Forwarded,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Owners {
    producers: Vec<Producer>,
}

#[hegel::test(print_blob = true)]
fn construction_guarantees_stay_with_their_owner_and_argument(tc: hegel::TestCase) {
    #[derive(serde::Deserialize)]
    struct Diagnostic {
        item: String,
        rule: String,
    }

    let Owners { producers } = tc.draw(hegel::generators::default::<Owners>());
    let producers: Vec<_> = [Producer::Checked, Producer::Unchecked, Producer::Forwarded]
        .into_iter()
        .chain(producers)
        .collect();
    let mut source = String::new();
    let mut expected = Vec::new();
    let entries = producers.iter().enumerate();
    for (index, producer) in entries {
        let extra = match producer {
            Producer::Checked => "",
            Producer::Forwarded => "pub fn forward(value: Self) -> Self { value }",
            Producer::Mutated => {
                expected.extend([
                    format!("read_{index}"),
                    format!("read_again_{index}"),
                    format!("read_shifted_{index}"),
                ]);
                "pub fn change(&mut self, value: usize) { self.start = value; }"
            }
            Producer::Unchecked => {
                expected.extend([
                    format!("read_{index}"),
                    format!("read_again_{index}"),
                    format!("read_shifted_{index}"),
                ]);
                "pub fn unchecked(start: usize, end: usize) -> Self { Self { start, end } }"
            }
            Producer::Unknown => {
                expected.extend([
                    format!("read_{index}"),
                    format!("read_again_{index}"),
                    format!("read_shifted_{index}"),
                ]);
                "pub fn receive(make: fn() -> Self) -> Self { make() }"
            }
        };
        source.push_str(&format!(
            "pub struct Span{index} {{ start: usize, end: usize }}
            impl Span{index} {{
                pub fn new(start: usize, end: usize) -> Option<Self> {{
                    if start <= end {{ Some(Self {{ start, end }}) }} else {{ None }}
                }}
                {extra}
            }}
            pub fn read_{index}(value: &Span{index}) -> usize {{ value.end - value.start }}
            pub fn read_again_{index}(value: &Span{index}) -> usize {{ value.end - value.start }}
            pub fn read_shifted_{index}(_: usize, value: &Span{index}) -> usize {{ value.end - value.start }}\n"
        ));
    }
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let actual: Vec<_> = output
        .lines()
        .map(|line| serde_json::from_str::<Diagnostic>(line).expect("finding"))
        .filter(|finding| {
            finding.rule == "unproven-precondition" && finding.item.starts_with("read_")
        })
        .map(|finding| finding.item)
        .collect();
    assert_eq!(actual, expected, "{producers:?}: {output}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum StateProducer {
    Duplicated,
    Mutated,
    Independent,
    Unknown,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct States {
    producers: Vec<StateProducer>,
}

#[hegel::test(print_blob = true)]
fn state_relations_use_only_their_owners_constructions_and_returns(tc: hegel::TestCase) {
    #[derive(serde::Deserialize)]
    struct Diagnostic {
        item: String,
        rule: String,
    }

    let States { producers } = tc.draw(hegel::generators::default::<States>());
    let producers: Vec<_> = [StateProducer::Duplicated, StateProducer::Unknown]
        .into_iter()
        .chain(producers)
        .collect();
    let mut source = String::new();
    let mut expected = Vec::new();
    let entries = producers.iter().enumerate();
    for (index, producer) in entries {
        let constructor = match producer {
            StateProducer::Independent => {
                "pub fn new(ready: bool, value: Option<u8>) -> Self { Self { ready, value } }"
            }
            StateProducer::Duplicated | StateProducer::Mutated | StateProducer::Unknown => {
                "pub fn new(value: Option<u8>) -> Self { Self { ready: value.is_some(), value } }"
            }
        };
        let extra = match producer {
            StateProducer::Duplicated => {
                expected.push(format!("State{index}"));
                ""
            }
            StateProducer::Independent => "",
            StateProducer::Mutated => {
                "pub fn change(&mut self, ready: bool) { self.ready = ready; }"
            }
            StateProducer::Unknown => "pub fn receive(make: fn() -> Self) -> Self { make() }",
        };
        source.push_str(&format!(
            "pub struct State{index} {{ ready: bool, value: Option<u8> }}
            impl State{index} {{
                {constructor}
                {extra}
                pub fn read(&self) -> Option<u8> {{ if self.ready {{ self.value }} else {{ None }} }}
            }}\n"
        ));
    }
    let output = support::analyze(&source, &["--show-analysis-gaps"]).expect("analysis");
    let actual: Vec<_> = output
        .lines()
        .map(|line| serde_json::from_str::<Diagnostic>(line).expect("finding"))
        .filter(|finding| finding.rule == "duplicated-state")
        .map(|finding| finding.item)
        .collect();
    assert_eq!(actual, expected, "{producers:?}: {output}");
}
