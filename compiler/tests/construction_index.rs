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
