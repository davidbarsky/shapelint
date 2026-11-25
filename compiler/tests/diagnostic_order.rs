#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

mod support;

use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::TyCtxt;
use shapelint::CompilerEvidence;
use shapelint_driver::analysis::Analysis;
use shapelint_driver::calls::{Dispatch, Instance, Target};
use shapelint_driver::contracts::graph::{TargetNode, with_graph};
use shapelint_driver::contracts::{
    self, Call, Condition, Consumer, Expr, Operation, Order, Requirement, Return, Summary,
};
use shapelint_driver::{artifacts, callers, pipeline};

#[derive(Debug, hegel::DefaultGenerator)]
enum ConsumerOrder {
    FirstThenSecond,
    SecondThenFirst,
}

#[hegel::test]
fn parallel_reporting_preserves_the_first_witness_and_validation_precedence(tc: hegel::TestCase) {
    #[derive(Debug, hegel::DefaultGenerator)]
    enum Calls {
        Direct,
        RecursiveCallback,
    }
    let (order, calls) = tc.draw(hegel::generators::default::<(ConsumerOrder, Calls)>());
    let (early, late) = match order {
        ConsumerOrder::FirstThenSecond => ("first", "second"),
        ConsumerOrder::SecondThenFirst => ("second", "first"),
    };
    let calls = match calls {
        Calls::Direct => "",
        Calls::RecursiveCallback => {
            r#"type Step = fn(u32) -> u32;
fn apply(step: Step, value: u32) -> u32 { step(value) }
fn back(value: u32) -> u32 { recur(value) }
pub fn recur(value: u32) -> u32 {
    if value > 1 { apply(back, value - 2) } else { value - 1 }
}"#
        }
    };
    let source = format!(
        r#"
pub struct Span {{ pub start: usize, pub end: usize }}
pub struct Window {{ start: usize, end: usize }}
pub fn reversed() -> Window {{ Window {{ start: 9, end: 0 }} }}
pub fn {early}(span: Span) -> usize {{ span.end - span.start }}
pub fn {early}_width(window: Window) -> usize {{ window.end - window.start }}
fn validate(index: usize, len: usize) {{ if index >= len {{ panic!("out of bounds"); }} }}
pub fn read(values: &[u8], index: usize) -> u8 {{
    validate(index, values.len());
    if index < values.len() {{ values[index] }} else {{ 0 }}
}}
pub fn {late}(span: Span) -> usize {{ span.end - span.start }}
pub fn {late}_width(window: Window) -> usize {{ window.end - window.start }}
{calls}
"#
    );
    let dir = tempfile::tempdir().expect("fixture directory");
    let path = dir.path().join("witnesses.rs");
    std::fs::write(&path, source).expect("fixture source");
    let summary = dir.path().join("summary.json");
    let run = |flags: &[&str]| {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_shapelint-driver"))
            .args([
                "--format=json",
                "--show-analysis-gaps",
                "--crate-type=lib",
                "--edition=2024",
                "--emit=metadata",
            ])
            .args(flags)
            .arg("--summary-output")
            .arg(&summary)
            .arg("--out-dir")
            .arg(dir.path())
            .arg(&path)
            .output()
            .expect("analyze witnesses");
        assert!(
            output.status.success() && output.stderr.is_empty(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let export = std::fs::read_to_string(&summary).expect("exported summary");
        let artifact: serde_json::Value = serde_json::from_str(&export).expect("artifact");
        let producer = artifact["crate_hash"].as_str().expect("producer hash");
        assert!(
            dir.path()
                .join(format!("libsummary-{producer}.rmeta"))
                .is_file()
        );
        (
            String::from_utf8(output.stdout).expect("UTF-8 report"),
            export.replace(producer, "<producer>"),
        )
    };
    let expected = run(&["-Zunstable-options", "--jobs-frontend=1"]);
    assert_eq!(
        expected,
        run(&["-Zunstable-options", "--jobs-frontend=6"]),
        "{order:?}"
    );
    assert_eq!(expected, run(&["-Zthreads=6"]), "{order:?}");
    let (serial, _) = expected;
    let findings: Vec<serde_json::Value> = serial
        .lines()
        .map(|line| serde_json::from_str(line).expect("finding"))
        .collect();
    let count = |rule: &str, item: &str| {
        findings
            .iter()
            .filter(|finding| finding["rule"] == rule && finding["item"] == item)
            .count()
    };
    assert_eq!(count("unencoded-precondition", "Span"), 1, "{serial}");
    assert_eq!(
        count("inconsistent-state-construction", "reversed"),
        1,
        "{serial}"
    );
    assert_eq!(count("discarded-validation", "read"), 1, "{serial}");
    assert_eq!(count("redundant-check", "read"), 0, "{serial}");
}

#[test]
fn callable_alternatives_keep_the_source_first_diagnostic_origin() {
    #[derive(Debug, serde::Serialize)]
    struct Diagnostic {
        operation: String,
        requirement: String,
        origin: shapelint::Related,
        explanation: String,
    }
    struct Check;
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let definitions: Vec<_> = tcx.hir_body_owners().collect();
            let first = definitions
                .iter()
                .copied()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "first")
                .expect("first target");
            let second = definitions
                .iter()
                .copied()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "second")
                .expect("second target");
            let root = definitions
                .iter()
                .copied()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "root")
                .expect("calling function");
            let hash_order: Vec<_> = with_graph(|mut graph| {
                let analyses: Vec<_> = definitions
                    .iter()
                    .map(|def| Analysis {
                        def: *def,
                        span: tcx.def_span(*def),
                        regions: None,
                        contracts: graph.freeze(Summary::default()).unwrap(),
                        findings: Vec::new(),
                        invariants: Vec::new(),
                        constructions: Vec::new(),
                        work: Default::default(),
                    })
                    .collect();
                let linked = pipeline::Collected::from(analyses).link(
                    artifacts::Inputs::default()
                        .import(tcx, &mut graph)
                        .expect("empty imports"),
                );
                let summaries: &pipeline::Summaries<'_> = linked.as_ref();
                summaries
                    .definitions
                    .keys()
                    .copied()
                    .filter(|def| tcx.item_name(*def).as_str().starts_with("holder_"))
                    .collect()
            });
            let (earlier, later) = hash_order
                .windows(2)
                .find_map(|pair| match pair {
                    [later, earlier] if tcx.def_span(*earlier).lo() < tcx.def_span(*later).lo() => {
                        Some((*earlier, *later))
                    }
                    _ => None,
                })
                .expect("the fixture contains a hash-order inversion among source-ordered holders");
            let findings = |definitions: &[LocalDefId]| {
                with_graph(|mut graph| {
                    let analyses: Vec<_> = definitions
                        .iter()
                        .map(|def| {
                            let owner = def.to_def_id();
                            let contracts = {
                                let mut summary = Summary::default();
                                let empty_guards = shapelint_driver::sequence::Sequence::EMPTY;
                                match owner {
                                    owner
                                        if owner == first.to_def_id()
                                            || owner == second.to_def_id() =>
                                    {
                                        let condition = graph
                                            .lower_condition(&Condition::Compare(
                                                Order::LessEqual,
                                                Expr::Number(1),
                                                Expr::Argument(0),
                                            ))
                                            .expect("condition");
                                        summary.requirements.push(Requirement {
                                            invalidated:
                                                shapelint_driver::sequence::Sequence::EMPTY,
                                            consumer: Consumer {
                                                def: owner,
                                                span: tcx.def_span(owner),
                                                operation: Operation::Subtraction {
                                                    left: Some("n".into()),
                                                    right: Some("1".into()),
                                                },
                                            },
                                            condition,
                                            guards: empty_guards,
                                            span: tcx.def_span(owner),
                                        });
                                    }
                                    owner if owner == earlier || owner == later => {
                                        let targets = match owner == earlier {
                                            true => [first, second],
                                            false => [second, first],
                                        };
                                        let value = Expr::Alternatives(
                                            targets
                                                .into_iter()
                                                .map(|def| {
                                                    Expr::Function(Instance {
                                                        def: def.to_def_id(),
                                                        args: Vec::new(),
                                                        dispatch: Dispatch::Item,
                                                    })
                                                })
                                                .collect(),
                                        );
                                        let value = graph.lower_expr(&value).expect("alternatives");
                                        summary.returns.push(Return {
                                            value,
                                            guards: empty_guards,
                                        });
                                    }
                                    owner if owner == root.to_def_id() => {
                                        let target = Expr::Call(
                                            Target::Direct(Instance {
                                                def: earlier,
                                                args: Vec::new(),
                                                dispatch: Dispatch::Item,
                                            }),
                                            Vec::new(),
                                            None,
                                        );
                                        let target = TargetNode::Indirect(
                                            graph.lower_expr(&target).expect("target"),
                                        );
                                        let argument =
                                            graph.lower_expr(&Expr::Argument(0)).expect("argument");
                                        let arguments = graph
                                            .expression_sequences
                                            .from_iter([argument])
                                            .expect("arguments");
                                        summary.calls.push(Call {
                                            basis: contracts::CheckBasis::Expression,
                                            target,
                                            arguments,
                                            guards: empty_guards,
                                            span: tcx.def_span(owner),
                                        });
                                    }
                                    _ => {}
                                }
                                graph.freeze(summary).expect("fixture summary")
                            };
                            Analysis {
                                def: *def,
                                span: tcx.def_span(*def),
                                regions: None,
                                contracts,
                                findings: Vec::new(),
                                invariants: Vec::new(),
                                constructions: Vec::new(),
                                work: Default::default(),
                            }
                        })
                        .collect();
                    let linked = pipeline::Collected::from(analyses).link(
                        artifacts::Inputs::default()
                            .import(tcx, &mut graph)
                            .expect("empty imports"),
                    );
                    contracts::findings(
                        tcx,
                        linked.as_ref(),
                        &mut graph,
                        callers::Scope::Library,
                        shapelint_driver::pipeline::AnalysisGaps::Show,
                        &shapelint_driver::diagnostics::Sources::default(),
                    )
                    .expect("contract analysis")
                    .findings
                    .into_iter()
                    .filter_map(|(owner, finding)| match (owner, finding.evidence) {
                        (
                            owner,
                            CompilerEvidence::UnprovenPrecondition {
                                operation,
                                requirement,
                                origin: Some(origin),
                                explanation,
                            },
                        ) if owner == root => Some(Diagnostic {
                            operation,
                            requirement,
                            origin,
                            explanation,
                        }),
                        _ => None,
                    })
                    .collect::<Vec<_>>()
                })
            };
            let forward = findings(&definitions);
            let reversed = definitions.iter().rev().copied().collect::<Vec<_>>();
            let reversed = findings(&reversed);
            assert_eq!(
                serde_json::to_value(&forward).expect("forward diagnostic"),
                serde_json::to_value(&reversed).expect("reversed diagnostic"),
                "summary insertion order changed the diagnostic or its related origin"
            );
            let [diagnostic] = forward.as_slice() else {
                panic!("expected one deduplicated requirement: {forward:?}");
            };
            assert_eq!(diagnostic.requirement, "requires n >= 1");
            assert_eq!(
                diagnostic.origin.label.message,
                "check originates in `first`"
            );
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("order.rs");
    let mut text = String::from(
        "pub fn first(n:u32)->u32{n-1}\npub fn second(n:u32)->u32{n-1}\npub fn root(n:u32)->u32{n}\n",
    );
    for index in 0..32 {
        use std::fmt::Write;
        writeln!(text, "pub fn holder_{index}()->fn(u32)->u32{{first}}").expect("fixture source");
    }
    std::fs::write(&source, text).expect("fixture source file");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        source.display().to_string(),
    ];
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Check));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Validation {
    Discarded,
    Repeated,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Validations {
    functions: Vec<Validation>,
}

#[hegel::test(print_blob = true)]
fn discarded_validations_suppress_only_their_own_redundant_checks(tc: hegel::TestCase) {
    #[derive(serde::Deserialize)]
    struct Diagnostic {
        item: String,
        rule: String,
    }

    let Validations { functions } = tc.draw(hegel::generators::default::<Validations>());
    let functions: Vec<_> = [Validation::Discarded, Validation::Repeated]
        .into_iter()
        .chain(functions)
        .collect();
    let mut source =
        String::from("fn validate(index: usize, len: usize) { if index >= len { panic!() } }\n");
    let mut expected = Vec::new();
    let indexed = functions.iter().enumerate();
    for (index, validation) in indexed {
        let (body, rule) = match validation {
            Validation::Discarded => (
                "validate(index, values.len()); if index < values.len() { values[index] } else { 0 }",
                "discarded-validation",
            ),
            Validation::Repeated => (
                "if index >= values.len() { return 0; } if index < values.len() { values[index] } else { 0 }",
                "redundant-check",
            ),
        };
        source.push_str(&format!(
            "pub fn read_{index}(values: &[u8], index: usize) -> u8 {{ {body} }}\n"
        ));
        expected.push((format!("read_{index}"), rule.to_owned()));
    }
    let output = support::analyze(&source, &[]).expect("analysis");
    let actual: Vec<_> = output
        .lines()
        .map(|line| serde_json::from_str::<Diagnostic>(line).expect("finding"))
        .filter_map(|finding| match finding.rule.as_str() {
            "discarded-validation" | "redundant-check" => Some((finding.item, finding.rule)),
            _ => None,
        })
        .collect();
    assert_eq!(actual, expected, "{functions:?}: {output}");
}

#[test]
fn unrelated_invalidated_fact_does_not_prove_a_precondition() {
    struct Check;
    impl rustc_driver::Callbacks for Check {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let root = tcx.hir_body_owners().next().expect("function");
            let def = root.to_def_id();
            let span = tcx.def_span(root);
            with_graph(|mut graph| {
                let contracts = {
                    let one = graph
                        .intern_expr(contracts::graph::ExprNode::Number(1))
                        .unwrap();
                    let amount = graph
                        .intern_expr(contracts::graph::ExprNode::Argument(0))
                        .unwrap();
                    let other = graph
                        .intern_expr(contracts::graph::ExprNode::Argument(1))
                        .unwrap();
                    let condition = graph
                        .intern_condition(contracts::graph::ConditionNode::Compare(
                            Order::LessEqual,
                            one,
                            amount,
                        ))
                        .unwrap();
                    let unrelated = graph
                        .intern_condition(contracts::graph::ConditionNode::Compare(
                            Order::LessEqual,
                            one,
                            other,
                        ))
                        .unwrap();
                    let invalidated = graph
                        .invalidated_sequences
                        .from_iter([contracts::InvalidatedFact {
                            condition: unrelated,
                            def,
                            span,
                        }])
                        .unwrap();
                    let summary = Summary {
                        requirements: vec![Requirement {
                            invalidated,
                            consumer: Consumer {
                                def,
                                span,
                                operation: Operation::Condition,
                            },
                            condition,
                            guards: shapelint_driver::sequence::Sequence::EMPTY,
                            span,
                        }],
                        ..Summary::default()
                    };
                    graph.freeze(summary).unwrap()
                };
                let analyses = vec![Analysis {
                    def: root,
                    span,
                    regions: None,
                    contracts,
                    findings: Vec::new(),
                    invariants: Vec::new(),
                    constructions: Vec::new(),
                    work: Default::default(),
                }];
                let linked = pipeline::Collected::from(analyses).link(
                    artifacts::Inputs::default()
                        .import(tcx, &mut graph)
                        .unwrap(),
                );
                let findings = contracts::findings(
                    tcx,
                    linked.as_ref(),
                    &mut graph,
                    callers::Scope::Library,
                    shapelint_driver::pipeline::AnalysisGaps::Show,
                    &Default::default(),
                )
                .unwrap();
                let [
                    (
                        _,
                        shapelint_driver::states::Finding {
                            evidence: CompilerEvidence::UnprovenPrecondition { .. },
                            ..
                        },
                    ),
                ] = findings.findings.as_slice()
                else {
                    panic!("an unrelated fact must leave one precondition unproven");
                };
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().unwrap();
    let source = directory.path().join("unrelated.rs");
    std::fs::write(
        &source,
        "pub fn run(amount: u32, other: u32) -> u32 { amount + other }",
    )
    .unwrap();
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        source.display().to_string(),
    ];
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Check));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[test]
fn optional_coverage_preserves_order_when_later_evidence_proves_the_same_failure() {
    let source = "fn a(x:u32, c:bool)->u32 {if c {x-1} else {x}}
        fn b(x:u32, _:bool)->u32 {x-2}
        fn d(x:u32, _:bool)->u32 {x-1}
        pub fn root(which:u8, c:bool)->u32 {
            let f:fn(u32,bool)->u32 = if which==0 {a} else if which==1 {b} else {d};
            f(0,c)
        }";
    let failures = |flags: &[&str]| {
        let output = support::analyze(source, flags).expect("driver analysis");
        output
            .lines()
            .map(|row| serde_json::from_str::<serde_json::Value>(row).expect("diagnostic"))
            .filter(|row| row["rule"] == "invalid-state-use" && row["item"] == "root")
            .map(|row| {
                row["primary"]["message"]
                    .as_str()
                    .expect("condition")
                    .to_owned()
            })
            .collect::<Vec<_>>()
    };
    let ordinary = failures(&[]);
    assert_eq!(ordinary, ["requires 0 >= 2", "requires 0 >= 1"]);
    assert_eq!(failures(&["--show-analysis-gaps"]), ordinary);
}
