#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use std::fmt::Write;

use rustc_middle::ty::TyCtxt;
use shapelint_driver::contracts::graph::with_graph;
use shapelint_driver::{analysis, artifacts, callers, contracts, diagnostics, pipeline};

fn analyze(text: &str) -> (contracts::Work, Vec<shapelint::Finding>) {
    #[derive(Default)]
    struct Capture {
        result: Option<(contracts::Work, Vec<shapelint::Finding>)>,
    }
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            self.result = Some(with_graph(|mut graph| {
                let sources = diagnostics::Sources::default();
                let mut analyses = Vec::new();
                for def in tcx.hir_body_owners() {
                    let body = tcx.mir_promoted(def).0.borrow();
                    analyses.push(
                        analysis::analyze(tcx, def, &body, &mut graph, &[], &sources)
                            .expect("MIR analysis"),
                    );
                }
                let imported = artifacts::Inputs::default()
                    .import(tcx, &mut graph)
                    .expect("empty imports");
                let linked = pipeline::Collected::from(analyses).link(imported);
                let analyzed = linked
                    .analyze(
                        tcx,
                        &mut graph,
                        callers::Scope::Library,
                        shapelint_driver::pipeline::AnalysisGaps::Show,
                        &shapelint::Config::default(),
                        &sources,
                    )
                    .expect("linked analysis");
                let findings: &[pipeline::SourceFindings] = analyzed.as_ref();
                let findings = findings
                    .iter()
                    .flat_map(|source| source.findings.iter())
                    .filter(|finding| {
                        finding.rule == "unproven-precondition"
                            || finding.rule == "invalidated-validation"
                            || finding.rule == "invalid-state-use"
                            || finding.rule == "unencoded-precondition"
                    })
                    .cloned()
                    .collect();
                (analyzed.work, findings)
            }));
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("compiler outputs");
    let path = directory.path().join("fixture.rs");
    std::fs::write(&path, text).expect("fixture source");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--crate-name=shapelint_reference".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        path.display().to_string(),
    ];
    let mut callback = Capture::default();
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut callback));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
    callback.result.expect("analysis callback ran")
}

fn diamond(depth: usize) -> String {
    let flags = std::iter::repeat_n("bool", depth)
        .collect::<Vec<_>>()
        .join(", ");
    let mut source =
        format!("fn leaf(data: &[u8], index: usize, _flags: ({flags})) -> u8 {{ data[index] }}\n");
    let mut callee = String::from("leaf");
    for index in 0..depth {
        let name = format!("stage_{index}");
        writeln!(source, "fn {name}(data: &[u8], index: usize, flags: ({flags})) -> u8 {{ if flags.{index} {{ {callee}(data, index, flags) }} else {{ {callee}(data, index, flags) }} }}").expect("branch forwarder");
        callee = name;
    }
    writeln!(source, "pub fn root(data: &[u8], index: usize, flags: ({flags})) -> u8 {{ {callee}(data, index, flags) }}\n").expect("root");
    source
}

#[test]
fn complementary_branches_have_linear_requirement_work() {
    let observations = [2, 4, 8].map(|depth| {
        let source = diamond(depth);
        let (work, findings) = analyze(&source);
        assert_eq!(findings.len(), 1, "{findings:?}");
        let finding = &findings[0];
        assert_eq!(finding.item, "root");
        assert_eq!(finding.primary.message, "index < data.len()");
        assert_eq!(finding.related.len(), 1);
        assert_eq!(
            finding.related[0].label.message,
            "check originates in `leaf`"
        );
        let span = finding.related[0].label.span;
        assert_eq!(&source[std::ops::Range::<usize>::from(span)], "data[index]");
        eprintln!("diamond depth {depth}: {work:?}");
        work
    });
    let [small, medium, large] = observations;
    assert!(
        large.requirement_visits - medium.requirement_visits
            <= 2 * (medium.requirement_visits - small.requirement_visits),
        "{observations:?}"
    );
    assert!(
        large.requirement_nodes - medium.requirement_nodes
            <= 2 * (medium.requirement_nodes - small.requirement_nodes),
        "{observations:?}"
    );
    assert!(
        large.applicability_nodes - medium.applicability_nodes
            <= 2 * (medium.applicability_nodes - small.applicability_nodes),
        "{observations:?}"
    );
    assert!(
        large.requirement_join_visits - medium.requirement_join_visits
            <= 2 * (medium.requirement_join_visits - small.requirement_join_visits),
        "{observations:?}"
    );
}

#[derive(Clone, Copy, Debug)]
enum Noise {
    Identity,
    Changing,
}

fn unused_argument(count: usize, noise: Noise) -> String {
    let indices = (0..count)
        .map(|index| format!("data[{index}]"))
        .collect::<Vec<_>>()
        .join(", ");
    let mut source =
        format!("fn leaf(data: &[u8], _noise: usize) -> [u8; {count}] {{ [{indices}] }}\n");
    let mut callee = String::from("leaf");
    for index in 0..count {
        let (parameter, argument) = match noise {
            Noise::Identity => ("noise", String::from("noise")),
            Noise::Changing => ("_noise", index.to_string()),
        };
        let name = format!("stage_{index}");
        writeln!(source, "fn {name}(data: &[u8], {parameter}: usize) -> [u8; {count}] {{ {callee}(data, {argument}) }}").expect("argument forwarder");
        callee = name;
    }
    writeln!(
        source,
        "pub fn root(data: &[u8], noise: usize) -> [u8; {count}] {{ {callee}(data, noise) }}"
    )
    .expect("root");
    source
}

#[test]
fn identity_argument_control_has_linear_transformations() {
    let observations = [8, 16, 32].map(|count| {
        let (work, findings) = analyze(&unused_argument(count, Noise::Identity));
        assert_eq!(findings.len(), count, "{findings:?}");
        assert_eq!(work.requirement_transformations, count);
        work
    });
    eprintln!("identity argument: {observations:?}");
}

#[test]
fn changing_an_unused_argument_reuses_identity_transformations() {
    let observations = [8, 16, 32].map(|count| {
        let (identity, expected) = analyze(&unused_argument(count, Noise::Identity));
        let (changing, actual) = analyze(&unused_argument(count, Noise::Changing));
        assert_eq!(actual.len(), count);
        let diagnostic = |finding: &shapelint::Finding| {
            (
                finding.item.clone(),
                finding.primary.message.clone(),
                finding
                    .related
                    .iter()
                    .map(|related| (related.label.message.clone(), related.label.span))
                    .collect::<Vec<_>>(),
            )
        };
        assert_eq!(
            actual.iter().map(diagnostic).collect::<Vec<_>>(),
            expected.iter().map(diagnostic).collect::<Vec<_>>()
        );
        eprintln!("unused argument {count}: identity {identity:?}, changing {changing:?}");
        assert_eq!(
            changing.requirement_applications, identity.requirement_applications,
            "unused arguments cannot distinguish plan applications"
        );
        (
            identity.requirement_transformations,
            changing.requirement_transformations,
        )
    });
    for (identity, changing) in observations {
        assert_eq!(
            changing, identity,
            "unused arguments cannot distinguish transformation queries"
        );
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Branch {
    Forward,
    Skip,
    Checked,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
struct Paths {
    then_branch: Branch,
    else_branch: Branch,
}

#[hegel::test(print_blob = true)]
fn branch_requirements_agree_with_exhaustive_path_oracle(tc: hegel::TestCase) {
    let Paths {
        then_branch,
        else_branch,
    } = tc.draw(hegel::generators::default::<Paths>());
    let body = |branch| match branch {
        Branch::Forward => "leaf(data, index)",
        Branch::Skip => "0",
        Branch::Checked => "if index < data.len() { leaf(data, index) } else { 0 }",
    };
    let source = format!(
        "fn leaf(data: &[u8], index: usize) -> u8 {{ data[index] }}\npub fn root(data: &[u8], index: usize, flag: bool) -> u8 {{ let _ = (data, index, leaf as fn(&[u8], usize) -> u8); if flag {{ {} }} else {{ {} }} }}",
        body(then_branch),
        body(else_branch)
    );
    let (_, findings) = analyze(&source);
    // Enumerate each feasible branch independently; checked paths discharge the bound.
    let mut unresolved = Vec::new();
    for branch in [then_branch, else_branch] {
        match branch {
            Branch::Forward => unresolved.push(()),
            Branch::Skip | Branch::Checked => {}
        }
    }
    match unresolved.as_slice() {
        [] => assert!(findings.is_empty(), "{source}\n{findings:?}"),
        [..] => {
            assert_eq!(findings.len(), unresolved.len(), "{source}\n{findings:?}");
            let mut previous = 0;
            for finding in findings {
                assert_eq!(finding.item, "root");
                assert_eq!(
                    finding.related[0].label.message,
                    "check originates in `leaf`"
                );
                let span = finding.primary.span;
                assert_eq!(
                    &source[std::ops::Range::<usize>::from(span)],
                    "leaf(data, index)"
                );
                assert!(span.start >= previous);
                previous = span.end;
            }
        }
    }
}

#[test]
fn one_sided_requirement_remains_conditional_at_callers() {
    let source = r#"
fn leaf(data: &[u8], index: usize) -> u8 { data[index] }
fn conditional(data: &[u8], index: usize, flag: bool) -> u8 {
    if flag { leaf(data, index) } else { 0 }
}
pub fn skipped(data: &[u8], index: usize) -> u8 { conditional(data, index, false) }
pub fn checked(data: &[u8], index: usize) -> u8 {
    if index < data.len() { conditional(data, index, true) } else { 0 }
}
pub fn unchecked(data: &[u8], index: usize) -> u8 { conditional(data, index, true) }
"#;
    let (_, findings) = analyze(source);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].item, "unchecked");
    assert_eq!(
        findings[0].related[0].label.message,
        "check originates in `leaf`"
    );
}

#[test]
fn branch_origins_remain_in_source_order() {
    let source = r#"
fn first(data: &[u8], index: usize) -> u8 { data[index] }
fn second(data: &[u8], index: usize) -> u8 { data[index] }
pub fn root(data: &[u8], index: usize, flag: bool) -> u8 {
    if flag { first(data, index) } else { second(data, index) }
}
"#;
    let (_, findings) = analyze(source);
    let origins: Vec<_> = findings
        .iter()
        .flat_map(|finding| &finding.related)
        .map(|related| related.label.message.as_str())
        .collect();
    assert_eq!(
        origins,
        [
            "check originates in `first`",
            "check originates in `second`"
        ]
    );
    for finding in findings {
        assert_eq!(finding.item, "root");
        assert_eq!(finding.primary.message, "index < data.len()");
    }
}

#[test]
fn branch_mutation_keeps_invalidation_distinct_from_checked_path() {
    let source = r#"
pub fn root(data: &mut Vec<u8>, index: usize, flag: bool) -> Option<u8> {
    if index < data.len() {
        if flag {
            data.clear();
            Some(data[index])
        } else {
            Some(data[index])
        }
    } else { None }
}
"#;
    let (_, findings) = analyze(source);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "invalidated-validation");
    assert_eq!(findings[0].item, "root");
    let span = findings[0].primary.span;
    assert_eq!(&source[std::ops::Range::<usize>::from(span)], "[index]");
}

fn assert_report_preserves_requirement(text: &str) {
    let (_, findings) = analyze(text);
    assert!(
        findings.iter().any(|finding| {
            finding.rule == "unproven-precondition"
                || finding.rule == "invalid-state-use"
                || finding.rule == "invalidated-validation"
        }),
        "{findings:?}"
    );
}

#[test]
fn report_certificate_keeps_select_dependent_conditions_contextual() {
    assert_report_preserves_requirement(
        r#"
fn leaf(data: &[u8], index: usize, flag: bool) -> u8 {
    let selected = if flag { index } else { data.len() };
    data[selected]
}
pub fn root(data: &[u8], index: usize, flag: bool) -> u8 { leaf(data, index, flag) }
"#,
    );
}

#[test]
fn report_certificate_keeps_test_dependent_conditions_contextual() {
    assert_report_preserves_requirement(
        r#"
pub fn root(data: &[u8], flag: bool) -> u8 { data[flag as usize] }
"#,
    );
}

#[test]
fn report_certificate_keeps_range_requirements_contextual() {
    assert_report_preserves_requirement(
        r#"
fn leaf(data: &[u8], index: usize) -> usize { data[index..].len() }
pub fn root(data: &[u8], index: usize) -> usize { leaf(data, index) }
"#,
    );
}

#[test]
fn report_certificate_keeps_subtraction_requirements_contextual() {
    assert_report_preserves_requirement(
        r#"
fn leaf(data: &[u8], index: usize) -> u8 { data[index - 1] }
pub fn root(data: &[u8], index: usize) -> u8 { leaf(data, index) }
"#,
    );
}

#[test]
fn report_certificate_keeps_local_callee_results_contextual() {
    assert_report_preserves_requirement(
        r#"
fn choose(data: &[u8], index: usize, flag: bool) -> usize {
    if flag { index } else { data.len() }
}
pub fn root(data: &[u8], index: usize, flag: bool) -> u8 { data[choose(data, index, flag)] }
"#,
    );
}

#[test]
fn report_certificate_does_not_shortcut_invalidated_requirements() {
    let source = r#"
pub fn root(data: &mut Vec<u8>, index: usize) -> Option<u8> {
    if index < data.len() {
        data.clear();
        Some(data[index])
    } else { None }
}
"#;
    let (_, findings) = analyze(source);
    assert!(
        findings
            .iter()
            .any(|finding| finding.rule == "invalidated-validation"),
        "{findings:?}"
    );
}

#[test]
fn complementary_refuted_paths_preserve_conditional_failure_classification() {
    let source = r#"
fn leaf(data: &[u8], index: usize) -> u8 { data[index] }
pub fn conditional(data: &[u8], flag: bool) -> u8 {
    if flag { leaf(data, data.len()) } else { leaf(data, data.len()) }
}
pub fn unconditional(data: &[u8]) -> u8 { leaf(data, data.len()) }
"#;
    let (_, findings) = analyze(source);
    let classification: Vec<_> = findings
        .iter()
        .map(|finding| (finding.item.as_str(), finding.rule))
        .collect();
    assert_eq!(
        classification,
        [
            ("conditional", "unproven-precondition"),
            ("conditional", "unproven-precondition"),
            ("unconditional", "invalid-state-use")
        ],
        "{findings:?}"
    );
    for finding in findings {
        assert_eq!(
            finding.related[0].label.message,
            "check originates in `leaf`"
        );
    }
}

fn bounds_after_argument_evaluation<'a>(
    rust_text: &str,
    findings: &'a [shapelint::Finding],
) -> &'a shapelint::Finding {
    let [bounds, addition] = findings else {
        panic!("expected the bounds and addition checks: {findings:?}")
    };
    assert_eq!(addition.item, "root");
    assert_eq!(addition.rule, "unproven-precondition");
    assert_eq!(
        &rust_text[std::ops::Range::<usize>::from(addition.primary.span)],
        "noise + 1"
    );
    bounds
}

#[test]
fn changing_a_used_argument_changes_the_remaining_requirement() {
    let source = r#"
fn leaf(data: &[u8], index: usize, _noise: usize) -> u8 { data[index] }
fn forward(data: &[u8], index: usize, noise: usize) -> u8 { leaf(data, index, noise) }
pub fn root(data: &[u8], noise: usize) -> Option<(u8, u8)> {
    if 0 < data.len() {
        Some((forward(data, 0, noise), forward(data, 1, noise + 1)))
    } else { None }
}
"#;
    let (_, findings) = analyze(source);
    let bounds = bounds_after_argument_evaluation(source, &findings);
    assert_eq!(bounds.item, "root");
    assert_eq!(bounds.primary.message, "1 < data.len()");
    assert_eq!(
        bounds.related[0].label.message,
        "check originates in `leaf`"
    );
}

#[test]
fn arguments_used_only_in_guards_distinguish_substitutions() {
    let source = r#"
fn leaf(data: &[u8], index: usize) -> u8 { data[index] }
fn gated(data: &[u8], index: usize, gate: usize) -> u8 {
    if gate == 0 { leaf(data, index) } else { 0 }
}
pub fn root(data: &[u8], index: usize) -> (u8, u8) {
    (gated(data, index, 1), gated(data, index, 0))
}
"#;
    let (_, findings) = analyze(source);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].item, "root");
    assert_eq!(findings[0].primary.message, "index < data.len()");
    let span = findings[0].primary.span;
    assert_eq!(
        &source[std::ops::Range::<usize>::from(span)],
        "gated(data, index, 0)"
    );
}

#[test]
fn swapping_caller_arguments_preserves_parameter_positions() {
    let source = r#"
fn leaf(data: &[u8], _other: &[u8], index: usize) -> u8 { data[index] }
fn swapped(first: &[u8], second: &[u8], index: usize) -> u8 { leaf(second, first, index) }
pub fn checked_first(first: &[u8], second: &[u8], index: usize) -> u8 {
    if index < first.len() { swapped(first, second, index) } else { 0 }
}
pub fn checked_second(first: &[u8], second: &[u8], index: usize) -> u8 {
    if index < second.len() { swapped(first, second, index) } else { 0 }
}
"#;
    let (_, findings) = analyze(source);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].item, "checked_first");
    assert_eq!(findings[0].primary.message, "index < second.len()");
    assert_eq!(
        findings[0].related[0].label.message,
        "check originates in `leaf`"
    );
}

#[test]
fn aliased_caller_arguments_share_the_same_bound() {
    let source = r#"
fn leaf(data: &[u8], _other: &[u8], index: usize) -> u8 { data[index] }
fn swapped(first: &[u8], second: &[u8], index: usize) -> u8 { leaf(second, first, index) }
pub fn root(data: &[u8], index: usize) -> u8 {
    if index < data.len() { swapped(data, data, index) } else { 0 }
}
"#;
    let (_, findings) = analyze(source);
    assert!(findings.is_empty(), "{findings:?}");
}

#[test]
fn forwarding_keeps_the_invalidated_fact_and_mutation_origin() {
    let source = r#"
fn leaf(data: &mut Vec<u8>, index: usize) -> Option<u8> {
    if index < data.len() {
        data.clear();
        Some(data[index])
    } else { None }
}
fn forward(data: &mut Vec<u8>, index: usize) -> Option<u8> { leaf(data, index) }
pub fn root(data: &mut Vec<u8>, index: usize) -> Option<u8> { forward(data, index) }
"#;
    let (_, findings) = analyze(source);
    let invalidated: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "invalidated-validation")
        .collect();
    assert_eq!(invalidated.len(), 1, "{findings:?}");
    assert_eq!(invalidated[0].item, "leaf");
    let mutations: Vec<_> = invalidated[0]
        .related
        .iter()
        .map(|related| &source[std::ops::Range::<usize>::from(related.label.span)])
        .collect();
    assert!(mutations.contains(&"data.clear()"), "{findings:?}");
}

#[test]
fn private_concrete_failure_is_reported_without_an_exported_call() {
    let source = r#"
fn private(data: &[u8]) -> u8 { data[data.len()] }
pub fn export() -> fn(&[u8]) -> u8 { private }
"#;
    let (_, findings) = analyze(source);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "invalid-state-use");
    assert_eq!(findings[0].item, "private");
}

#[test]
fn private_invalidated_validation_is_reported_without_an_exported_call() {
    let source = r#"
fn private(data: &mut Vec<u8>, index: usize) -> Option<u8> {
    if index < data.len() {
        data.clear();
        Some(data[index])
    } else { None }
}
pub fn export() -> fn(&mut Vec<u8>, usize) -> Option<u8> { private }
"#;
    let (_, findings) = analyze(source);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "invalidated-validation");
    assert_eq!(findings[0].item, "private");
}

#[test]
fn private_unresolved_requirement_is_retained_for_exported_callers() {
    let source = r#"
fn leaf(data: &[u8], index: usize) -> u8 { data[index] }
fn private(data: &[u8], index: usize) -> u8 { leaf(data, index) }
pub fn root(data: &[u8], index: usize) -> u8 { private(data, index) }
"#;
    let (_, findings) = analyze(source);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "unproven-precondition");
    assert_eq!(findings[0].item, "root");
    assert_eq!(findings[0].primary.message, "index < data.len()");
    assert_eq!(
        findings[0].related[0].label.message,
        "check originates in `leaf`"
    );
}

#[test]
fn private_unresolved_requirement_is_not_reported_without_an_exported_call() {
    let source = r#"
fn private(data: &[u8], index: usize) -> u8 { data[index] }
pub fn export() -> fn(&[u8], usize) -> u8 { private }
"#;
    let (_, findings) = analyze(source);
    assert!(findings.is_empty(), "{findings:?}");
}

#[test]
fn opaque_forwarding_preserves_the_requirement_display() {
    let source = r#"
fn unknown(value: usize) -> Option<usize> { std::hint::black_box(Some(value)) }
fn leaf(value: usize) -> usize { unknown(value).unwrap() }
fn middle(flag: bool) -> usize { if flag { leaf(0) } else { leaf(1) } }
pub fn root(flag: bool) -> usize { middle(flag) }
"#;
    let (_, findings) = analyze(source);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].item, "root");
    assert_eq!(
        findings[0].primary.message,
        "the value must be option::Option::Some"
    );
}

#[test]
fn private_consumer_preserves_representation_finding_and_origin() {
    let source = r#"pub struct Span { pub start: usize, pub end: usize }
fn consume(span: Span) -> usize { span.end - span.start }
pub fn wrapper(span: Span) { consume(span); }
pub fn other(span: Span) { consume(span); }
"#;
    let (_, findings) = analyze(source);
    let representations: Vec<_> = findings
        .iter()
        .filter(|finding| finding.rule == "unencoded-precondition")
        .collect();
    assert_eq!(representations.len(), 1, "{findings:?}");
    assert_eq!(representations[0].item, "Span");
    assert_eq!(representations[0].primary.message, "requires start <= end");
    let evidence =
        serde_json::to_value(representations[0]).expect("serialized representation evidence");
    let footers = evidence["footers"].as_array().expect("footers");
    let Some(_) = footers.iter().find(|footer| {
        footer["message"]
            .as_str()
            .expect("footer message")
            .contains("Required by `consume`")
    }) else {
        panic!("missing original consumer: {findings:?}");
    };
}

#[test]
fn opaque_substitution_preserves_used_arguments() {
    use shapelint_driver::contracts::Invocation;
    use shapelint_driver::contracts::graph::ExprNode;

    with_graph(|mut graph| {
        let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let start = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let end = graph.intern_expr(ExprNode::Number(1)).unwrap();
        let slice = graph
            .intern_expr(ExprNode::Slice {
                text: argument,
                start,
                end,
            })
            .unwrap();
        let first = graph.values.intern_text("first").unwrap();
        let first = graph.intern_expr(ExprNode::Text(first)).unwrap();
        let second = graph.values.intern_text("second").unwrap();
        let second = graph.intern_expr(ExprNode::Text(second)).unwrap();
        let first_arguments = graph.expression_sequences.from_iter([first]).unwrap();
        let second_arguments = graph.expression_sequences.from_iter([second]).unwrap();
        let expected_first = graph
            .intern_expr(ExprNode::Slice {
                text: first,
                start,
                end,
            })
            .unwrap();
        let expected_second = graph
            .intern_expr(ExprNode::Slice {
                text: second,
                start,
                end,
            })
            .unwrap();
        assert_eq!(
            graph
                .substitute_expr(slice, &first_arguments, &Invocation::LOCAL)
                .unwrap(),
            expected_first
        );
        assert_eq!(
            graph
                .substitute_expr(slice, &second_arguments, &Invocation::LOCAL)
                .unwrap(),
            expected_second
        );
        assert_eq!(
            graph
                .substitute_expr(slice, &first_arguments, &Invocation::LOCAL)
                .unwrap(),
            expected_first
        );
    });
}

#[hegel::test(print_blob = true)]
fn guard_substitution_keeps_inputs_outside_the_main_condition(tc: hegel::TestCase) {
    use shapelint_driver::contracts::graph::{ConditionNode, ExprNode};
    use shapelint_driver::contracts::{Invocation, Order};

    let number = u128::from(tc.draw(hegel::generators::integers::<u64>()));
    with_graph(|mut graph| {
        let argument = graph.intern_expr(ExprNode::Argument(1)).unwrap();
        let first = graph.intern_expr(ExprNode::Number(number)).unwrap();
        let second = graph.intern_expr(ExprNode::Number(number + 1)).unwrap();
        let guard = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, argument, first))
            .unwrap();
        let guards = graph.condition_sequences.from_iter([guard]).unwrap();
        let first_arguments = graph
            .expression_sequences
            .from_iter([first, first])
            .unwrap();
        let second_arguments = graph
            .expression_sequences
            .from_iter([first, second])
            .unwrap();
        let first_guard = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, first, first))
            .unwrap();
        let second_guard = graph
            .intern_condition(ConditionNode::Compare(Order::Equal, second, first))
            .unwrap();
        let first_expected = graph.condition_sequences.from_iter([first_guard]).unwrap();
        let second_expected = graph.condition_sequences.from_iter([second_guard]).unwrap();
        assert_eq!(
            graph
                .substitute_guards(&guards, &first_arguments, &Invocation::LOCAL)
                .unwrap(),
            first_expected
        );
        assert_eq!(
            graph
                .substitute_guards(&guards, &second_arguments, &Invocation::LOCAL)
                .unwrap(),
            second_expected
        );
        assert_eq!(
            graph
                .substitute_guards(&guards, &first_arguments, &Invocation::LOCAL)
                .unwrap(),
            first_expected
        );
    });
}

#[test]
fn private_unresolved_forwarders_do_not_materialize_or_describe_every_report() {
    let observations = [8, 16, 32].map(|count| {
        let (work, findings) = analyze(&unused_argument(count, Noise::Identity));
        assert_eq!(findings.len(), count, "{findings:?}");
        assert_eq!(
            work.descriptions_rendered, count,
            "only exported unresolved diagnostics need descriptions: {work:?}"
        );
        eprintln!("private reporting {count}: {work:?}");
        work
    });
    let [small, medium, large] = observations;
    assert!(
        large.reporting_materializations - medium.reporting_materializations
            <= 2 * (medium.reporting_materializations - small.reporting_materializations),
        "{observations:?}"
    );
    assert!(
        large.reporting_classifications - medium.reporting_classifications
            <= 2 * (medium.reporting_classifications - small.reporting_classifications),
        "local classification must reuse private forwarding summaries: {observations:?}"
    );
    assert!(
        large.reporting_plan_visits - medium.reporting_plan_visits
            <= 2 * (medium.reporting_plan_visits - small.reporting_plan_visits),
        "report demands must share transformed plans: {observations:?}"
    );
}

#[test]
fn deep_complementary_branches_keep_linear_created_structure() {
    let observations = [8, 16, 32].map(|depth| {
        let (work, findings) = analyze(&diamond(depth));
        assert_eq!(findings.len(), 1, "{findings:?}");
        assert_eq!(findings[0].item, "root");
        eprintln!("deep diamond {depth}: {work:?}");
        work
    });
    let [small, medium, large] = observations;
    assert!(
        large.requirement_visits - medium.requirement_visits
            <= 2 * (medium.requirement_visits - small.requirement_visits),
        "{observations:?}"
    );
    assert!(
        large.requirement_nodes - medium.requirement_nodes
            <= 2 * (medium.requirement_nodes - small.requirement_nodes),
        "{observations:?}"
    );
    assert!(
        large.applicability_nodes - medium.applicability_nodes
            <= 2 * (medium.applicability_nodes - small.applicability_nodes),
        "{observations:?}"
    );
    assert!(
        large.requirement_join_visits - medium.requirement_join_visits
            <= 2 * (medium.requirement_join_visits - small.requirement_join_visits),
        "{observations:?}"
    );
}

#[test]
fn one_forwarder_joins_distinct_obligations_with_linear_work() {
    let observations = [8, 16, 32].map(|count| {
        let indices = (0..count).map(|index| format!("data[{index}]")).collect::<Vec<_>>().join(", ");
        let source = format!("fn leaf(data: &[u8]) -> [u8; {count}] {{ [{indices}] }}\npub fn root(data: &[u8]) -> [u8; {count}] {{ leaf(data) }}\n");
        let (work, findings) = analyze(&source);
        assert_eq!(findings.len(), count, "{findings:?}");
        for finding in findings {
            assert_eq!(finding.item, "root");
            assert_eq!(finding.related[0].label.message, "check originates in `leaf`");
        }
        eprintln!("distinct obligations {count}: {work:?}");
        work
    });
    let [small, medium, large] = observations;
    assert!(
        large.requirement_join_visits - medium.requirement_join_visits
            <= 2 * (medium.requirement_join_visits - small.requirement_join_visits),
        "one forwarded set must not rescan each growing prefix: {observations:?}"
    );
}

#[test]
fn refuted_prefixes_do_not_enumerate_all_complementary_paths() {
    let observations = [8, 16, 32].map(|depth| {
        let mut source = diamond(depth);
        let root = source.find("pub fn root").expect("generated root");
        source.truncate(root);
        let flags = std::iter::repeat_n("false", depth)
            .collect::<Vec<_>>()
            .join(", ");
        writeln!(
            source,
            "pub fn root(data: &[u8], index: usize) -> u8 {{ stage_{}(data, index, ({flags})) }}",
            depth - 1
        )
        .expect("constant false root");
        let (work, findings) = analyze(&source);
        assert_eq!(findings.len(), 1, "{findings:?}");
        assert_eq!(findings[0].item, "root");
        assert_eq!(findings[0].primary.message, "index < data.len()");
        assert_eq!(
            findings[0].related[0].label.message,
            "check originates in `leaf`"
        );
        eprintln!("last feasible diamond path {depth}: {work:?}");
        work
    });
    let [small, medium, large] = observations;
    // Every private summary may still inspect a prefix as long as its depth.
    assert!(
        large.applicability_visits - medium.applicability_visits
            <= 4 * (medium.applicability_visits - small.applicability_visits),
        "prefix inspection may be quadratic across summaries, but cannot enumerate branch assignments: {observations:?}"
    );
}

#[test]
fn shared_infeasible_subgraphs_are_not_revisited_for_each_branch_path() {
    let observations = [8, 16, 32].map(|depth| {
        let flags = std::iter::repeat_n("bool", depth).collect::<Vec<_>>().join(", ");
        let mut source = format!("fn leaf(data: &[u8], index: usize, _flags: ({flags}), gate: bool) -> u8 {{ if gate {{ data[index] }} else {{ 0 }} }}\n");
        let mut callee = String::from("leaf");
        for index in 0..depth {
            let name = format!("stage_{index}");
            writeln!(source, "fn {name}(data: &[u8], index: usize, flags: ({flags}), gate: bool) -> u8 {{ if flags.{index} {{ {callee}(data, index, flags, gate) }} else {{ {callee}(data, index, flags, gate) }} }}").expect("gated branch forwarder");
            callee = name;
        }
        writeln!(source, "pub fn root(data: &[u8], index: usize, flags: ({flags})) -> u8 {{ {callee}(data, index, flags, false) }}").expect("closed leaf gate");
        let (work, findings) = analyze(&source);
        assert!(findings.is_empty(), "{findings:?}");
        eprintln!("infeasible shared leaf {depth}: {work:?}");
        work
    });
    let [small, medium, large] = observations;
    assert!(
        large.applicability_visits - medium.applicability_visits
            <= 4 * (medium.applicability_visits - small.applicability_visits),
        "shared impossible obligations cannot enumerate branch assignments: {observations:?}"
    );
}

#[test]
fn unused_argument_projection_inspects_linear_argument_positions() {
    let observations = [8, 16, 32].map(|count| {
        let (work, findings) = analyze(&unused_argument(count, Noise::Changing));
        assert_eq!(findings.len(), count, "{findings:?}");
        eprintln!("argument projection {count}: {work:?}");
        work
    });
    let [small, medium, large] = observations;
    assert!(
        large.argument_projections - medium.argument_projections
            <= 2 * (medium.argument_projections - small.argument_projections),
        "projection queries must scale with distinct argument contexts: {observations:?}"
    );
    assert!(
        large.argument_projection_positions - medium.argument_projection_positions
            <= 2 * (medium.argument_projection_positions - small.argument_projection_positions),
        "cache hits must not rescan every argument position: {observations:?}"
    );
    assert!(
        large.plan_input_visits - medium.plan_input_visits
            <= 2 * (medium.plan_input_visits - small.plan_input_visits),
        "plan dependency summaries must be shared: {observations:?}"
    );
    assert!(
        large.plan_input_positions - medium.plan_input_positions
            <= 2 * (medium.plan_input_positions - small.plan_input_positions),
        "nested plans must not repeatedly scan unchanged argument positions: {observations:?}"
    );
    let counts = observations.map(|work| work.report_support_visits);
    let [small, medium, large] = counts;
    assert!(
        large - medium <= 3 * (medium - small),
        "support visits must reuse shared guard prefixes: {counts:?}"
    );
    let counts = observations.map(|work| work.report_projection_guards);
    let [small, medium, large] = counts;
    assert!(
        large - medium <= 3 * (medium - small),
        "projection guards must reuse shared guard prefixes: {counts:?}"
    );
    let counts = observations.map(|work| work.report_projection_storage);
    let [small, medium, large] = counts;
    assert!(
        large - medium <= 3 * (medium - small),
        "projection storage must reuse shared guard prefixes: {counts:?}"
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum SubstitutionShape {
    Length,
    Slice,
    ScopedCursor,
    Unknown,
    Opaque,
    IndirectCall,
    Returned,
    Found,
    Tokens,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ArgumentPresence {
    Complete,
    MissingGuard,
    MissingAll,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum SubstitutionScope {
    Preserve,
    Forget,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Substitutions {
    shape: SubstitutionShape,
    presence: ArgumentPresence,
    scope: SubstitutionScope,
    value: u64,
    guard: u64,
    noise: Vec<u64>,
}

#[derive(Debug, PartialEq)]
struct SubstitutionObservation {
    expression: contracts::Expr,
    condition: contracts::Condition,
    guards: Vec<contracts::Condition>,
    truth: contracts::Truth,
    evidence: Vec<contracts::Condition>,
}

fn substitution_observation<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    shape: SubstitutionShape,
    presence: ArgumentPresence,
    scope: SubstitutionScope,
    value: u128,
    guard: u128,
    noise: u128,
) -> SubstitutionObservation {
    use shapelint_driver::contracts::graph::evidence::Proof;
    use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, TargetNode};
    use shapelint_driver::contracts::{Invocation, Order, Relocation};

    let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
    let guard_argument = graph.intern_expr(ExprNode::Argument(2)).unwrap();
    let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
    let one = graph.intern_expr(ExprNode::Number(1)).unwrap();
    let expression = match shape {
        SubstitutionShape::Length => graph.intern_expr(ExprNode::Length(argument)).unwrap(),
        SubstitutionShape::Slice => graph
            .intern_expr(ExprNode::Slice {
                text: argument,
                start: zero,
                end: one,
            })
            .unwrap(),
        SubstitutionShape::Unknown => graph.intern_expr(ExprNode::Unknown).unwrap(),
        SubstitutionShape::Opaque => {
            let origin = graph
                .values
                .intern_origin(&contracts::Origin {
                    def: rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
                    name: None,
                    adt: None,
                    identity: None,
                })
                .unwrap();
            graph.intern_expr(ExprNode::Opaque(origin)).unwrap()
        }
        SubstitutionShape::IndirectCall => {
            let arguments = graph.expression_sequences.from_iter([argument]).unwrap();
            graph
                .intern_expr(ExprNode::Call(
                    TargetNode::Indirect(guard_argument),
                    arguments,
                    None,
                ))
                .unwrap()
        }
        SubstitutionShape::Returned => {
            let arguments = graph.expression_sequences.from_iter([argument]).unwrap();
            let condition = graph
                .intern_condition(ConditionNode::Returned(
                    TargetNode::Indirect(guard_argument),
                    arguments,
                ))
                .unwrap();
            graph.intern_expr(ExprNode::Test(condition)).unwrap()
        }
        SubstitutionShape::Found => graph
            .intern_expr(ExprNode::Found {
                text: argument,
                pattern: guard_argument,
            })
            .unwrap(),
        SubstitutionShape::Tokens => graph
            .intern_expr(ExprNode::Tokens {
                text: argument,
                consumed: guard_argument,
            })
            .unwrap(),
        SubstitutionShape::ScopedCursor => graph
            .intern_expr(ExprNode::Cursor {
                def: rustc_hir::def_id::CRATE_DEF_ID.to_def_id(),
                local: rustc_middle::mir::Local::from_usize(0),
            })
            .unwrap(),
    };
    let condition = graph
        .intern_condition(ConditionNode::Compare(Order::Equal, argument, zero))
        .unwrap();
    let guard_condition = graph
        .intern_condition(ConditionNode::Compare(Order::Equal, guard_argument, zero))
        .unwrap();
    let guards = graph
        .condition_sequences
        .from_iter([condition, guard_condition])
        .unwrap();
    let value = graph.intern_expr(ExprNode::Number(value)).unwrap();
    let guard = graph.intern_expr(ExprNode::Number(guard)).unwrap();
    let noise = graph.intern_expr(ExprNode::Number(noise)).unwrap();
    let arguments = match presence {
        ArgumentPresence::Complete => graph
            .expression_sequences
            .from_iter([value, noise, guard])
            .unwrap(),
        ArgumentPresence::MissingGuard => graph
            .expression_sequences
            .from_iter([value, noise])
            .unwrap(),
        ArgumentPresence::MissingAll => shapelint_driver::sequence::Sequence::EMPTY,
    };
    let invocation = match scope {
        SubstitutionScope::Preserve => Invocation::LOCAL,
        SubstitutionScope::Forget => Invocation {
            relocation: Relocation::Into(None),
            generics: shapelint_driver::values::GenericsId::EMPTY,
        },
    };
    let expression = graph
        .substitute_expr(expression, &arguments, &invocation)
        .unwrap();
    let condition = graph
        .substitute_condition(condition, &arguments, &invocation)
        .unwrap();
    let guards = graph
        .substitute_guards(&guards, &arguments, &invocation)
        .unwrap();
    let proof = graph.prove(condition, &guards).unwrap();
    let truth = contracts::Truth::from(proof);
    let evidence = match proof {
        Proof::Proven(evidence) | Proof::Refuted(evidence) => {
            let evidence = graph.evidence_sequence(evidence).unwrap();
            graph
                .condition_sequences
                .iter(evidence)
                .map(|condition| graph.raise_condition(*condition))
                .collect()
        }
        Proof::Unknown(_) => Vec::new(),
    };
    SubstitutionObservation {
        expression: graph.raise_expr(expression),
        condition: graph.raise_condition(condition),
        guards: graph
            .condition_sequences
            .iter(guards)
            .map(|condition| graph.raise_condition(*condition))
            .collect(),
        truth,
        evidence,
    }
}

#[hegel::test(print_blob = true)]
fn projected_substitutions_match_fresh_full_context_recomputation(tc: hegel::TestCase) {
    let Substitutions {
        shape,
        presence,
        scope,
        value,
        guard,
        noise,
    } = tc.draw(hegel::generators::default::<Substitutions>());
    let value = u128::from(value);
    let guard = u128::from(guard);
    let other_scope = match scope {
        SubstitutionScope::Preserve => SubstitutionScope::Forget,
        SubstitutionScope::Forget => SubstitutionScope::Preserve,
    };
    let contexts = std::iter::once((scope, value, guard, 0))
        .chain(
            noise
                .into_iter()
                .map(|noise| (scope, value, guard, u128::from(noise))),
        )
        .chain([
            (scope, value + 1, guard, 0),
            (scope, value, guard + 1, 0),
            (other_scope, value, guard, 0),
            (scope, value, guard, 0),
        ]);
    with_graph(|mut reused| {
        for (scope, value, guard, noise) in contexts {
            let actual =
                substitution_observation(&mut reused, shape, presence, scope, value, guard, noise);
            // A fresh graph recomputes from all supplied arguments without prior rewrite entries.
            let expected = with_graph(|mut fresh| {
                substitution_observation(&mut fresh, shape, presence, scope, value, guard, noise)
            });
            assert_eq!(actual, expected);
        }
    });
}

#[test]
fn nested_permutations_transfer_used_inputs_to_the_callers_positions() {
    let source = r#"
fn leaf(index: usize, data: &[u8], _first: usize, _second: usize) -> u8 { data[index] }
fn permuted(first: usize, second: usize, data: &[u8], index: usize) -> u8 {
    leaf(index, data, first, second)
}
fn outer(data: &[u8], index: usize, noise: usize) -> u8 { permuted(noise, 0, data, index) }
pub fn root(data: &[u8], noise: usize) -> Option<(u8, u8)> {
    if 0 < data.len() {
        Some((outer(data, 0, noise), outer(data, 1, noise + 1)))
    } else { None }
}
"#;
    let (_, findings) = analyze(source);
    let bounds = bounds_after_argument_evaluation(source, &findings);
    assert_eq!(bounds.item, "root");
    assert_eq!(bounds.primary.message, "1 < data.len()");
    assert_eq!(
        bounds.related[0].label.message,
        "check originates in `leaf`"
    );
    let span = bounds.primary.span;
    assert_eq!(
        &source[std::ops::Range::<usize>::from(span)],
        "outer(data, 1, noise + 1)"
    );
}

#[test]
fn nested_permutations_transfer_guard_inputs_to_the_callers_positions() {
    let source = r#"
fn leaf(gate: usize, data: &[u8], index: usize) -> u8 {
    if gate == 0 { data[index] } else { 0 }
}
fn permuted(_noise: usize, data: &[u8], index: usize, gate: usize) -> u8 {
    leaf(gate, data, index)
}
fn outer(data: &[u8], index: usize, gate: usize, noise: usize) -> u8 {
    permuted(noise, data, index, gate)
}
pub fn root(data: &[u8], index: usize, noise: usize) -> (u8, u8) {
    (outer(data, index, 1, noise), outer(data, index, 0, noise + 1))
}
"#;
    let (_, findings) = analyze(source);
    let bounds = bounds_after_argument_evaluation(source, &findings);
    assert_eq!(bounds.item, "root");
    assert_eq!(bounds.primary.message, "index < data.len()");
    let span = bounds.primary.span;
    assert_eq!(
        &source[std::ops::Range::<usize>::from(span)],
        "outer(data, index, 0, noise + 1)"
    );
}

#[derive(Clone, Copy)]
enum OpaqueCaller {
    Direct,
    Guarded,
}

fn opaque_forwarders(count: usize, caller: OpaqueCaller) -> String {
    let indices = (0..count)
        .map(|index| format!("data[{index}]"))
        .collect::<Vec<_>>()
        .join(", ");
    let mut source = format!(
        "fn leaf(data: &[u8], _noise: usize, _gate: bool) -> [u8; {count}] {{ let data = std::hint::black_box(data); [{indices}] }}\n"
    );
    let mut callee = String::from("leaf");
    for index in 0..count {
        let name = format!("stage_{index}");
        let body = match caller {
            OpaqueCaller::Direct => format!("{callee}(data, {index}, gate)"),
            OpaqueCaller::Guarded => {
                format!("if gate {{ {callee}(data, {index}, gate) }} else {{ [0; {count}] }}")
            }
        };
        writeln!(
            source,
            "fn {name}(data: &[u8], _noise: usize, gate: bool) -> [u8; {count}] {{ {body} }}"
        )
        .expect("opaque forwarder");
        callee = name;
    }
    writeln!(source, "pub fn root(data: &[u8], noise: usize, gate: bool) -> [u8; {count}] {{ {callee}(data, noise, gate) }}").expect("opaque root");
    source
}

#[test]
fn opaque_requirements_share_symbolic_applicability_before_proof() {
    let source = opaque_forwarders(8, OpaqueCaller::Direct);
    let (work, findings) = analyze(&source);
    eprintln!("opaque fallback work: {work:?}");
    assert_eq!(findings.len(), 8, "{findings:?}");
    assert!(
        work.sharing_unknown_rejections > 0,
        "fixture must exercise contextual dependencies: {work:?}"
    );
    assert_eq!(work.sharing_proof_queries, 0, "{work:?}");
    assert!(work.applicability_first_visits > 0, "{work:?}");
    for finding in findings {
        assert_eq!(finding.item, "root");
        assert_eq!(
            finding.related[0].label.message,
            "check originates in `leaf`"
        );
    }
}

#[test]
fn guarded_opaque_requirements_retain_their_obligations() {
    let source = opaque_forwarders(8, OpaqueCaller::Guarded);
    let (work, findings) = analyze(&source);
    eprintln!("opaque fallback work: {work:?}");
    assert_eq!(findings.len(), 8, "{findings:?}");
    assert!(work.sharing_unknown_rejections > 0, "{work:?}");
    assert_eq!(work.sharing_proof_queries, 0, "{work:?}");
    assert!(work.applicability_first_visits > 0, "{work:?}");
}

#[test]
fn opaque_fallback_dependency_metadata_tracks_unique_nodes_not_transform_contexts() {
    let observations = [8, 16, 32].map(|count| {
        let (work, findings) = analyze(&opaque_forwarders(count, OpaqueCaller::Direct));
        assert_eq!(findings.len(), count, "{findings:?}");
        eprintln!("opaque dependency metadata {count}: {work:?}");
        work
    });
    let [small, medium, large] = observations;
    assert!(
        large.requirement_input_entries - medium.requirement_input_entries
            <= 2 * (medium.requirement_input_entries - small.requirement_input_entries),
        "dependency metadata belongs to immutable requirement IDs: {observations:?}"
    );
    assert!(
        large.plan_input_entries - medium.plan_input_entries
            <= 2 * (medium.plan_input_entries - small.plan_input_entries),
        "dependency metadata belongs to immutable plan IDs: {observations:?}"
    );
    assert!(
        large.plan_sequence_input_entries - medium.plan_sequence_input_entries
            <= 2 * (medium.plan_sequence_input_entries - small.plan_sequence_input_entries),
        "unknown fallback contexts must not duplicate sequence dependency metadata: {observations:?}"
    );
}

#[test]
fn opaque_forwarders_reuse_transformations_across_unused_arguments() {
    let observations = [8, 16, 32].map(|count| {
        let (work, findings) = analyze(&opaque_forwarders(count, OpaqueCaller::Direct));
        assert_eq!(findings.len(), count, "{findings:?}");
        assert_eq!(work.sharing_proof_queries, 0, "{work:?}");
        eprintln!("opaque substitution {count}: {work:?}");
        work
    });
    let [small, medium, large] = observations;
    assert!(
        large.requirement_transformations - medium.requirement_transformations
            <= 2 * (medium.requirement_transformations - small.requirement_transformations),
        "unused arguments must not multiply transformations: {observations:?}"
    );
    assert!(
        large.requirement_visits - medium.requirement_visits
            <= 2 * (medium.requirement_visits - small.requirement_visits),
        "unused arguments must not multiply plan work: {observations:?}"
    );
}

#[test]
fn guarded_opaque_forwarders_reuse_transformations_across_unused_arguments() {
    let observations = [8, 16, 32].map(|count| {
        let (work, findings) = analyze(&opaque_forwarders(count, OpaqueCaller::Guarded));
        assert_eq!(findings.len(), count, "{findings:?}");
        assert_eq!(work.sharing_proof_queries, 0, "{work:?}");
        eprintln!("guarded opaque substitution {count}: {work:?}");
        work
    });
    let [small, medium, large] = observations;
    assert!(
        large.requirement_transformations - medium.requirement_transformations
            <= 2 * (medium.requirement_transformations - small.requirement_transformations),
        "unused arguments must not multiply guarded transformations: {observations:?}"
    );
    assert!(
        large.requirement_visits - medium.requirement_visits
            <= 2 * (medium.requirement_visits - small.requirement_visits),
        "unused arguments must not multiply guarded plan work: {observations:?}"
    );
}

#[test]
fn an_early_unknown_dependency_skips_the_irrelevant_suffix() {
    use shapelint_driver::contracts::Order;
    use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, NodeId};

    let observations = [8, 16, 32].map(|depth| with_graph(|mut graph| {
        let unknown = graph.intern_expr(ExprNode::Unknown).unwrap();
        let mut suffix = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        for _ in 0..depth {
            suffix = graph.intern_expr(ExprNode::Length(suffix)).unwrap();
        }
        let condition = graph.intern_condition(ConditionNode::Compare(Order::Less, unknown, suffix)).unwrap();
        match graph.inputs(NodeId::Condition(condition)).unwrap() {
            None => {}
            Some(inputs) => panic!("unknown child must retain full-context fallback: {inputs:?}"),
        }
        let visits = graph.substitution_work.input_visits;
        let Some(inputs) = graph.inputs(NodeId::Expr(suffix)).unwrap() else {
            panic!("the independent suffix uses exactly argument zero");
        };
        assert_eq!(inputs.into_iter().collect::<Vec<_>>(), [0]);
        let suffix_visits = graph.substitution_work.input_visits - visits;
        let before_cached = graph.substitution_work.input_visits;
        match graph.inputs(NodeId::Condition(condition)).unwrap() {
            None => {}
            Some(inputs) => panic!("cached unknown dependency changed: {inputs:?}"),
        }
        let cached_visits = graph.substitution_work.input_visits - before_cached;
        eprintln!("early unknown depth {depth}: discovery {visits}, suffix discovery {suffix_visits}, cached root {cached_visits}");
        assert!(suffix_visits >= depth + 1, "each suffix node must remain undiscovered until requested");
        assert_eq!(cached_visits, 0, "root cache hit performs no discovery");
        visits
    }));
    assert_eq!(observations[0], observations[1], "{observations:?}");
    assert_eq!(observations[1], observations[2], "{observations:?}");
}

#[test]
fn exported_reporting_reuses_summary_resolution() {
    let source = unused_argument(8, Noise::Identity)
        .replace("fn ", "pub fn ")
        .replace("pub pub fn ", "pub fn ");
    let (work, findings) = analyze(&source);
    eprintln!("exported reporting work: {work:?}");
    assert_eq!(findings.len(), 8 * (8 + 2), "{findings:?}");
    assert_eq!(
        work.reporting_classifications, 0,
        "all bodies are exported: {work:?}"
    );
    assert_eq!(
        work.reporting_plan_visits, 0,
        "an exported report requires the already-resolved summary rather than another demand traversal: {work:?}"
    );
}

#[hegel::test(print_blob = true)]
fn irrelevant_arguments_reuse_opaque_substitutions(tc: hegel::TestCase) {
    let Substitutions {
        shape,
        presence,
        scope,
        value,
        guard,
        noise,
    } = tc.draw(hegel::generators::default::<Substitutions>());
    with_graph(|mut graph| {
        let expected = substitution_observation(
            &mut graph,
            shape,
            presence,
            scope,
            u128::from(value),
            u128::from(guard),
            0,
        );
        for noise in noise {
            let before = graph.substitution_work.rewritten_nodes;
            let actual = substitution_observation(
                &mut graph,
                shape,
                presence,
                scope,
                u128::from(value),
                u128::from(guard),
                u128::from(noise),
            );
            assert_eq!(actual, expected);
            assert_eq!(
                graph.substitution_work.rewritten_nodes, before,
                "an unused argument caused another rewrite for {shape:?}"
            );
        }
    });
}

#[derive(Debug, hegel::DefaultGenerator)]
enum DependencyOrder {
    ValueFirst,
    SubstitutionFirst,
}

#[hegel::test(print_blob = true)]
fn substitution_dependencies_do_not_make_an_opaque_value_known(tc: hegel::TestCase) {
    use shapelint_driver::contracts::Invocation;
    use shapelint_driver::contracts::graph::{ExprNode, NodeId};
    let order = tc.draw(hegel::generators::default::<DependencyOrder>());
    with_graph(|mut graph| {
        let argument = graph.intern_expr(ExprNode::Argument(0)).unwrap();
        let zero = graph.intern_expr(ExprNode::Number(0)).unwrap();
        let slice = graph
            .intern_expr(ExprNode::Slice {
                text: argument,
                start: zero,
                end: zero,
            })
            .unwrap();
        let arguments = graph.expression_sequences.from_iter([zero]).unwrap();
        match order {
            DependencyOrder::ValueFirst => {
                assert_eq!(graph.inputs(NodeId::Expr(slice)).unwrap(), None)
            }
            DependencyOrder::SubstitutionFirst => {}
        }
        let substituted = graph
            .substitute_expr(slice, &arguments, &Invocation::LOCAL)
            .unwrap();
        let expected = graph
            .intern_expr(ExprNode::Slice {
                text: zero,
                start: zero,
                end: zero,
            })
            .unwrap();
        assert_eq!(substituted, expected);
        assert_eq!(graph.inputs(NodeId::Expr(slice)).unwrap(), None);
        let before = graph.substitution_work.rewritten_nodes;
        assert_eq!(
            graph
                .substitute_expr(slice, &arguments, &Invocation::LOCAL)
                .unwrap(),
            expected
        );
        assert_eq!(graph.substitution_work.rewritten_nodes, before);
    });
}

// shapelint: allow(literal-test-cases) These counters compare growth across one geometric fixture family.
#[test]
fn opaque_diamond_reports_one_root_requirement_at_each_depth() {
    let mut prior: Vec<contracts::Work> = Vec::new();
    let observations = [4, 8, 12, 16, 32].map(|depth| {
        let flags = format!(
            "({})",
            std::iter::repeat_n("bool", depth)
                .collect::<Vec<_>>()
                .join(", ")
        );
        let source = diamond(depth).replace(&flags, "Flags").replacen(
            "{ data[index] }",
            "{ let data = std::hint::black_box(data); data[index] }",
            1,
        );
        let source = format!("type Flags = {flags};\n{source}");
        let sourcebytes = source.len();
        let (work, findings) = analyze(&source);
        assert_eq!(findings.len(), 1, "depth {depth}: {findings:?}");
        let finding = &findings[0];
        assert_eq!(finding.item, "root");
        assert_eq!(finding.rule, "unproven-precondition");
        assert_eq!(finding.primary.message, "index < data.len()");
        assert_eq!(finding.related.len(), 1);
        assert_eq!(
            finding.related[0].label.message,
            "check originates in `leaf`"
        );
        eprintln!(
            "opaque diamond depth {depth}: transforms={} plans={} reqnodes={} sourcebytes={sourcebytes} work={work:?}",
            work.requirement_transformations, work.requirement_visits, work.requirement_nodes,
        );
        if let [.., before, previous] = prior.as_slice() {
            assert!(
                work.reporting_materializations - previous.reporting_materializations
                    <= 4 * (previous.reporting_materializations - before.reporting_materializations),
                "opaque reporting expanded before depth {depth}: previous={previous:?}, current={work:?}",
            );
        }
        prior.push(work);
        work
    });
    let metrics = [
        (
            "requirement_visits",
            observations.map(|work| work.requirement_visits),
        ),
        (
            "requirement_transformations",
            observations.map(|work| work.requirement_transformations),
        ),
        (
            "requirement_nodes",
            observations.map(|work| work.requirement_nodes),
        ),
        (
            "applicability_nodes",
            observations.map(|work| work.applicability_nodes),
        ),
        (
            "applicability_visits",
            observations.map(|work| work.applicability_visits),
        ),
        (
            "requirement_join_visits",
            observations.map(|work| work.requirement_join_visits),
        ),
        (
            "reporting_visits",
            observations.map(|work| work.reporting_visits),
        ),
        (
            "reporting_classifications",
            observations.map(|work| work.reporting_classifications),
        ),
        (
            "reporting_plan_visits",
            observations.map(|work| work.reporting_plan_visits),
        ),
        (
            "reporting_materializations",
            observations.map(|work| work.reporting_materializations),
        ),
        (
            "descriptions_rendered",
            observations.map(|work| work.descriptions_rendered),
        ),
        (
            "argument_projection_positions",
            observations.map(|work| work.argument_projection_positions),
        ),
        (
            "rewritten_nodes",
            observations.map(|work| work.rewritten_nodes),
        ),
        (
            "plan_input_visits",
            observations.map(|work| work.plan_input_visits),
        ),
        (
            "sharing_probes",
            observations.map(|work| work.sharing_probes),
        ),
        (
            "applicability_first_visits",
            observations.map(|work| work.applicability_first_visits),
        ),
        (
            "applicability_substitution_entries",
            observations.map(|work| work.applicability_substitution_entries),
        ),
        ("input_visits", observations.map(|work| work.input_visits)),
        (
            "requirement_input_entries",
            observations.map(|work| work.requirement_input_entries),
        ),
        (
            "plan_input_entries",
            observations.map(|work| work.plan_input_entries),
        ),
        (
            "plan_sequence_input_entries",
            observations.map(|work| work.plan_sequence_input_entries),
        ),
        (
            "requirement_plan_cache_entries",
            observations.map(|work| work.requirement_plan_cache_entries),
        ),
        (
            "plan_input_positions",
            observations.map(|work| work.plan_input_positions),
        ),
        (
            "report_support_nodes",
            observations.map(|work| work.report_support_nodes),
        ),
        (
            "report_support_visits",
            observations.map(|work| work.report_support_visits),
        ),
        (
            "report_support_entries",
            observations.map(|work| work.report_support_entries),
        ),
        (
            "report_support_elements",
            observations.map(|work| work.report_support_elements),
        ),
        (
            "report_support_overlap_visits",
            observations.map(|work| work.report_support_overlap_visits),
        ),
        (
            "report_support_retained",
            observations.map(|work| work.report_support_retained),
        ),
        (
            "report_projection_visits",
            observations.map(|work| work.report_projection_visits),
        ),
        (
            "report_projection_guards",
            observations.map(|work| work.report_projection_guards),
        ),
        (
            "report_projection_storage",
            observations.map(|work| work.report_projection_storage),
        ),
    ];
    let depths = [4, 8, 12, 16, 32];
    for (name, counts) in metrics {
        let windows = counts.windows(3).zip(depths.windows(3));
        for (work, depth) in windows {
            assert!(
                (work[2] - work[1]) * (depth[1] - depth[0])
                    <= (work[1] - work[0]) * (depth[2] - depth[1]),
                "{name} must grow at most linearly through depth 32: {counts:?}; {observations:?}",
            );
        }
    }
}

// shapelint: allow(literal-test-cases) One geometric family measures reporting growth independently of timing.
#[test]
fn contextual_diamond_keeps_reporting_work_shared() {
    let mut observations: Vec<(usize, contracts::Work)> = Vec::new();
    for depth in [4, 8, 12, 16, 32] {
        let flags = format!(
            "({})",
            std::iter::repeat_n("bool", depth)
                .collect::<Vec<_>>()
                .join(", ")
        );
        let source = diamond(depth).replace(&flags, "Flags").replacen(
            "{ data[index] }",
            "{ let data = std::hint::black_box(data); data[index.wrapping_sub(1)] }",
            1,
        );
        let source = format!("type Flags = {flags};\n{source}");
        let (work, findings) = analyze(&source);
        assert_eq!(findings.len(), 1, "depth {depth}: {findings:?}");
        let finding = &findings[0];
        assert_eq!(finding.item, "root");
        assert_eq!(finding.rule, "unproven-precondition");
        assert_eq!(
            finding.primary.message,
            "index.wrapping_sub(1) < data.len()"
        );
        assert_eq!(finding.related.len(), 1);
        assert_eq!(
            finding.related[0].label.message,
            "check originates in `leaf`"
        );
        let span = finding.related[0].label.span;
        assert_eq!(
            &source[std::ops::Range::<usize>::from(span)],
            "data[index.wrapping_sub(1)]"
        );
        eprintln!(
            "contextual diamond depth {depth}: sourcebytes={} work={work:?}",
            source.len()
        );
        if let [.., (before_depth, before), (previous_depth, previous)] = observations.as_slice() {
            let metrics = [
                (
                    "report visits",
                    before.reporting_visits,
                    previous.reporting_visits,
                    work.reporting_visits,
                ),
                (
                    "materializations",
                    before.reporting_materializations,
                    previous.reporting_materializations,
                    work.reporting_materializations,
                ),
                (
                    "applicability visits",
                    before.applicability_visits,
                    previous.applicability_visits,
                    work.applicability_visits,
                ),
                (
                    "requirement nodes",
                    before.requirement_nodes,
                    previous.requirement_nodes,
                    work.requirement_nodes,
                ),
                (
                    "applicability nodes",
                    before.applicability_nodes,
                    previous.applicability_nodes,
                    work.applicability_nodes,
                ),
                (
                    "plan visits",
                    before.requirement_visits,
                    previous.requirement_visits,
                    work.requirement_visits,
                ),
                (
                    "input visits",
                    before.input_visits,
                    previous.input_visits,
                    work.input_visits,
                ),
                (
                    "plan cache",
                    before.requirement_plan_cache_entries,
                    previous.requirement_plan_cache_entries,
                    work.requirement_plan_cache_entries,
                ),
                (
                    "report_support_nodes",
                    before.report_support_nodes,
                    previous.report_support_nodes,
                    work.report_support_nodes,
                ),
                (
                    "report_support_visits",
                    before.report_support_visits,
                    previous.report_support_visits,
                    work.report_support_visits,
                ),
                (
                    "report_support_entries",
                    before.report_support_entries,
                    previous.report_support_entries,
                    work.report_support_entries,
                ),
                (
                    "report_support_elements",
                    before.report_support_elements,
                    previous.report_support_elements,
                    work.report_support_elements,
                ),
                (
                    "report_support_overlap_visits",
                    before.report_support_overlap_visits,
                    previous.report_support_overlap_visits,
                    work.report_support_overlap_visits,
                ),
                (
                    "report_support_retained",
                    before.report_support_retained,
                    previous.report_support_retained,
                    work.report_support_retained,
                ),
                (
                    "report_projection_visits",
                    before.report_projection_visits,
                    previous.report_projection_visits,
                    work.report_projection_visits,
                ),
                (
                    "report_projection_guards",
                    before.report_projection_guards,
                    previous.report_projection_guards,
                    work.report_projection_guards,
                ),
                (
                    "report_projection_storage",
                    before.report_projection_storage,
                    previous.report_projection_storage,
                    work.report_projection_storage,
                ),
            ];
            for (name, before, previous, current) in metrics {
                assert!(
                    4 * current.saturating_sub(previous) * (previous_depth - before_depth)
                        <= 5 * previous.saturating_sub(before) * (depth - previous_depth),
                    "{name} expands at depth {depth}: {before} -> {previous} -> {current}"
                );
            }
        }
        observations.push((depth, work));
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ReportingOperation {
    WrappingSubtraction,
    Subtraction,
    Selection,
    Range,
    Element,
    Field,
    LocalCall,
}

#[hegel::test]
fn irrelevant_forwarding_diamonds_preserve_contextual_report_outcomes(tc: hegel::TestCase) {
    let operation = tc.draw(hegel::generators::default::<ReportingOperation>());
    let (declarations, body) = match operation {
        ReportingOperation::WrappingSubtraction => ("", "data[index.wrapping_sub(1)]"),
        ReportingOperation::Subtraction => ("", "data[index - 1]"),
        ReportingOperation::Selection => (
            "",
            "let selected = if index > 0 { index } else { 0 }; data[selected]",
        ),
        ReportingOperation::Range => ("", "data[index..][0]"),
        ReportingOperation::Element => ("", "data[data[index] as usize]"),
        ReportingOperation::Field => (
            "struct Slot { index: usize }",
            "let slot = std::hint::black_box(Slot { index }); data[slot.index]",
        ),
        ReportingOperation::LocalCall => (
            "fn choose(index: usize, flag: bool) -> usize { if flag { index } else { 0 } }",
            "data[choose(index, index > 0)]",
        ),
    };
    let leaf = format!(
        "{declarations}\ntype Flags = (bool, bool);\nfn leaf(data: &[u8], index: usize, _flags: Flags) -> u8 {{ let data = std::hint::black_box(data); {body} }}"
    );
    let direct = format!(
        "{leaf}\npub fn root(data: &[u8], index: usize, flags: Flags) -> u8 {{ leaf(data, index, flags) }}"
    );
    let diamond = format!(
        "{leaf}\nfn stage(data: &[u8], index: usize, flags: Flags) -> u8 {{ if flags.0 {{ leaf(data, index, flags) }} else {{ leaf(data, index, flags) }} }}\nfn outer(data: &[u8], index: usize, flags: Flags) -> u8 {{ if flags.1 {{ stage(data, index, flags) }} else {{ stage(data, index, flags) }} }}\npub fn root(data: &[u8], index: usize, flags: Flags) -> u8 {{ outer(data, index, flags) }}"
    );
    let (_, direct) = analyze(&direct);
    let (_, diamond) = analyze(&diamond);
    let mut expected: Vec<_> = direct
        .into_iter()
        .filter(|finding| finding.item == "root")
        .map(|finding| (finding.rule, finding.primary.message))
        .collect();
    let mut actual: Vec<_> = diamond
        .into_iter()
        .filter(|finding| finding.item == "root")
        .map(|finding| (finding.rule, finding.primary.message))
        .collect();
    expected.sort();
    actual.sort();
    assert_eq!(actual, expected, "{operation:?}");
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum ReportingBranchOrder {
    SafeFirst,
    UnsafeFirst,
}

#[hegel::test]
fn report_projection_preserves_transitive_guard_relationships(tc: hegel::TestCase) {
    let order = tc.draw(hegel::generators::default::<ReportingBranchOrder>());
    let branches = match order {
        ReportingBranchOrder::SafeFirst => {
            "if flag { if y == 0 { leaf(x) } else { 0 } } else { if y > 0 { leaf(x) } else { 0 } }"
        }
        ReportingBranchOrder::UnsafeFirst => {
            "if flag { if y > 0 { leaf(x) } else { 0 } } else { if y == 0 { leaf(x) } else { 0 } }"
        }
    };
    let source = format!(
        "fn leaf(x: usize) -> u8 {{ [42][x] }}\nfn stage(x: usize, y: usize, flag: bool) -> u8 {{ if x == y {{ {branches} }} else {{ 0 }} }}\npub fn root(x: usize, y: usize, flag: bool) -> u8 {{ stage(x, y, flag) }}"
    );
    let (_, findings) = analyze(&source);
    let obligations: Vec<_> = findings
        .iter()
        .filter(|finding| finding.item == "root")
        .collect();
    assert!(
        !obligations.is_empty(),
        "{order:?}: positive y reaches the one-element index: {findings:?}"
    );
}

// shapelint: allow(literal-test-cases) Each generated operation crosses the same geometric branch-depth family.
#[hegel::test]
fn contextual_operations_keep_irrelevant_branch_work_bounded(tc: hegel::TestCase) {
    let operation = tc.draw(hegel::generators::default::<ReportingOperation>());
    let (declarations, body) = match operation {
        ReportingOperation::WrappingSubtraction => ("", "data[index.wrapping_sub(1)]"),
        ReportingOperation::Subtraction => ("", "data[index - 1]"),
        ReportingOperation::Selection => (
            "",
            "let selected = if index > 0 { index } else { 0 }; data[selected]",
        ),
        ReportingOperation::Range => ("", "data[index..][0]"),
        ReportingOperation::Element => ("", "data[data[index] as usize]"),
        ReportingOperation::Field => (
            "struct Slot { index: usize }",
            "let slot = std::hint::black_box(Slot { index }); data[slot.index]",
        ),
        ReportingOperation::LocalCall => (
            "fn choose(index: usize, flag: bool) -> usize { if flag { index } else { 0 } }",
            "data[choose(index, index > 0)]",
        ),
    };
    let mut observations: Vec<(usize, contracts::Work)> = Vec::new();
    let mut expected = None;
    for depth in [4, 8, 12, 16, 32] {
        let flags = format!(
            "({})",
            std::iter::repeat_n("bool", depth)
                .collect::<Vec<_>>()
                .join(", ")
        );
        let source = diamond(depth).replace(&flags, "Flags").replacen(
            "{ data[index] }",
            &format!("{{ let data = std::hint::black_box(data); {body} }}"),
            1,
        );
        let source = format!("{declarations}\ntype Flags = {flags};\n{source}");
        let (work, findings) = analyze(&source);
        let mut outcomes: Vec<_> = findings
            .into_iter()
            .filter(|finding| finding.item == "root")
            .map(|finding| (finding.rule, finding.primary.message))
            .collect();
        outcomes.sort();
        match &expected {
            None => {
                assert!(
                    !outcomes.is_empty(),
                    "{operation:?} must retain the unresolved check"
                );
                expected = Some(outcomes);
            }
            Some(expected) => assert_eq!(&outcomes, expected, "{operation:?} at depth {depth}"),
        }
        eprintln!("contextual {operation:?} diamond depth {depth}: work={work:?}");
        if let [.., (before_depth, before), (previous_depth, previous)] = observations.as_slice() {
            let metrics = [
                (
                    "report visits",
                    before.reporting_visits,
                    previous.reporting_visits,
                    work.reporting_visits,
                ),
                (
                    "materializations",
                    before.reporting_materializations,
                    previous.reporting_materializations,
                    work.reporting_materializations,
                ),
                (
                    "applicability visits",
                    before.applicability_visits,
                    previous.applicability_visits,
                    work.applicability_visits,
                ),
                (
                    "requirement nodes",
                    before.requirement_nodes,
                    previous.requirement_nodes,
                    work.requirement_nodes,
                ),
                (
                    "applicability nodes",
                    before.applicability_nodes,
                    previous.applicability_nodes,
                    work.applicability_nodes,
                ),
                (
                    "plan visits",
                    before.requirement_visits,
                    previous.requirement_visits,
                    work.requirement_visits,
                ),
                (
                    "input visits",
                    before.input_visits,
                    previous.input_visits,
                    work.input_visits,
                ),
                (
                    "plan cache",
                    before.requirement_plan_cache_entries,
                    previous.requirement_plan_cache_entries,
                    work.requirement_plan_cache_entries,
                ),
                (
                    "report_support_nodes",
                    before.report_support_nodes,
                    previous.report_support_nodes,
                    work.report_support_nodes,
                ),
                (
                    "report_support_visits",
                    before.report_support_visits,
                    previous.report_support_visits,
                    work.report_support_visits,
                ),
                (
                    "report_support_entries",
                    before.report_support_entries,
                    previous.report_support_entries,
                    work.report_support_entries,
                ),
                (
                    "report_support_elements",
                    before.report_support_elements,
                    previous.report_support_elements,
                    work.report_support_elements,
                ),
                (
                    "report_support_overlap_visits",
                    before.report_support_overlap_visits,
                    previous.report_support_overlap_visits,
                    work.report_support_overlap_visits,
                ),
                (
                    "report_support_retained",
                    before.report_support_retained,
                    previous.report_support_retained,
                    work.report_support_retained,
                ),
                (
                    "report_projection_visits",
                    before.report_projection_visits,
                    previous.report_projection_visits,
                    work.report_projection_visits,
                ),
                (
                    "report_projection_guards",
                    before.report_projection_guards,
                    previous.report_projection_guards,
                    work.report_projection_guards,
                ),
                (
                    "report_projection_storage",
                    before.report_projection_storage,
                    previous.report_projection_storage,
                    work.report_projection_storage,
                ),
            ];
            for (name, before, previous, current) in metrics {
                assert!(
                    4 * current.saturating_sub(previous) * (previous_depth - before_depth)
                        <= 5 * previous.saturating_sub(before) * (depth - previous_depth),
                    "{name} expands at depth {depth}: {before} -> {previous} -> {current}"
                );
            }
        }
        observations.push((depth, work));
    }
}
