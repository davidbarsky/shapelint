#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use std::fmt::Write;

use rustc_middle::ty::TyCtxt;
use shapelint_driver::contracts::graph::with_graph;
use shapelint_driver::{analysis, artifacts, callers, contracts, diagnostics, pipeline};

fn analyze(text: &str, gaps: pipeline::AnalysisGaps) -> (contracts::Work, Vec<shapelint::Finding>) {
    let (work, mut findings) = analyze_all(text, gaps);
    findings.retain(|finding| {
        finding.rule == "unproven-precondition"
            || finding.rule == "invalidated-validation"
            || finding.rule == "invalid-state-use"
            || finding.rule == "unencoded-precondition"
    });
    (work, findings)
}

fn analyze_all(
    text: &str,
    gaps: pipeline::AnalysisGaps,
) -> (contracts::Work, Vec<shapelint::Finding>) {
    struct Capture {
        gaps: pipeline::AnalysisGaps,
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
                        self.gaps,
                        &shapelint::Config::default(),
                        &sources,
                    )
                    .expect("linked analysis");
                let findings: &[pipeline::SourceFindings] = analyzed.as_ref();
                let findings = findings
                    .iter()
                    .flat_map(|source| source.findings.iter())
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
        "--crate-name=shapelint_reporting_fallback".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        path.display().to_string(),
    ];
    let mut callback = Capture { gaps, result: None };
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut callback));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
    callback.result.expect("analysis callback ran")
}

#[test]
fn callback_expansions_are_independent_of_closed_sibling_branches() {
    let root = "fn render(value: bool) -> u32 { if value { 1 } else { 0 } }
        fn invoke(f: fn(bool) -> u32) -> u32 { f(false) }
        pub fn root(route: usize) -> u32 { sibling(render, route); invoke(render) }
        fn leaf(_: fn(bool) -> u32, _: usize) {}
        ";
    let analyze_tree = |source: &str| {
        let (work, findings) = analyze_all(source, pipeline::AnalysisGaps::Hide);
        let witnesses: Vec<_> = findings
            .iter()
            .filter(|finding| finding.rule == "unused-capability" && finding.item == "render")
            .collect();
        let [witness] = witnesses.as_slice() else {
            panic!("expected the callback's constant argument finding: {witnesses:?}");
        };
        assert_eq!(witness.primary.message, "`value` is always false");
        assert!(work.caller_expansions > 0);
        let callers: Vec<_> = witness
            .related
            .iter()
            .map(|related| related.label.clone())
            .collect();
        assert!(!callers.is_empty());
        (work.caller_expansions, witness.primary.clone(), callers)
    };
    let [baseline, two_branches, five_branches] = [0, 2, 5].map(|branches| {
        let mut source = root.to_owned();
        for branch in 0..branches {
            writeln!(
                source,
                "fn branch_{branch}(f: fn(bool) -> u32, n: usize) {{ leaf(f, n) }}"
            )
            .unwrap();
        }
        source.push_str("fn sibling(f: fn(bool) -> u32, n: usize) { match n {\n");
        for branch in 0..branches {
            writeln!(source, "{branch} => branch_{branch}(f, n),").unwrap();
        }
        source.push_str("_ => leaf(f, n), } }\n");
        analyze_tree(&source)
    });
    assert_eq!([&two_branches, &five_branches], [&baseline; 2]);
}

fn unknown_guard_diamond(depth: usize) -> String {
    let choices = std::iter::repeat_n("Choice", depth)
        .collect::<Vec<_>>()
        .join(", ");
    let mut source = format!(
        "#[derive(Clone, Copy)] pub enum Choice {{ First, Second, Other }}\n\
         pub type Choices = ({choices});\n\
         fn recursive(data: &[u8], index: usize, choices: Choices) -> u8 {{\n\
             match choices.{} {{\n\
                 Choice::First => data[index],\n\
                 _ => recursive(data, index, choices),\n\
             }}\n\
         }}\n",
        depth - 1
    );
    let mut callee = String::from("recursive");
    for index in (0..depth).rev() {
        let name = format!("stage_{index}");
        writeln!(
            source,
            "fn {name}(data: &[u8], index: usize, choices: Choices) -> u8 {{\n\
                 match choices.{index} {{\n\
                     Choice::First => {callee}(data, index, choices),\n\
                     _ => {callee}(data, index, choices),\n\
                 }}\n\
             }}"
        )
        .expect("stage source");
        callee = name;
    }
    writeln!(
        source,
        "pub fn root(data: &[u8], index: usize, choices: Choices) -> u8 {{ {callee}(data, index, choices) }}"
    )
    .expect("root source");
    source
}

fn exact_field_guard_diamond(depth: usize) -> String {
    let flags = std::iter::repeat_n("bool", depth)
        .collect::<Vec<_>>()
        .join(", ");
    let mut source = format!(
        "#[derive(Clone, Copy)] pub struct Slot {{ pub start: usize }}\n\
         pub type Flags = ({flags});\n\
         fn leaf(slot: Slot, bound: usize) -> usize {{ bound - slot.start }}\n"
    );
    let last = depth - 1;
    let mut callee = format!("stage_{last}");
    writeln!(
        source,
        "fn {callee}(slot: Slot, bound: usize, flags: Flags) -> usize {{\n\
             if flags.{last} {{\n\
                 if slot.start <= bound {{ leaf(slot, bound) }} else {{ leaf(slot, bound) }}\n\
             }} else {{\n\
                 if slot.start <= bound {{ leaf(slot, bound) }} else {{ leaf(slot, bound) }}\n\
             }}\n\
         }}"
    )
    .expect("last stage source");
    for index in (0..last).rev() {
        let name = format!("stage_{index}");
        writeln!(
            source,
            "fn {name}(slot: Slot, bound: usize, flags: Flags) -> usize {{\n\
                 if flags.{index} {{\n\
                     if slot.start <= bound {{ {callee}(slot, bound, flags) }} else {{ {callee}(slot, bound, flags) }}\n\
                 }} else {{\n\
                     if slot.start <= bound {{ {callee}(slot, bound, flags) }} else {{ {callee}(slot, bound, flags) }}\n\
                 }}\n\
             }}"
        )
        .expect("stage source");
        callee = name;
    }
    writeln!(
        source,
        "pub fn root(slot: Slot, bound: usize, flags: Flags) -> usize {{\n\
             let slot = std::hint::black_box(slot);\n\
             let bound = std::hint::black_box(bound);\n\
             {callee}(slot, bound, flags)\n\
         }}"
    )
    .expect("root source");
    source
}

// shapelint: allow(literal-test-cases) Fixed geometric depths compare one fixture family's work growth.
#[test]
fn unknown_guard_diamonds_keep_reporting_work_linear() {
    let observations = [4, 8, 16, 32].map(|depth| {
        let source = unknown_guard_diamond(depth);
        let (work, findings) = analyze(&source, pipeline::AnalysisGaps::Show);
        assert_eq!(findings.len(), 1, "depth {depth}: {findings:?}");
        let finding = &findings[0];
        assert_eq!(finding.rule, "unproven-precondition", "depth {depth}");
        assert_eq!(finding.item, "root", "depth {depth}");
        assert_eq!(
            finding.primary.message, "index < data.len()",
            "depth {depth}"
        );
        let Some(origin) = finding
            .related
            .iter()
            .find(|related| related.label.message == "check originates in `recursive`")
        else {
            panic!("expected the recursive check's origin: {finding:?}");
        };
        assert_eq!(
            &source[std::ops::Range::<usize>::from(origin.label.span)],
            "data[index]"
        );
        eprintln!("unknown guard diamond depth {depth}: {work:?}");
        (work, findings)
    });
    let [small, medium, large, largest] = observations.map(|(work, _)| work);
    let reporting_growth = [
        small.reporting_materializations,
        medium.reporting_materializations,
        large.reporting_materializations,
        largest.reporting_materializations,
    ];
    let applicability_growth = [
        small.applicability_visits,
        medium.applicability_visits,
        large.applicability_visits,
        largest.applicability_visits,
    ];
    for growth in [reporting_growth, applicability_growth] {
        assert!(growth[0] <= growth[1], "{growth:?}");
        assert!(growth[1] <= growth[2], "{growth:?}");
        assert!(growth[2] <= growth[3], "{growth:?}");
        assert!(
            growth[2] - growth[1] <= 2 * (growth[1] - growth[0]),
            "{growth:?}"
        );
        assert!(
            growth[3] - growth[2] <= 2 * (growth[2] - growth[1]),
            "{growth:?}"
        );
    }
}

// shapelint: allow(literal-test-cases) Fixed depths and counters form one linear-work scaling gate.
#[test]
fn exact_opaque_field_guards_keep_reporting_work_linear() {
    let observations = [2, 4, 8].map(|depth| {
        let source = exact_field_guard_diamond(depth);
        let (work, findings) = analyze(&source, pipeline::AnalysisGaps::Show);
        assert_eq!(findings.len(), 1, "depth {depth}: {findings:?}");
        let finding = &findings[0];
        assert_eq!(finding.rule, "unproven-precondition", "depth {depth}");
        assert_eq!(finding.item, "root", "depth {depth}");
        assert_eq!(
            finding.primary.message,
            "requires bound >= slot.start",
            "depth {depth}"
        );
        let Some(origin) = finding
            .related
            .iter()
            .find(|related| related.label.message == "check originates in `leaf`")
        else {
            panic!("expected the leaf check's origin: {finding:?}");
        };
        assert_eq!(
            &source[std::ops::Range::<usize>::from(origin.label.span)],
            "bound - slot.start"
        );
        eprintln!(
            "exact field guard depth {depth}: materializations {}, applicability visits {}, support visits {}, overlap frames {}, projection visits {}, projection storage {}, support entries {}",
            work.reporting_materializations,
            work.applicability_visits,
            work.report_support_visits,
            work.report_support_overlap_visits,
            work.report_projection_visits,
            work.report_projection_storage,
            work.report_support_entries,
        );
        work
    });
    let [small, medium, large] = observations;
    let work_growth = [
        [
            small.reporting_materializations,
            medium.reporting_materializations,
            large.reporting_materializations,
        ],
        [
            small.applicability_visits,
            medium.applicability_visits,
            large.applicability_visits,
        ],
        [
            small.report_support_visits,
            medium.report_support_visits,
            large.report_support_visits,
        ],
        [
            small.report_support_overlap_visits,
            medium.report_support_overlap_visits,
            large.report_support_overlap_visits,
        ],
        [
            small.report_projection_visits,
            medium.report_projection_visits,
            large.report_projection_visits,
        ],
        [
            small.report_projection_storage,
            medium.report_projection_storage,
            large.report_projection_storage,
        ],
        [
            small.report_support_entries,
            medium.report_support_entries,
            large.report_support_entries,
        ],
        [
            small.report_support_retained,
            medium.report_support_retained,
            large.report_support_retained,
        ],
    ];
    for growth in work_growth {
        assert!(growth[0] <= growth[1], "{growth:?}");
        assert!(growth[1] <= growth[2], "{growth:?}");
        assert!(
            growth[2] - growth[1] <= 2 * (growth[1] - growth[0]),
            "{growth:?}"
        );
    }
}

#[test]
fn default_reporting_skips_descriptions_for_unresolved_requirements() {
    let source = unknown_guard_diamond(8);
    let (default_work, findings) = analyze(&source, pipeline::AnalysisGaps::Hide);
    assert!(findings.is_empty());
    assert_eq!(default_work.descriptions_rendered, 0);
    let (coverage_work, gaps) = analyze(&source, pipeline::AnalysisGaps::Show);
    assert_eq!(gaps.len(), 1);
    assert_eq!(gaps[0].kind, shapelint::Kind::AnalysisGap);
    assert_eq!(coverage_work.descriptions_rendered, 1);
}
