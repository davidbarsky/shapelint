#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use rustc_middle::ty::TyCtxt;
use shapelint_driver::contracts::graph::with_graph;
use shapelint_driver::{analysis, artifacts, callers, contracts, diagnostics, pipeline};
use std::fmt::Write;

fn analyze(text: &str) -> (contracts::Work, Vec<shapelint::Finding>) {
    #[derive(Default)]
    struct Capture(Option<(contracts::Work, Vec<shapelint::Finding>)>);

    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            self.0 = Some(with_graph(|mut graph| {
                let sources = diagnostics::Sources::default();
                let analyses: Vec<_> = tcx
                    .hir_body_owners()
                    .map(|def| {
                        let body = tcx.mir_promoted(def).0.borrow();
                        analysis::analyze(tcx, def, &body, &mut graph, &[], &sources)
                            .expect("MIR analysis")
                    })
                    .collect();
                let imported = artifacts::Inputs::default()
                    .import(tcx, &mut graph)
                    .expect("empty imports");
                let analyzed = pipeline::Collected::from(analyses)
                    .link(imported)
                    .analyze(
                        tcx,
                        &mut graph,
                        callers::Scope::Library,
                        shapelint_driver::pipeline::AnalysisGaps::Show,
                        &shapelint::Config::default(),
                        &sources,
                    )
                    .expect("linked analysis");
                let work = analyzed.work;
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
                (work, findings)
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
        "--crate-name=shapelint_applicability_membership".into(),
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
    callback.0.expect("analysis callback ran")
}

#[test]
fn exact_guard_membership_preserves_diagnostic_order() {
    let source = "pub fn guarded(data: &[u8], index: usize) -> u8 {\n\
         if index < data.len() { data[index] } else { 0 }\n\
     }\n\
     pub fn first(data: &[u8], index: usize) -> u8 { data[index] }\n\
     pub fn second(data: &[u8], index: usize) -> u8 { data[index] }\n";
    let (_, findings) = analyze(source);
    assert_eq!(findings.len(), 2, "the guarded access is safe");
    assert_eq!(findings[0].item, "first");
    assert_eq!(findings[1].item, "second");
}

#[test]
fn caller_exact_guard_discharges_a_callee_requirement() {
    let source = "fn leaf(data: &[u8], index: usize) -> u8 { data[index] }\n\
         pub fn root(data: &[u8], index: usize) -> u8 {\n\
             if index < data.len() { leaf(data, index) } else { 0 }\n\
         }\n";
    let (_, findings) = analyze(source);
    assert!(
        findings.is_empty(),
        "the caller's exact guard proves the access: {findings:?}"
    );
}

#[test]
fn known_caller_flag_resolves_a_selected_index_without_reordering_findings() {
    let text = "fn choose(data: &[u8], index: usize, flag: bool) -> u8 {\n\
             let selected = if flag { 0 } else { index };\n\
             data[selected]\n\
         }\n\
         pub fn first(data: &[u8], index: usize) -> u8 {\n\
             if 0 < data.len() { choose(data, index, true) } else { 0 }\n\
         }\n\
         pub fn second(data: &[u8], index: usize) -> u8 { choose(data, index, false) }\n";
    let (_, findings) = analyze(text);
    assert_eq!(
        findings.len(),
        1,
        "the constant-true caller is safe: {findings:?}"
    );
    assert_eq!(findings[0].item, "second");
    assert_eq!(findings[0].primary.message, "index < data.len()");
}

#[test]
fn returned_guard_survives_two_outer_call_substitutions() {
    let text = "#[derive(Clone, Copy)] pub struct Slot { pub start: usize }\n\
         fn safe(slot: Slot, bound: usize) -> bool { slot.start <= bound }\n\
         fn leaf(slot: Slot, bound: usize) -> usize { bound - slot.start }\n\
         fn middle(slot: Slot, bound: usize) -> usize {\n\
             if safe(slot, bound) { leaf(slot, bound) } else { 0 }\n\
         }\n\
         fn outer(slot: Slot, bound: usize) -> usize { middle(slot, bound) }\n\
         pub fn root(slot: Slot, bound: usize) -> usize { outer(slot, bound) }\n\
         pub fn unguarded(slot: Slot, bound: usize) -> usize { leaf(slot, bound) }\n";
    let (_, findings) = analyze(text);
    assert_eq!(
        findings.len(),
        1,
        "only the unguarded call is unsafe: {findings:?}"
    );
    assert_eq!(findings[0].item, "unguarded");
}

fn branching_guards(depth: usize) -> String {
    let fields = (0..depth)
        .map(|index| format!("flags.{index}"))
        .collect::<Vec<_>>();
    let mut source = format!(
        "pub type Flags = ({});\n\
         fn leaf(data: &[u8], index: usize, _flags: Flags) -> u8 {{ data[index] }}\n",
        std::iter::repeat_n("bool", depth)
            .collect::<Vec<_>>()
            .join(", ")
    );
    let mut callee = "leaf".to_owned();
    for index in (0..depth).rev() {
        let name = format!("stage_{index}");
        writeln!(
            source,
            "fn {name}(data: &[u8], index: usize, flags: Flags) -> u8 {{\n\
                 if {} {{ {callee}(data, index, flags) }} else {{ {callee}(data, index, flags) }}\n\
             }}",
            fields[index]
        )
        .expect("fixture source formatting");
        callee = name;
    }
    writeln!(
        source,
        "pub fn root(data: &[u8], index: usize, flags: Flags) -> u8 {{ {callee}(data, index, flags) }}"
    )
    .expect("fixture source formatting");
    source
}

// shapelint: allow(literal-test-cases) Fixed geometric depths compare one applicability family.
#[test]
fn shared_guard_fragments_keep_exact_membership_work_linear() {
    let observations = [4, 8, 16, 32].map(|depth| {
        let source = branching_guards(depth);
        let (work, findings) = analyze(&source);
        assert_eq!(findings.len(), 1, "depth {depth}: {findings:?}");
        assert_eq!(findings[0].item, "root", "depth {depth}");
        assert!(work.applicability_membership_visits > 0, "{work:?}");
        assert!(work.applicability_membership_guard_sequence_visits > 0, "{work:?}");
        assert!(work.applicability_membership_guard_sequence_cache_hits > 0, "{work:?}");
        assert!(work.applicability_membership_guard_leaf_comparisons > 0, "{work:?}");
        assert!(work.applicability_membership_guard_sequence_entries > 0, "{work:?}");
        assert!(work.applicability_membership_entries > 0, "{work:?}");
        assert!(
            work.applicability_membership_guard_leaf_comparisons
                <= work.applicability_membership_guard_sequence_entries,
            "each leaf comparison belongs to a retained fragment: {work:?}"
        );
        eprintln!(
            "applicability membership depth {depth}: visits {}, guard frames {}, cache hits {}, leaf comparisons {}, sequence entries {}, node entries {}",
            work.applicability_membership_visits,
            work.applicability_membership_guard_sequence_visits,
            work.applicability_membership_guard_sequence_cache_hits,
            work.applicability_membership_guard_leaf_comparisons,
            work.applicability_membership_guard_sequence_entries,
            work.applicability_membership_entries,
        );
        (depth, work)
    });
    let visits = observations.map(|(_, work)| work.applicability_membership_visits);
    let sequence_visits =
        observations.map(|(_, work)| work.applicability_membership_guard_sequence_visits);
    let leaf_comparisons =
        observations.map(|(_, work)| work.applicability_membership_guard_leaf_comparisons);
    let entries = observations.map(|(_, work)| work.applicability_membership_entries);
    let sequence_entries =
        observations.map(|(_, work)| work.applicability_membership_guard_sequence_entries);
    for growth in [
        visits,
        sequence_visits,
        leaf_comparisons,
        entries,
        sequence_entries,
    ] {
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
