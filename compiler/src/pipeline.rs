pub mod artifacts;
pub mod report;

use crate::analysis::Analysis;
use crate::callers::CallIndex;
use crate::contracts::graph::{CapacityError, Graph};
use crate::pipeline::report::evaluator::{Evaluator, ReportDemand, RequirementReport};

pub struct Summaries<'g> {
    pub definitions: rustc_data_structures::fx::FxHashMap<
        rustc_hir::def_id::DefId,
        crate::contracts::summaries::SummaryId<'g>,
    >,
    pub coverage: rustc_data_structures::fx::FxHashSet<rustc_hir::def_id::CrateNum>,
}

impl<'g> Summaries<'g> {
    pub fn link(analyses: Vec<Analysis<'g>>, imported: artifacts::Imported<'g>) -> Self {
        let mut summaries = Self::from(imported);
        summaries.definitions.extend(
            analyses
                .into_iter()
                .map(|analysis| (analysis.def.to_def_id(), analysis.contracts)),
        );
        summaries
    }
}

pub fn evaluate_crate<'g>(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    graph: &mut Graph<'g>,
    summaries: &Summaries<'g>,
) -> Result<crate::contracts::Work, CapacityError> {
    let definitions = &summaries.definitions;
    let calls = CallIndex::try_new(tcx, definitions, graph)?;
    let mut ordered: Vec<_> = definitions.iter().map(|(&def, &id)| (def, id)).collect();
    ordered.sort_by_cached_key(|&(def, _)| (tcx.def_span(def).lo(), tcx.def_path_hash(def)));
    let mut evaluator = Evaluator::try_new(tcx, &ordered, graph, &calls)?;
    for &(def, _) in &ordered {
        for (span, mut cursor) in
            evaluator.resolve_requirements(def, ReportDemand::LocalFindings)?
        {
            while let Some(requirement) = evaluator.next_requirement(&mut cursor)? {
                if let RequirementReport::Pending(id) = requirement {
                    evaluator.report_requirement(&mut cursor, id, span)?;
                }
            }
        }
    }
    Ok(evaluator.finish_work())
}

pub struct SourceFindings {
    pub input: shapelint::SourceInput,
    pub findings: Vec<shapelint::Finding>,
}

impl SourceFindings {
    pub fn collect(
        tcx: rustc_middle::ty::TyCtxt<'_>,
        source_inputs: &crate::diagnostics::Sources,
        config: &shapelint::Config,
    ) -> Result<Vec<Self>, shapelint::LintError> {
        let map = tcx.sess.source_map();
        let mut spans: Vec<_> = tcx
            .iter_local_def_id()
            .map(|def| tcx.def_span(def))
            .collect();
        tcx.hir_for_each_module(|module| {
            spans.push(tcx.hir_get_module(module).0.spans.inner_span);
        });
        let mut files = rustc_data_structures::fx::FxIndexMap::default();
        for span in spans {
            if span.is_dummy() {
                continue;
            }
            let file = map.lookup_source_file(span.lo());
            if file.is_imported() {
                continue;
            }
            let name = file.name.prefer_local_unconditionally().to_string();
            if let Some(shapelint::Language::Rust) = shapelint::Language::of(&name) {
                files.entry(file.start_pos).or_insert(file);
            }
        }
        let inputs = files
            .into_values()
            .map(|file| source_inputs.input(file.as_ref()))
            .collect::<Result<Vec<_>, _>>()?;
        let findings = shapelint::lint_sources(&inputs, config)?;
        Ok(inputs
            .into_iter()
            .zip(findings)
            .map(|(input, findings)| Self { input, findings })
            .collect())
    }
}
