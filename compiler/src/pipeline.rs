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
                files.entry(file.start_pos).or_insert((file, Vec::new()));
            }
        }
        for crate::Located {
            def,
            item_span,
            span,
            evidence,
        } in crate::hir_rules::findings(tcx)
            .into_iter()
            .chain(crate::architecture::findings(tcx, source_inputs)?)
        {
            let Some(span) = crate::diagnostics::source_span(tcx, def.to_def_id(), span) else {
                continue;
            };
            let item_span = item_span.source_callsite();
            let file = map.lookup_source_file(span.lo());
            if file.is_imported() {
                continue;
            }
            let item_span = match (file.contains(item_span.lo()), file.contains(item_span.hi())) {
                (true, true) => item_span,
                _ => span,
            };
            let finding = shapelint::CompilerFinding {
                item: crate::diagnostics::item(tcx, def.to_def_id()),
                item_span: shapelint::Span {
                    start: file.original_relative_byte_pos(item_span.lo()).0,
                    end: file.original_relative_byte_pos(item_span.hi()).0,
                },
                span: shapelint::Span {
                    start: file.original_relative_byte_pos(span.lo()).0,
                    end: file.original_relative_byte_pos(span.hi()).0,
                },
                evidence,
            };
            let (_, findings) = files
                .entry(file.start_pos)
                .or_insert_with(|| (file, Vec::new()));
            findings.push(finding);
        }
        let mut inputs = Vec::new();
        let mut evidence = Vec::new();
        for (file, findings) in files.into_values() {
            inputs.push(source_inputs.input(file.as_ref())?);
            evidence.push(findings);
        }
        let findings = shapelint::lint_sources(&inputs, config)?;
        let mut sources = Vec::with_capacity(inputs.len());
        for ((input, evidence), mut findings) in inputs.into_iter().zip(evidence).zip(findings) {
            findings.extend(shapelint::lint_compiler(&input, config, &evidence)?);
            findings.sort_by_key(|finding| finding.primary.span);
            sources.push(Self { input, findings });
        }
        Ok(sources)
    }
}
