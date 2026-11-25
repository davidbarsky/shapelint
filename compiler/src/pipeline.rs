pub mod report;

use crate::analysis::Analysis;
use crate::callers::CallIndex;
use crate::contracts::graph::{CapacityError, Graph};
use crate::pipeline::report::evaluator::{Evaluator, ReportDemand, RequirementReport};

pub fn evaluate_crate<'g>(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    graph: &mut Graph<'g>,
    analyses: Vec<Analysis<'g>>,
) -> Result<crate::contracts::Work, CapacityError> {
    let definitions = analyses
        .into_iter()
        .map(|analysis| (analysis.def.to_def_id(), analysis.contracts))
        .collect();
    let calls = CallIndex::try_new(tcx, &definitions, graph)?;
    let mut ordered: Vec<_> = definitions.into_iter().collect();
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
