use crate::contracts::graph::{CapacityError, ConditionNode};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::LocalDefId;
use shapelint::CompilerEvidence;

use crate::contracts::{Consumer, Operation, Truth};
use crate::pipeline::report::{ReportContext, evaluator::Evaluator};
use crate::{callers, diagnostics, states};

impl<'g> Evaluator<'_, '_, 'g> {
    pub fn boundary_findings(
        &mut self,
        context: &mut ReportContext<'_, '_, 'g>,
        scope: callers::Scope,
    ) -> Result<Vec<(LocalDefId, states::Finding)>, CapacityError> {
        let tcx = context.tcx;
        let summaries = context.summaries;
        let mut findings = Vec::new();
        let mut definitions: Vec<_> = summaries
            .keys()
            .copied()
            .filter(|def| match scope {
                callers::Scope::Library => def.is_local(),
                callers::Scope::Target => true,
            })
            .collect();
        definitions.sort_by_key(|def| tcx.def_span(*def).lo());
        for def in definitions {
            let summary = self.graph[summaries[&def]];
            let Some(local) = def.as_local() else {
                continue;
            };
            let mut checks = self.graph.scan(summary.checks);
            while let Some(check) = checks.next() {
                let guards = self.graph.scan(check.guards).enumerate();
                for (index, guard) in guards {
                    let ConditionNode::Returned(target, _) = &self.graph[guard] else {
                        continue;
                    };
                    let Some(callee) = target.definition(self.graph) else {
                        continue;
                    };
                    let Some(body) = summaries.get(&callee) else {
                        continue;
                    };
                    let body = self.graph[*body];
                    match tcx.def_kind(callee) {
                        DefKind::Fn | DefKind::AssocFn => {}
                        _ => continue,
                    }
                    if !tcx
                        .fn_sig(callee)
                        .instantiate_identity()
                        .skip_binder()
                        .output()
                        .is_unit()
                    {
                        continue;
                    }
                    let one = crate::sequence::Sequences::from_iter(self.graph.as_mut(), [guard])?;
                    let guarantees = self.resolve_guards(&one)?;
                    let condition = self.resolve_condition(check.condition, &guarantees)?;
                    if self.graph.truth(condition, &guarantees)? != Truth::Proven
                        || self
                            .graph
                            .truth(condition, &crate::sequence::Sequence::EMPTY)?
                            == Truth::Proven
                    {
                        continue;
                    }
                    let (remaining, _) = crate::sequence::Sequences::remove(
                        self.graph.as_mut(),
                        check.guards,
                        index,
                    )?
                    .expect("the guard cursor selected an existing occurrence");
                    let remaining = self.resolve_guards(&remaining)?;
                    if self.graph.truth(condition, &remaining)? == Truth::Proven
                        || crate::sequence::Sequences::len(self.graph.as_ref(), body.returns) == 0
                    {
                        continue;
                    }
                    let Some(origin_span) =
                        diagnostics::source_span(tcx, callee, tcx.def_span(callee))
                    else {
                        continue;
                    };
                    let mut origin = Consumer {
                        def: callee,
                        span: origin_span,
                        operation: Operation::Condition,
                    }
                    .source(tcx, context.sources);
                    origin.label.message = format!(
                        "`{}` establishes this on normal return",
                        diagnostics::item(tcx, callee)
                    );
                    findings.push((
                        local,
                        states::Finding {
                            span: check.span,
                            evidence: CompilerEvidence::DiscardedValidation {
                                condition: diagnostics::Condition {
                                    restorer: &context.restorer,
                                    tcx,
                                    def,
                                    condition,
                                    graph: &self.graph,
                                }
                                .to_string(),
                                origin,
                            },
                        },
                    ));
                    break;
                }
            }
        }
        Ok(findings)
    }
}
