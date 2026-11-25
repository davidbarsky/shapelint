use crate::contracts::graph::{CapacityError, ConditionNode, ExprId, ExprNode, Graph, NodeId};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty;
use rustc_span::sym;
use shapelint::CompilerEvidence;
use std::collections::hash_map::Entry;

use crate::contracts::summaries::{BehaviorNode, SummaryId};
use crate::contracts::{Consumer, Operation, Order, Truth, Writes};
use crate::pipeline::report::{ProductionKind, ReportContext, evaluator::Evaluator};
use crate::{diagnostics, states};

impl<'g> Graph<'g> {
    fn variant(&self, root: ExprId<'g>, def: DefId, variant: usize) -> Option<()> {
        let mut pending = vec![root];
        let mut visited = FxHashSet::default();
        while let Some(value) = pending.pop() {
            if !visited.insert(value) {
                continue;
            }
            match &self[value] {
                ExprNode::Variant(owner, actual, _) if *owner == def && *actual == variant => {}
                ExprNode::Select(_, yes, no) => {
                    pending.push(*no);
                    pending.push(*yes);
                }
                _ => return None,
            }
        }
        Some(())
    }
}

fn pure<'g>(
    def: DefId,
    summaries: &FxHashMap<DefId, SummaryId<'g>>,
    purity: &mut FxHashMap<DefId, Option<()>>,
    graph: &Graph<'g>,
) -> Option<()> {
    enum Work {
        Visit(DefId),
        Build(DefId),
    }
    let mut pending = vec![Work::Visit(def)];
    while let Some(work) = pending.pop() {
        match work {
            Work::Visit(def) => {
                if purity.contains_key(&def) {
                    continue;
                }
                purity.insert(def, None);
                let Some(summary) = summaries.get(&def) else {
                    continue;
                };
                let summary = graph[*summary];
                if crate::sequence::Sequences::len(graph.as_ref(), summary.loops) != 0
                    || crate::sequence::Sequences::len(graph.as_ref(), summary.requirements) != 0
                {
                    continue;
                }
                match summary.behavior {
                    BehaviorNode::Pure => {
                        purity.insert(def, Some(()));
                    }
                    BehaviorNode::Unknown => {}
                    BehaviorNode::Calls(calls) => {
                        pending.push(Work::Build(def));
                        pending.extend(graph.members(calls).map(Work::Visit));
                    }
                }
            }
            Work::Build(def) => {
                let BehaviorNode::Calls(calls) = graph[summaries[&def]].behavior else {
                    unreachable!("only calls schedule purity dependencies");
                };
                let result = graph.members(calls).map(|callee| purity[&callee]).collect();
                purity.insert(def, result);
            }
        }
    }
    purity[&def]
}

fn scalar_result(ty: ty::Ty<'_>) -> Option<()> {
    let mut pending = vec![ty];
    while let Some(ty) = pending.pop() {
        match ty.kind() {
            ty::Bool | ty::Uint(_) | ty::Int(_) => {}
            ty::Tuple(fields) => pending.extend(fields.iter()),
            _ => return None,
        }
    }
    Some(())
}

fn cached_variant<'g>(
    graph: &Graph<'g>,
    cache: &mut FxHashMap<(ExprId<'g>, DefId, usize), Option<()>>,
    value: ExprId<'g>,
    owner: DefId,
    variant: usize,
) -> Option<()> {
    if let Some(result) = cache.get(&(value, owner, variant)) {
        return *result;
    }
    let result = graph.variant(value, owner, variant);
    cache.insert((value, owner, variant), result);
    result
}

impl<'g> Evaluator<'_, '_, 'g> {
    pub fn review_findings(
        &mut self,
        context: &mut ReportContext<'_, '_, 'g>,
    ) -> Result<Vec<(LocalDefId, states::Finding)>, CapacityError> {
        let tcx = context.tcx;
        let summaries = context.summaries;
        let mut findings = Vec::new();
        let mut defs: Vec<_> = summaries.keys().copied().collect();
        defs.sort_by_key(|def| tcx.def_span(*def).lo());
        let mut equivalents = FxHashMap::default();
        let mut purity = FxHashMap::default();
        let mut variants = FxHashMap::default();
        for def in defs {
            let Some(local) = def.as_local() else {
                continue;
            };
            match tcx.def_kind(def) {
                DefKind::Fn | DefKind::AssocFn => {}
                _ => continue,
            }
            let summary = self.graph[summaries[&def]];
            let Some(span) = diagnostics::source_span(tcx, def, tcx.def_span(def)) else {
                continue;
            };
            let signature = tcx.fn_sig(def).instantiate_identity().skip_binder();
            let trait_method = tcx
                .trait_of_assoc(def)
                .or_else(|| tcx.trait_impl_of_assoc(def));
            let fallibility = match signature.output().kind() {
                ty::Adt(adt, _) if tcx.is_diagnostic_item(sym::Result, adt.did()) => {
                    match trait_method {
                        None => Some(adt.did()),
                        Some(_) => None,
                    }
                }
                _ => None,
            };
            let equivalent = match scalar_result(signature.output()) {
                Some(()) if tcx.generics_of(def).count() == 0 => {
                    pure(def, summaries, &mut purity, self.graph)
                }
                Some(()) | None => None,
            };
            let mut returns = Vec::new();
            let mut return_guards = crate::sequence::Sequence::EMPTY;
            let return_candidates = match (fallibility, equivalent) {
                (None, None) => crate::sequence::Sequence::EMPTY,
                (Some(_), _) | (_, Some(())) => summary.returns,
            };
            let mut return_candidates = self.graph.scan(return_candidates);
            while let Some(returned) = return_candidates.next() {
                let guards = self.resolve_guards(&returned.guards)?;
                return_guards = self.graph.append(return_guards, guards)?;
                if self
                    .graph
                    .conjunction(&guards, &crate::sequence::Sequence::EMPTY)?
                    == Truth::Refuted
                {
                    continue;
                }
                returns.push(self.resolve_expression(returned.value, &guards)?);
            }
            if let Some(adt) = fallibility
                && !returns.is_empty()
                && returns.iter().all(|value| {
                    cached_variant(self.graph, &mut variants, *value, adt, 0) == Some(())
                })
            {
                findings.push((
                    local,
                    states::Finding {
                        span,
                        evidence: CompilerEvidence::UnnecessaryFallibility,
                    },
                ));
            }
            let mut checks = self.graph.scan(summary.checks);
            while let Some(check) = checks.next() {
                let Some(writes) = &check.loop_writes else {
                    continue;
                };
                let guards = self.resolve_guards(&check.guards)?;
                let condition = self.resolve_condition(check.condition, &guards)?;
                match self.graph.truth(condition, &guards)? {
                    Truth::Proven | Truth::Refuted => continue,
                    Truth::Unknown(_) => {}
                }
                let Some(inputs) = self.graph.inputs(NodeId::Condition(condition))? else {
                    continue;
                };
                if inputs.is_empty() {
                    continue;
                }
                let stable = match writes {
                    Writes::None => Some(()),
                    Writes::Arguments(written) => {
                        match self
                            .graph
                            .members(*written)
                            .find(|index| inputs.contains(index))
                        {
                            None => Some(()),
                            Some(_) => None,
                        }
                    }
                    Writes::Unknown => None,
                };
                if let None = stable {
                    continue;
                }
                if !inputs
                    .iter()
                    .all(|index| match signature.inputs().get(*index) {
                        Some(ty) => ty
                            .peel_refs()
                            .is_freeze(tcx, ty::TypingEnv::post_analysis(tcx, def)),
                        None => false,
                    })
                {
                    continue;
                }
                findings.push((
                    local,
                    states::Finding {
                        span: check.span,
                        evidence: CompilerEvidence::LoopInvariantCheck {
                            condition: diagnostics::Condition {
                                restorer: &context.restorer,
                                tcx,
                                def,
                                condition,
                                graph: &self.graph,
                            }
                            .to_string(),
                        },
                    },
                ));
            }
            if let Some(()) = equivalent
                && let [value] = returns.as_slice()
                && let Some(_) = self.graph.inputs(NodeId::Expr(*value))?
                && self
                    .graph
                    .conjunction(&return_guards, &crate::sequence::Sequence::EMPTY)?
                    == Truth::Proven
            {
                let signature = tcx.erase_and_anonymize_regions(signature);
                match equivalents.entry((signature, *value)) {
                    Entry::Occupied(entry) => {
                        let original_def = *entry.get();
                        let mut original = Consumer {
                            def: original_def,
                            span: tcx.def_span(original_def),
                            operation: Operation::Condition,
                        }
                        .source(tcx, context.sources);
                        original.label.message =
                            "equivalent typed result and modeled effects".into();
                        findings.push((
                            local,
                            states::Finding {
                                span,
                                evidence: CompilerEvidence::EquivalentImplementation { original },
                            },
                        ));
                    }
                    Entry::Vacant(entry) => {
                        entry.insert(def);
                    }
                }
            }
        }
        let mut owners = Vec::new();
        for (&owner, productions) in context.productions {
            if let Some(_) =
                productions
                    .iter()
                    .find(|production| match production.production_kind {
                        ProductionKind::Construction => true,
                        ProductionKind::Return => false,
                    })
            {
                owners.push(owner);
            }
        }
        owners.sort_by_key(|owner| (tcx.def_span(*owner).lo(), owner.index));
        for owner in owners {
            let Some(local) = owner.as_local() else {
                continue;
            };
            let Some(span) = diagnostics::source_span(tcx, owner, tcx.def_span(owner)) else {
                continue;
            };
            let adt = tcx.adt_def(owner);
            if !adt.is_struct() || context.mutations.contains(&owner) {
                continue;
            }
            let fields = &adt.non_enum_variant().fields;
            let args = ty::GenericArgs::identity_for_item(tcx, owner);
            let productions = &context.productions[&owner];
            let constructions =
                productions
                    .iter()
                    .filter(|production| match production.production_kind {
                        ProductionKind::Construction => true,
                        ProductionKind::Return => false,
                    });
            let returns =
                productions
                    .iter()
                    .filter(|production| match production.production_kind {
                        ProductionKind::Construction => false,
                        ProductionKind::Return => true,
                    });
            let values: Vec<_> = constructions.chain(returns).collect();
            let mut resolved_values = Vec::new();
            for production in &values {
                let guards = self.resolve_guards(&production.guards)?;
                if self
                    .graph
                    .conjunction(&guards, &crate::sequence::Sequence::EMPTY)?
                    == Truth::Refuted
                {
                    continue;
                }
                let value = self.resolve_expression(production.value, &guards)?;
                resolved_values.push((guards, value));
            }
            if resolved_values.is_empty() {
                continue;
            }
            for (flag, field) in fields.iter_enumerated() {
                if field.vis.is_public() || !field.ty(tcx, args).skip_normalization().is_bool() {
                    continue;
                }
                for (payload, other) in fields.iter_enumerated() {
                    if other.vis.is_public() {
                        continue;
                    }
                    let ty = other.ty(tcx, args).skip_normalization();
                    let ty::Adt(option, _) = ty.kind() else {
                        continue;
                    };
                    if !tcx.is_diagnostic_item(sym::Option, option.did()) {
                        continue;
                    }
                    let mut complete = Some(());
                    let mut implication = Some(());
                    let mut present = None;
                    let mut absent = None;
                    for (guards, value) in &resolved_values {
                        let flag_value = self.graph.field(*value, flag.index())?;
                        let payload_value = self.graph.field(*value, payload.index())?;
                        let has_payload = self
                            .graph
                            .intern_condition(ConditionNode::Variant(payload_value, 1))?;
                        match self.graph.truth(has_payload, guards)? {
                            Truth::Proven => present = Some(()),
                            Truth::Refuted => absent = Some(()),
                            Truth::Unknown(_) => {}
                        }
                        let one = self.graph.intern_expr(ExprNode::Number(1))?;
                        let antecedent = self.graph.intern_condition(ConditionNode::Compare(
                            Order::Equal,
                            flag_value,
                            one,
                        ))?;
                        if self.graph.truth(antecedent, guards)? != Truth::Refuted {
                            let required = self.graph.push(*guards, antecedent)?;
                            if self.graph.truth(has_payload, &required)? != Truth::Proven {
                                implication = None;
                            }
                        }
                        let has_payload = self.graph.intern_expr(ExprNode::Test(has_payload))?;
                        let condition = self.graph.intern_condition(ConditionNode::Compare(
                            Order::Equal,
                            flag_value,
                            has_payload,
                        ))?;
                        let condition = self.resolve_condition(condition, guards)?;
                        if self.graph.truth(condition, guards)? != Truth::Proven {
                            complete = None;
                        }
                    }
                    if let Some(()) = complete {
                        findings.push((
                            local,
                            states::Finding {
                                span,
                                evidence: CompilerEvidence::DuplicatedState {
                                    relation: format!(
                                        "`{}` always equals whether `{}` is Some",
                                        field.name, other.name
                                    ),
                                },
                            },
                        ));
                    } else if let (Some(()), Some(()), Some(())) = (implication, present, absent) {
                        findings.push((local, states::Finding { span, evidence: CompilerEvidence::CorrelatedState {
                        relation: format!("`{} = true` requires `{} = Some(..)`; the independent fields also permit `None` with `true`", field.name, other.name),
                    } }));
                    }
                }
            }
        }
        Ok(findings)
    }
}
