//! Resolves linked contracts and selects source evidence for diagnostics.

mod boundaries;
mod evaluator;
mod reviews;

use rustc_abi::FieldIdx;
use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap};
use rustc_hir::def_id::{DefId, DefPathHash, LocalDefId};
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;
use shapelint::{CheckOutcome, CompilerEvidence};

use crate::contracts::graph::{
    CapacityError, ConditionId, ConditionNode, ExprId, ExprNode, Graph, NodeId, TargetNode,
};
use crate::contracts::{
    Call, CheckBasis, Consumer, Invocation, Operation, Order, Relocation, Truth, Work, summaries,
};
use crate::pipeline::AnalysisGaps;
use crate::pipeline::report::evaluator::Evaluator;
use crate::sequence::Sequence;
use crate::{diagnostics, states};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
struct RequirementSourceOrder {
    file: String,
    offset: u32,
    def: DefPathHash,
}

enum RequirementEvidence<'g> {
    Invalidated {
        def: DefId,
        condition: ConditionId<'g>,
        mutation: Consumer,
    },
    AnalysisIncomplete {
        operation: String,
        consumer: Consumer,
    },
    Invalid {
        def: DefId,
        condition: ConditionId<'g>,
        consumer: Consumer,
        origin: Option<Consumer>,
    },
    Unproven {
        def: DefId,
        condition: ConditionId<'g>,
        consumer: Consumer,
        outcome: Truth,
        origin: Option<Consumer>,
    },
}

impl<'g> Evaluator<'_, '_, 'g> {
    fn render_requirement<'tcx>(
        &mut self,
        evidence: RequirementEvidence<'g>,
        tcx: TyCtxt<'tcx>,
        context: &mut ReportContext<'_, 'tcx, 'g>,
    ) -> Result<CompilerEvidence, CapacityError> {
        match evidence {
            RequirementEvidence::Invalidated {
                def,
                condition,
                mutation,
            } => {
                let mut mutation = mutation.source(tcx, context.sources);
                mutation.label.message = "this mutation invalidates the earlier guarantee".into();
                Ok(CompilerEvidence::InvalidatedValidation {
                    condition: diagnostics::Condition {
                        restorer: &context.restorer,
                        tcx,
                        def,
                        graph: self.graph,
                        condition,
                    }
                    .text()?,
                    mutation,
                })
            }
            RequirementEvidence::AnalysisIncomplete {
                operation,
                consumer,
            } => {
                let origin = consumer.source(tcx, context.sources);
                Ok(CompilerEvidence::AnalysisIncomplete { operation, origin })
            }
            RequirementEvidence::Invalid {
                def,
                condition,
                consumer,
                origin,
            } => {
                self.work.descriptions_rendered = self.work.descriptions_rendered.saturating_add(1);
                let diagnostics::Description::Check {
                    unproven: _,
                    invalid,
                    requirement,
                } = (diagnostics::Condition {
                    restorer: &context.restorer,
                    tcx,
                    def,
                    graph: self.graph,
                    condition,
                })
                .describe(&consumer)?
                else {
                    unreachable!("supported requirement selected a check description")
                };
                Ok(CompilerEvidence::InvalidPrecondition {
                    operation: invalid.into(),
                    requirement,
                    origin: origin.map(|consumer| consumer.source(tcx, context.sources)),
                })
            }
            RequirementEvidence::Unproven {
                def,
                condition,
                consumer,
                outcome,
                origin,
            } => {
                self.work.descriptions_rendered = self.work.descriptions_rendered.saturating_add(1);
                let diagnostics::Description::Check {
                    unproven,
                    invalid: _,
                    requirement,
                } = (diagnostics::Condition {
                    restorer: &context.restorer,
                    tcx,
                    def,
                    graph: self.graph,
                    condition,
                })
                .describe(&consumer)?
                else {
                    unreachable!("supported requirement selected a check description")
                };
                Ok(CompilerEvidence::UnprovenPrecondition {
                    explanation: match outcome {
                        Truth::Unknown(reason) => reason.to_string(),
                        Truth::Refuted => "This check fails on a path whose reachability has not been established.".into(),
                        Truth::Proven => unreachable!("proved requirements were discharged"),
                    },
                    operation: unproven.into(),
                    requirement,
                    origin: origin.map(|consumer| consumer.source(tcx, context.sources)),
                })
            }
        }
    }
}

struct RequirementCandidate<'g> {
    position: usize,
    order: RequirementSourceOrder,
    owner: LocalDefId,
    evidence: RequirementEvidence<'g>,
}

fn publish_requirement_finding<'g>(
    tcx: TyCtxt<'_>,
    reported: &mut FxIndexMap<(Span, ConditionId<'g>), RequirementCandidate<'g>>,
    owner: LocalDefId,
    consumer: &Consumer,
    span: Span,
    condition: ConditionId<'g>,
    evidence: RequirementEvidence<'g>,
    position: usize,
) {
    let source = consumer.span.source_callsite();
    let file = tcx.sess.source_map().lookup_source_file(source.lo());
    let order = RequirementSourceOrder {
        file: file.name.prefer_local_unconditionally().to_string(),
        offset: file.original_relative_byte_pos(source.lo()).0,
        def: tcx.def_path_hash(consumer.def),
    };
    let key = (span, condition);
    match reported.get_mut(&key) {
        Some(candidate) if order < candidate.order => {
            candidate.order = order;
            candidate.owner = owner;
            candidate.evidence = evidence;
        }
        Some(_) => {}
        None => {
            reported.insert(
                key,
                RequirementCandidate {
                    position,
                    order,
                    owner,
                    evidence,
                },
            );
        }
    }
}

pub(crate) struct EstablishedCheck<'g> {
    basis: CheckBasis<Sequence<'g, ConditionId<'g>>>,
    condition: ConditionId<'g>,
    outcome: CheckOutcome,
    support: evaluator::Support<'g>,
}

impl<'g> EstablishedCheck<'g> {
    fn render<'tcx>(
        self,
        tcx: TyCtxt<'tcx>,
        def: DefId,
        graph: &mut Graph<'g>,
        restorer: &std::cell::RefCell<crate::values::Restorer<'tcx, 'g>>,
        origin: Option<shapelint::Related>,
    ) -> Result<CompilerEvidence, CapacityError> {
        let Self {
            condition,
            outcome,
            support,
            basis,
        } = self;
        let rendered = diagnostics::Condition {
            restorer,
            tcx,
            def,
            graph,
            condition,
        }
        .text()?;
        let sequence = graph.evidence_sequence(support.facts)?;
        let facts: Vec<_> = graph
            .items(sequence)
            .copied()
            .map(|condition| {
                diagnostics::Condition {
                    restorer,
                    tcx,
                    def,
                    graph,
                    condition,
                }
                .text()
            })
            .collect::<Result<_, _>>()?;
        let mut established = match (facts.first(), support.derivation) {
            (Some(_), evaluator::Derivation::Direct) => {
                format!("Established before this check: {}.", facts.join("; "))
            }
            (Some(_), evaluator::Derivation::Recursive) => format!(
                "Recursive return and control-flow analysis, together with {}, establishes this result.",
                facts.join("; ")
            ),
            (None, evaluator::Derivation::Recursive) => {
                "Recursive return and control-flow analysis establishes this result.".to_owned()
            }
            (None, evaluator::Derivation::Direct) => {
                let conclusion = match outcome {
                    CheckOutcome::AlwaysTrue => condition,
                    CheckOutcome::AlwaysFalse => graph.negate(condition)?,
                };
                format!(
                    "Known values imply {}.",
                    diagnostics::Condition {
                        restorer,
                        tcx,
                        def,
                        graph,
                        condition: conclusion
                    }
                    .text()?
                )
            }
        };
        if let CheckBasis::ControlFlow(basis) = basis {
            let facts: Vec<_> = graph
                .items(basis)
                .map(|condition| {
                    diagnostics::Condition {
                        restorer,
                        tcx,
                        def,
                        graph,
                        condition: *condition,
                    }
                    .text()
                })
                .collect::<Result<_, _>>()?;
            let historical = match facts.first() {
                Some(_) => format!(
                    "Earlier control flow selected values using {}.",
                    facts.join("; ")
                ),
                None => "Earlier control-flow analysis selected these values.".to_owned(),
            };
            established.push(' ');
            established.push_str(&historical);
        }
        let evidence = CompilerEvidence::RedundantCheck {
            condition: rendered,
            outcome,
            established,
            origin,
        };
        Ok(evidence)
    }
}

#[derive(Clone, Copy)]
enum ProductionKind {
    Construction,
    Return,
}

struct Production<'g> {
    producer: DefId,
    production_kind: ProductionKind,
    value: ExprId<'g>,
    guards: Sequence<'g, ConditionId<'g>>,
}

struct ReportContext<'a, 'tcx, 'g> {
    sources: &'a diagnostics::Sources,
    restorer: std::cell::RefCell<crate::values::Restorer<'tcx, 'g>>,
    tcx: TyCtxt<'tcx>,
    call_index: &'a crate::callers::CallIndex<'a, 'g>,
    summaries: &'a FxHashMap<DefId, summaries::SummaryId<'g>>,
    constructors: &'a FxHashMap<DefId, Vec<(DefId, summaries::SummaryId<'g>)>>,
    coverage: &'a FxHashSet<rustc_hir::def_id::CrateNum>,
    productions: &'a FxHashMap<DefId, Vec<Production<'g>>>,
    resolved_productions: FxHashMap<DefId, Vec<(DefId, Sequence<'g, ConditionId<'g>>, ExprId<'g>)>>,
    mutations: &'a FxHashSet<DefId>,
    guarantees: FxHashMap<(DefId, ConditionId<'g>), Option<()>>,
}

impl<'g> Evaluator<'_, '_, 'g> {
    pub fn escaped_functions(
        &mut self,
        context: &ReportContext<'_, '_, 'g>,
        scope: crate::callers::Scope,
        definitions: impl Iterator<Item = (DefId, summaries::SummaryId<'g>)>,
        calls: &[(DefId, Call<'g, ExprId<'g>, ConditionId<'g>, TargetNode<'g>>)],
    ) -> Result<FxHashSet<DefId>, CapacityError> {
        let mut escaped = FxHashSet::default();
        for (owner, id) in definitions {
            let summary = self.graph[id];
            escaped.extend(self.graph.members(summary.escapes));
            if let crate::callers::Exposure::External =
                crate::callers::exposure(context.tcx, owner, scope)
            {
                let mut returns = self.graph.scan(summary.returns);
                while let Some(returned) = returns.next() {
                    let value = self.resolve_expression(returned.value, &returned.guards)?;
                    self.graph.functions(value, &mut escaped)?;
                }
            }
        }
        for (_, call) in calls {
            let Some(def) = call.target.definition(self.graph) else {
                if let TargetNode::Indirect(value) = &call.target {
                    let value = self.resolve_expression(*value, &call.guards)?;
                    self.graph.functions(value, &mut escaped)?;
                }
                let mut arguments = self.graph.scan(call.arguments);
                while let Some(argument) = arguments.next() {
                    self.graph.functions(argument, &mut escaped)?;
                }
                continue;
            };
            let Some(summary) = context.summaries.get(&def) else {
                let mut arguments = self.graph.scan(call.arguments);
                while let Some(argument) = arguments.next() {
                    self.graph.functions(argument, &mut escaped)?;
                }
                continue;
            };
            let summary = self.graph[*summary];
            self.graph.escaped_argument_functions(
                call.arguments,
                summary.escaped_arguments,
                &mut escaped,
            )?;
        }
        Ok(escaped)
    }
}

struct ParameterField {
    owner: DefId,
    argument: usize,
    index: usize,
}

fn parameter_field<'g>(
    tcx: TyCtxt<'_>,
    def: DefId,
    graph: &Graph<'g>,
    expression: ExprId<'g>,
) -> Option<ParameterField> {
    let projection = match &graph[expression] {
        ExprNode::Length(base) => *base,
        _ => expression,
    };
    let ExprNode::Field(base, field) = &graph[projection] else {
        return None;
    };
    let ExprNode::Argument(argument) = graph[*base] else {
        return None;
    };
    match tcx.def_kind(def) {
        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn => {}
        _ => return None,
    }
    let signature = tcx.fn_sig(def).instantiate_identity().skip_binder();
    let ty = signature.inputs().get(argument)?.peel_refs();
    if ty.is_privately_uninhabited(tcx, ty::TypingEnv::post_analysis(tcx, def)) {
        return None;
    }
    let ty::Adt(adt, _) = *ty.kind() else {
        return None;
    };
    if !adt.is_struct() || !adt.did().is_local() {
        return None;
    }
    let field_def = adt
        .non_enum_variant()
        .fields
        .get(FieldIdx::from_usize(*field))?;
    let ty = tcx
        .type_of(field_def.did)
        .instantiate_identity()
        .skip_normalization();
    match (&graph[expression], ty.peel_refs().kind()) {
        (ExprNode::Field(..), ty::Uint(_)) => {}
        (ExprNode::Length(_), ty::Str | ty::Slice(_) | ty::Array(..)) => {}
        (ExprNode::Length(_), ty::Adt(adt, _))
            if tcx.is_diagnostic_item(rustc_span::sym::Vec, adt.did())
                || tcx.lang_items().string() == Some(adt.did()) => {}
        _ => return None,
    }
    Some(ParameterField {
        owner: adt.did(),
        argument,
        index: *field,
    })
}

impl<'g> Evaluator<'_, '_, 'g> {
    fn construction_guarantee(
        &mut self,
        tcx: TyCtxt<'_>,
        def: DefId,
        condition: ConditionId<'g>,
        context: &mut ReportContext<'_, '_, 'g>,
    ) -> Result<Option<()>, CapacityError> {
        let ConditionNode::Compare(_, left, right) = self.graph[condition] else {
            return Ok(None);
        };
        let mut fields = Vec::new();
        for value in [left, right] {
            match &self.graph[value] {
                ExprNode::Number(_) => {}
                _ => {
                    let Some(field) = parameter_field(tcx, def, self.graph, value) else {
                        return Ok(None);
                    };
                    fields.push(field);
                }
            }
        }
        let Some(first) = fields.first() else {
            return Ok(None);
        };
        let owner = first.owner;
        let argument = first.argument;
        let definition = tcx.adt_def(owner);
        for field in fields {
            if field.owner != owner
                || field.argument != argument
                || definition.non_enum_variant().fields[FieldIdx::from_usize(field.index)]
                    .vis
                    .is_public()
            {
                return Ok(None);
            }
        }
        let entry = match context.guarantees.entry((owner, condition)) {
            std::collections::hash_map::Entry::Occupied(entry) => return Ok(*entry.get()),
            std::collections::hash_map::Entry::Vacant(entry) => entry,
        };
        let guarantee = 'proof: {
            if context.mutations.contains(&owner) {
                break 'proof None;
            }
            let productions = match context.resolved_productions.entry(owner) {
                std::collections::hash_map::Entry::Occupied(entry) => entry.into_mut(),
                std::collections::hash_map::Entry::Vacant(entry) => {
                    let Some(productions) = context.productions.get(&owner) else {
                        break 'proof None;
                    };
                    let productions = productions
                        .iter()
                        .map(|production| {
                            (production.producer, production.value, production.guards)
                        })
                        .collect::<Vec<_>>();
                    let mut resolved = Vec::new();
                    for (producer, value, guards) in productions {
                        let guards = self.resolve_guards(&guards)?;
                        if self
                            .graph
                            .conjunction(&guards, &crate::sequence::Sequence::EMPTY)?
                            == Truth::Refuted
                        {
                            continue;
                        }
                        let value = self.resolve_expression(value, &guards)?;
                        resolved.push((producer, guards, value));
                    }
                    entry.insert(resolved)
                }
            };
            let mut observed = None;
            for (producer, guards, value) in productions.iter() {
                let unknown = self.graph.intern_expr(ExprNode::Unknown)?;
                let arguments = crate::sequence::Sequences::from_iter(
                    self.graph.as_mut(),
                    (0..=argument).map(|index| if index == argument { *value } else { unknown }),
                )?;
                let invocation = Invocation::LOCAL;
                let requirement =
                    self.graph
                        .substitute_condition(condition, &arguments, &invocation)?;
                let requirement = self.resolve_condition(requirement, guards)?;
                if self.graph.truth(requirement, guards)? != Truth::Proven {
                    match tcx.def_kind(*producer) {
                        rustc_hir::def::DefKind::Fn | rustc_hir::def::DefKind::AssocFn => {}
                        _ => break 'proof None,
                    }
                    let signature = tcx.fn_sig(*producer).instantiate_identity().skip_binder();
                    let mut preserved = None;
                    let inputs = signature.inputs().iter().enumerate();
                    for (index, ty) in inputs {
                        let ty::Adt(adt, _) = ty.peel_refs().kind() else {
                            continue;
                        };
                        if adt.did() != owner {
                            continue;
                        }
                        let value = self.graph.intern_expr(ExprNode::Argument(argument))?;
                        let incoming = crate::sequence::Sequences::from_iter(
                            self.graph.as_mut(),
                            (0..signature.inputs().len())
                                .map(|position| if position == index { value } else { unknown }),
                        )?;
                        let invocation = Invocation::LOCAL;
                        if self
                            .graph
                            .substitute_condition(requirement, &incoming, &invocation)?
                            == condition
                        {
                            preserved = Some(());
                            break;
                        }
                    }
                    let Some(()) = preserved else {
                        break 'proof None;
                    };
                }
                observed = Some(());
            }
            observed
        };
        entry.insert(guarantee);
        Ok(guarantee)
    }
}

pub struct Analysis {
    pub findings: Vec<(LocalDefId, states::Finding)>,
    pub work: Work,
}

struct ReportIndex<'a, 'g> {
    summaries: &'a crate::pipeline::Summaries<'g>,
    ordered_definitions: Vec<(DefId, summaries::SummaryId<'g>)>,
    calls: crate::callers::CallIndex<'a, 'g>,
    productions: FxHashMap<DefId, Vec<Production<'g>>>,
    constructors: FxHashMap<DefId, Vec<(DefId, summaries::SummaryId<'g>)>>,
    mutations: FxHashSet<DefId>,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum ReportSite {
    Local(LocalDefId),
    Construction {
        constructor: LocalDefId,
        owner: DefId,
        first: usize,
        second: usize,
    },
    Representation {
        owner: LocalDefId,
        first: usize,
        second: usize,
        order: Order,
    },
}

pub fn findings<'g>(
    tcx: TyCtxt<'_>,
    summaries: &crate::pipeline::Summaries<'g>,
    graph: &mut Graph<'g>,
    scope: crate::callers::Scope,
    gaps: AnalysisGaps,
    sources: &diagnostics::Sources,
) -> Result<Analysis, CapacityError> {
    use rustc_data_structures::marker::IntoDynSyncSend;

    let index = ReportIndex::try_new(tcx, summaries, graph)?;
    let mut definitions: Vec<_> = summaries
        .definitions
        .keys()
        .filter_map(|def| def.as_local())
        .collect();
    definitions.sort_by_key(|def| tcx.def_span(*def).lo());
    let workers = tcx
        .sess
        .opts
        .jobs
        .frontend
        .map_or(0, |jobs| (1..jobs.get()).len());
    let serial = |graph: &mut Graph<'g>| -> Result<_, CapacityError> {
        let (mut evaluator, mut context) = index.context(tcx, graph, sources)?;
        let findings = evaluator.crate_findings(&mut context, scope)?;
        let functions = evaluator.function_findings(&mut context, &definitions, gaps)?;
        Ok((
            Analysis {
                findings,
                work: evaluator.finish_work(),
            },
            vec![functions],
        ))
    };
    let (mut analysis, batches) = if workers == 0 || definitions.len() <= 1 {
        serial(graph)?
    } else {
        // Every job owns its evaluator and recursion state. Graph views share canonical
        // values. Contiguous definition ranges preserve the serial order at collection.
        let index = IntoDynSyncSend(&index);
        let sources = IntoDynSyncSend(sources);
        let mut global_graph = IntoDynSyncSend(graph.fork());
        let size = definitions.len().div_ceil(workers);
        let jobs: Vec<_> = definitions
            .chunks(size)
            .map(|defs| (defs, IntoDynSyncSend(graph.fork())))
            .collect();
        let (global, batches) = rustc_data_structures::sync::par_join(
            || -> Result<_, CapacityError> {
                let (mut evaluator, mut context) =
                    index.context(tcx, &mut global_graph, &sources)?;
                let findings = evaluator.crate_findings(&mut context, scope)?;
                let analysis = Analysis {
                    findings,
                    work: evaluator.finish_work(),
                };
                Ok((analysis, evaluator.recursion))
            },
            || {
                rustc_data_structures::sync::par_map::<_, _, _, Vec<_>>(
                    jobs,
                    |(defs, IntoDynSyncSend(mut view))| -> Result<_, CapacityError> {
                        let (mut evaluator, mut context) =
                            index.context(tcx, &mut view, &sources)?;
                        let findings = evaluator.function_findings(&mut context, defs, gaps)?;
                        let work = evaluator.finish_work();
                        Ok((findings, work, evaluator.recursion))
                    },
                )
            },
        );
        let (mut analysis, recursion) = global?;
        let mut workers = Vec::with_capacity(batches.len());
        let mut ordered = Vec::with_capacity(batches.len());
        for batch in batches {
            let (functions, work, calls) = batch?;
            workers.push(calls);
            analysis.work += work;
            ordered.push(functions);
        }
        // A newly resolved call can close a cycle across batches. That changes the
        // recursion decisions already made by independent requirement evaluators.
        if let Some(_) = recursion.merged_revision(workers)? {
            let (mut retried, batches) = serial(graph)?;
            retried.work += analysis.work;
            (retried, batches)
        } else {
            (analysis, ordered)
        }
    };
    let discarded: FxHashSet<_> = analysis
        .findings
        .iter()
        .filter_map(|(local, finding)| match finding.evidence {
            CompilerEvidence::DiscardedValidation { .. } => Some((*local, finding.span)),
            _ => None,
        })
        .collect();
    let mut seen = FxHashSet::default();
    let functions = batches.into_iter().flatten();
    for (site, finding) in functions {
        let owner = match site {
            ReportSite::Local(local) => {
                if let CompilerEvidence::RedundantCheck { .. } = finding.evidence
                    && discarded.contains(&(local, finding.span))
                {
                    continue;
                }
                local
            }
            ReportSite::Construction {
                constructor: owner, ..
            }
            | ReportSite::Representation { owner, .. } => {
                if !seen.insert(site) {
                    continue;
                }
                owner
            }
        };
        analysis.findings.push((owner, finding));
    }
    Ok(analysis)
}

impl<'a, 'g> ReportIndex<'a, 'g> {
    fn try_new(
        tcx: TyCtxt<'_>,
        summaries: &'a crate::pipeline::Summaries<'g>,
        graph: &Graph<'g>,
    ) -> Result<Self, CapacityError> {
        let definitions = &summaries.definitions;
        let calls = crate::callers::CallIndex::try_new(tcx, definitions, graph)?;
        let mut productions: FxHashMap<_, Vec<_>> = FxHashMap::default();
        let mut constructors: FxHashMap<_, Vec<_>> = FxHashMap::default();
        let mut mutations = FxHashSet::default();
        for (&producer, id) in definitions {
            let summary = graph[*id];
            mutations.extend(graph.members(summary.mutations));
            for construction in graph.items(summary.constructions) {
                productions
                    .entry(construction.owner)
                    .or_default()
                    .push(Production {
                        producer,
                        production_kind: ProductionKind::Construction,
                        value: construction.value,
                        guards: construction.guards,
                    });
            }
            if let Some(owner) = summary.output {
                constructors.entry(owner).or_default().push((producer, *id));
                for returned in graph.items(summary.returns) {
                    productions.entry(owner).or_default().push(Production {
                        producer,
                        production_kind: ProductionKind::Return,
                        value: returned.value,
                        guards: returned.guards,
                    });
                }
            }
        }
        let (mut local, mut imported): (Vec<_>, Vec<_>) = definitions
            .iter()
            .map(|(&def, &summary)| (def, summary))
            .partition(|(def, _)| def.is_local());
        local.sort_by_cached_key(|&(def, _)| (tcx.def_span(def).lo(), tcx.def_path_hash(def)));
        imported.sort_by_cached_key(|&(def, _)| tcx.def_path_hash(def));
        let mut ordered_definitions = local;
        ordered_definitions.extend(imported);
        Ok(Self {
            summaries,
            ordered_definitions,
            calls,
            productions,
            constructors,
            mutations,
        })
    }

    fn context<'r, 'tcx>(
        &'r self,
        tcx: TyCtxt<'tcx>,
        graph: &'r mut Graph<'g>,
        sources: &'r diagnostics::Sources,
    ) -> Result<(Evaluator<'r, 'tcx, 'g>, ReportContext<'r, 'tcx, 'g>), CapacityError> {
        let summaries = &self.summaries.definitions;
        let restorer = std::cell::RefCell::new(crate::values::Restorer::new(
            tcx,
            crate::values::Values::share(graph.as_ref()),
        ));
        let evaluator = Evaluator::try_new(tcx, &self.ordered_definitions, graph, &self.calls)?;
        let context = ReportContext {
            sources,
            restorer,
            tcx,
            call_index: &self.calls,
            summaries,
            constructors: &self.constructors,
            coverage: &self.summaries.coverage,
            productions: &self.productions,
            resolved_productions: FxHashMap::default(),
            mutations: &self.mutations,
            guarantees: FxHashMap::default(),
        };
        Ok((evaluator, context))
    }
}

impl<'g> Evaluator<'_, '_, 'g> {
    fn crate_findings(
        &mut self,
        context: &mut ReportContext<'_, '_, 'g>,
        scope: crate::callers::Scope,
    ) -> Result<Vec<(LocalDefId, states::Finding)>, CapacityError> {
        let mut findings = self.review_findings(context)?;
        findings.extend(self.boundary_findings(context, scope)?);
        Ok(findings)
    }
}

impl<'g> Evaluator<'_, '_, 'g> {
    fn function_findings(
        &mut self,
        context: &mut ReportContext<'_, '_, 'g>,
        defs: &[LocalDefId],
        gaps: AnalysisGaps,
    ) -> Result<Vec<(ReportSite, states::Finding)>, CapacityError> {
        let tcx = context.tcx;
        let sources = context.sources;
        let summaries = context.summaries;
        let mut findings = Vec::new();
        let mut seen = FxHashSet::default();
        for &local in defs {
            let def = local.to_def_id();
            let summary = self.graph[summaries[&def]];
            let mut checks_reported = FxHashSet::default();
            let mut checks = self.graph.scan(summary.checks);
            while let Some(check) = checks.next() {
                let guards = self.resolve_guards(&check.guards)?;
                if let Some(established) =
                    self.established(check.condition, &guards, &check.basis)?
                    && checks_reported.insert(check.span)
                {
                    let evidence =
                        established.render(tcx, def, self.graph, &context.restorer, None)?;
                    findings.push((
                        ReportSite::Local(local),
                        states::Finding {
                            span: check.span,
                            evidence,
                        },
                    ));
                }
            }
            for call in context.call_index.calls(def) {
                let TargetNode::Direct(instance) = call.target else {
                    continue;
                };
                let instance = self.graph[instance];
                if instance.dispatch != crate::values::Dispatch::Item {
                    continue;
                }
                let callee_def = instance.def;
                let Some(callee) = summaries.get(&callee_def) else {
                    continue;
                };
                let callee = self.graph[*callee];
                let invocation = Invocation {
                    relocation: Relocation::Into(None),
                    generics: instance.args.clone(),
                };
                let guards = self.resolve_guards(&call.guards)?;
                let mut checks = self.graph.scan(callee.checks);
                while let Some(check) = checks.next() {
                    let local_guards = self.resolve_guards(&check.guards)?;
                    if let Some(_) =
                        self.established(check.condition, &local_guards, &check.basis)?
                    {
                        continue;
                    }
                    let mut path = crate::sequence::Sequence::EMPTY;
                    let mut input = self.graph.scan(check.guards);
                    while let Some(guard) = input.next() {
                        let guard =
                            self.graph
                                .substitute_condition(guard, &call.arguments, &invocation)?;
                        let guard = self.resolve_condition(guard, &guards)?;
                        path = self.graph.push(path, guard)?;
                    }
                    if self.graph.conjunction(&path, &guards)? != Truth::Proven {
                        continue;
                    }
                    let condition = self.graph.substitute_condition(
                        check.condition,
                        &call.arguments,
                        &invocation,
                    )?;
                    let basis = match &check.basis {
                        CheckBasis::Expression => CheckBasis::Expression,
                        CheckBasis::ControlFlow(basis) => CheckBasis::ControlFlow(
                            self.graph
                                .substitute_guards(basis, &call.arguments, &invocation)?,
                        ),
                    };
                    let basis = self.graph.combine_bases(&call.basis, &basis)?;
                    if let Some(established) = self.established(condition, &guards, &basis)?
                        && checks_reported.insert(call.span)
                    {
                        let origin = Consumer {
                            def: callee_def,
                            span: check.span,
                            operation: Operation::Condition,
                        }
                        .source(tcx, sources);
                        let evidence = established.render(
                            tcx,
                            def,
                            self.graph,
                            &context.restorer,
                            Some(origin),
                        )?;
                        findings.push((
                            ReportSite::Local(local),
                            states::Finding {
                                span: call.span,
                                evidence,
                            },
                        ));
                    }
                }
            }
            let exported = tcx.effective_visibilities(()).is_exported(local);
            let mut reported = FxIndexMap::default();
            let mut coverage = FxIndexMap::default();
            let demand = match (exported, gaps) {
                (true, AnalysisGaps::Show) => evaluator::ReportDemand::ExportedContract,
                _ => evaluator::ReportDemand::LocalFindings,
            };
            let requirements_start = findings.len();
            let requirements = self.resolve_requirements(def, demand)?;
            for (span, mut group) in requirements {
                while let Some(report) = self.next_requirement(&mut group)? {
                    let Some(report) = (match report {
                        evaluator::RequirementReport::Pending(id) => {
                            self.report_requirement(&mut group, id, span)?
                        }
                        evaluator::RequirementReport::Resolved(requirement) => Some(requirement),
                    }) else {
                        continue;
                    };
                    let evaluator::ResolvedRequirement {
                        requirement,
                        condition,
                        outcome,
                    } = report;
                    let consumer = self.graph[requirement.consumer].export(self.graph);
                    let guards = requirement.guards;
                    if let Some(()) = self.construction_guarantee(tcx, def, condition, context)? {
                        continue;
                    }
                    if let Truth::Unknown(_) = outcome {
                        let mut stale = None;
                        let mut facts = self.graph.scan(requirement.invalidated);
                        while let Some(fact) = facts.next() {
                            let fact_condition = self.resolve_condition(fact.condition, &guards)?;
                            let restored = self.graph.push(guards, fact_condition)?;
                            if self.graph.truth(condition, &restored)? == Truth::Proven {
                                stale = Some(fact);
                                break;
                            }
                        }
                        if let Some(fact) = stale {
                            let mutation = Consumer {
                                def: fact.def,
                                span: fact.span,
                                operation: Operation::Condition,
                            };
                            publish_requirement_finding(
                                tcx,
                                &mut reported,
                                local,
                                &consumer,
                                requirement.span,
                                condition,
                                RequirementEvidence::Invalidated {
                                    def,
                                    condition,
                                    mutation,
                                },
                                findings.len(),
                            );
                            continue;
                        }
                    }
                    let displayed = if let Some(()) = self.graph.known(NodeId::Condition(condition))
                    {
                        condition
                    } else {
                        requirement.condition
                    };
                    if let Some(operation) = (diagnostics::Condition {
                        restorer: &context.restorer,
                        tcx,
                        def,
                        graph: self.graph,
                        condition: displayed,
                    })
                    .unsupported(&consumer)
                    {
                        if !exported || gaps == AnalysisGaps::Hide {
                            continue;
                        }
                        publish_requirement_finding(
                            tcx,
                            &mut coverage,
                            local,
                            &consumer,
                            requirement.span,
                            condition,
                            RequirementEvidence::AnalysisIncomplete {
                                operation: operation.into(),
                                consumer: consumer.clone(),
                            },
                            findings.len(),
                        );
                        continue;
                    }
                    if let Truth::Proven = outcome {
                        continue;
                    }
                    if let Truth::Refuted = outcome
                        && self
                            .graph
                            .conjunction(&guards, &crate::sequence::Sequence::EMPTY)?
                            == Truth::Proven
                    {
                        publish_requirement_finding(
                            tcx,
                            &mut reported,
                            local,
                            &consumer,
                            requirement.span,
                            condition,
                            RequirementEvidence::Invalid {
                                def,
                                condition: displayed,
                                consumer: consumer.clone(),
                                origin: if def != consumer.def || requirement.span != consumer.span
                                {
                                    Some(consumer.clone())
                                } else {
                                    None
                                },
                            },
                            findings.len(),
                        );
                        continue;
                    }
                    {
                        let mut representation = None;
                        if let ConditionNode::Compare(
                            order @ (Order::LessEqual | Order::Less),
                            left,
                            right,
                        ) = self.graph[condition].clone()
                            && let (ExprNode::Field(..), ExprNode::Field(..)) =
                                (&self.graph[left], &self.graph[right])
                            && let Some(first) = parameter_field(tcx, def, self.graph, left)
                            && let Some(second) = parameter_field(tcx, def, self.graph, right)
                            && first.owner == second.owner
                            && first.argument == second.argument
                            && first.index != second.index
                        {
                            let adt = tcx.adt_def(first.owner);
                            let fields = &adt.non_enum_variant().fields;
                            if let None = self.graph.items(guards).next() {
                                let constructors =
                                    context.constructors.get(&first.owner).into_iter().flatten();
                                for &(constructor, id) in constructors {
                                    let summary = self.graph[id];
                                    let Some(constructor_local) = constructor.as_local() else {
                                        continue;
                                    };
                                    let mut returns = self.graph.scan(summary.returns);
                                    while let Some(returned) = returns.next() {
                                        let unknown = self.graph.intern_expr(ExprNode::Unknown)?;
                                        let arguments = crate::sequence::Sequences::from_iter(
                                            self.graph.as_mut(),
                                            (0..=first.argument).map(|index| {
                                                if index == first.argument {
                                                    returned.value
                                                } else {
                                                    unknown
                                                }
                                            }),
                                        )?;
                                        let mut guards = crate::sequence::Sequence::EMPTY;
                                        let mut input = self.graph.scan(returned.guards);
                                        while let Some(guard) = input.next() {
                                            let empty = crate::sequence::Sequence::EMPTY;
                                            let guard = self.resolve_condition(guard, &empty)?;
                                            guards = self.graph.push(guards, guard)?;
                                        }
                                        let invocation = Invocation::LOCAL;
                                        let instantiated = self.graph.substitute_condition(
                                            condition,
                                            &arguments,
                                            &invocation,
                                        )?;
                                        let instantiated =
                                            self.resolve_condition(instantiated, &guards)?;
                                        let site = ReportSite::Construction {
                                            constructor: constructor_local,
                                            owner: first.owner,
                                            first: first.index,
                                            second: second.index,
                                        };
                                        if self.graph.truth(instantiated, &guards)?
                                            == Truth::Refuted
                                            && self.graph.conjunction(
                                                &guards,
                                                &crate::sequence::Sequence::EMPTY,
                                            )? == Truth::Proven
                                            && seen.insert(site)
                                        {
                                            findings.push((
                                                site,
                                                states::Finding {
                                                    span: tcx.def_span(constructor),
                                                    evidence:
                                                        CompilerEvidence::InconsistentConstruction {
                                                            assumption: format!(
                                                                "returned fields violate {}",
                                                                diagnostics::Condition {
                                                                    restorer: &context.restorer,
                                                                    tcx,
                                                                    def,
                                                                    graph: self.graph,
                                                                    condition: instantiated
                                                                }
                                                                .text()?
                                                            ),
                                                            consumer: format!(
                                                                "{} requires {}",
                                                                diagnostics::item(tcx, def),
                                                                diagnostics::Condition {
                                                                    restorer: &context.restorer,
                                                                    tcx,
                                                                    def,
                                                                    graph: self.graph,
                                                                    condition
                                                                }
                                                                .text()?
                                                            ),
                                                        },
                                                },
                                            ));
                                        }
                                    }
                                }
                            }
                            if fields[FieldIdx::from_usize(first.index)].vis.is_public()
                                && fields[FieldIdx::from_usize(second.index)].vis.is_public()
                            {
                                let witness = format!(
                                    "{} {{ {}: 1, {}: 0, .. }}",
                                    diagnostics::item(tcx, first.owner),
                                    fields[FieldIdx::from_usize(first.index)].name,
                                    fields[FieldIdx::from_usize(second.index)].name
                                );
                                representation =
                                    Some((first.owner, first.index, second.index, order, witness));
                            }
                        }
                        match representation {
                            Some((owner, first, second, order, witness)) => {
                                let site = ReportSite::Representation {
                                    owner: owner.expect_local(),
                                    first,
                                    second,
                                    order,
                                };
                                if seen.insert(site) {
                                    let fields = &tcx.adt_def(owner).non_enum_variant().fields;
                                    let consumer = &consumer;
                                    let location = tcx
                                        .sess
                                        .source_map()
                                        .lookup_char_pos(consumer.span.source_callsite().lo());
                                    findings.push((
                                        site,
                                        states::Finding {
                                            span: tcx.def_span(owner),
                                            evidence: CompilerEvidence::UnencodedPrecondition {
                                                owner: diagnostics::item(tcx, owner),
                                                requirement: format!(
                                                    "{} {order} {}",
                                                    fields[FieldIdx::from_usize(first)].name,
                                                    fields[FieldIdx::from_usize(second)].name
                                                ),
                                                witness,
                                                consumer: format!(
                                                    "`{}` at {}:{}:{}",
                                                    diagnostics::item(tcx, consumer.def),
                                                    location
                                                        .file
                                                        .name
                                                        .prefer_local_unconditionally(),
                                                    location.line,
                                                    location.col.0 as u128 + 1
                                                ),
                                            },
                                        },
                                    ));
                                }
                                continue;
                            }
                            None if exported && gaps == AnalysisGaps::Show => {
                                publish_requirement_finding(
                                    tcx,
                                    &mut coverage,
                                    local,
                                    &consumer,
                                    requirement.span,
                                    condition,
                                    RequirementEvidence::Unproven {
                                        def,
                                        condition: displayed,
                                        consumer: consumer.clone(),
                                        outcome,
                                        origin: if def != consumer.def
                                            || requirement.span != consumer.span
                                        {
                                            Some(consumer.clone())
                                        } else {
                                            None
                                        },
                                    },
                                    findings.len(),
                                );
                                continue;
                            }
                            None => continue,
                        }
                    }
                }
            }
            // Report concrete findings in the same order in both modes. Coverage only fills
            // obligations that still lack a finding after all callees have contributed.
            coverage.retain(|key, candidate| {
                candidate.position = findings.len();
                !reported.contains_key(key)
            });
            let positions = requirements_start..findings.len();
            let mut direct = positions
                .zip(findings.split_off(requirements_start))
                .peekable();
            let candidates = reported.into_iter().chain(coverage);
            for (
                (span, _),
                RequirementCandidate {
                    position,
                    owner,
                    evidence,
                    ..
                },
            ) in candidates
            {
                while let Some((_, finding)) = direct.next_if(|(index, _)| *index < position) {
                    findings.push(finding);
                }
                findings.push((
                    ReportSite::Local(owner),
                    states::Finding {
                        span,
                        evidence: self.render_requirement(evidence, tcx, context)?,
                    },
                ));
            }
            findings.extend(direct.map(|(_, finding)| finding));
        }
        Ok(findings)
    }
}
