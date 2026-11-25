use crate::contracts::graph::{CapacityError, ConditionNode, ExprId, ExprNode, NodeId};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty;
use rustc_span::sym;
use shapelint::CompilerEvidence;

use crate::contracts::summaries::BehaviorNode;
use crate::contracts::{Consumer, Operation, Truth};
use crate::pipeline::report::{ReportContext, evaluator::Evaluator};
use crate::{callers, diagnostics, states};

#[derive(Clone, Copy, PartialEq, Eq)]
enum Alternative {
    False,
    True,
    Variant(DefId),
}

impl<'g> Evaluator<'_, '_, 'g> {
    fn parameter_callers(
        &mut self,
        context: &mut ReportContext<'_, '_, 'g>,
        candidates: &mut FxHashMap<DefId, FxHashSet<usize>>,
        scope: callers::Scope,
    ) -> Result<Option<callers::Callers<'g>>, CapacityError> {
        if candidates.is_empty() {
            return Ok(None);
        }
        let declarations = candidates.keys().copied().collect();
        let mut roots = context.call_index.relevant(&declarations);
        let mut descend = roots.clone();
        // Recursing with a callback emits an unknown call that can expose it.
        context
            .call_index
            .include_callers(&mut descend, self.recursion.recursive_definitions());
        roots.retain(|def| def.is_local());
        // A resolved callback keeps its root's owner and span. Either a direct or
        // an indirect local call can supply the location for an imported declaration.
        let local_calls = self.resolved_calls(&roots, &descend)?;
        let witnessed: FxHashSet<_> = local_calls
            .iter()
            .filter_map(|(_, call)| call.target.definition(self.graph))
            .collect();
        candidates.retain(|def, _| witnessed.contains(def));
        if candidates.is_empty() {
            return Ok(None);
        }

        let imported: FxHashSet<_> = candidates
            .keys()
            .copied()
            .filter(|def| !def.is_local())
            .collect();
        let mut calls = if imported.is_empty() {
            local_calls
        } else {
            // A dependency can have other callers or escapes anywhere in the linked
            // crates, even when those callers are unreachable from the reporting site.
            let mut roots = context.call_index.relevant(&imported);
            roots.retain(|def| !def.is_local());
            let mut calls = self.resolved_calls(&roots, &descend)?;
            calls.extend(local_calls);
            calls
        };
        let definitions = context
            .summaries
            .iter()
            .filter(|(owner, _)| owner.is_local() || !imported.is_empty())
            .map(|(&owner, &summary)| (owner, summary));
        let escapes = self.escaped_functions(context, scope, definitions, &calls)?;
        let values = &*self.graph;
        calls.retain(|(_, call)| match call.target.definition(values) {
            Some(def) => candidates.contains_key(&def),
            None => false,
        });
        let callers = callers::Callers::try_new(scope, values, calls, escapes, context.coverage)?;
        Ok(Some(callers))
    }
}

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
        let mut candidates: FxHashMap<DefId, FxHashSet<usize>> = FxHashMap::default();
        for def in &definitions {
            match tcx.def_kind(*def) {
                DefKind::Fn | DefKind::AssocFn => {}
                _ => continue,
            }
            let Some(_) = diagnostics::source_span(tcx, *def, tcx.def_span(*def)) else {
                continue;
            };
            let signature = tcx.fn_sig(*def).instantiate_identity().skip_binder();
            let inputs = signature.inputs().iter().enumerate();
            let mut eligible = FxHashSet::default();
            for (index, ty) in inputs {
                let Some(_) = tcx.fn_arg_idents(*def).get(index).copied().flatten() else {
                    continue;
                };
                match ty.kind() {
                    ty::Bool => {}
                    ty::Adt(adt, _) if adt.is_enum() => {}
                    _ => continue,
                }
                eligible.insert(index);
            }
            if eligible.is_empty() {
                continue;
            }
            let summary = self.graph[summaries[def]];
            let mut inspections = self.graph.scan(summary.inspections);
            while let Some(value) = inspections.next() {
                if let Some(inputs) = self.graph.inputs(NodeId::Expr(value))? {
                    for index in inputs {
                        if eligible.contains(&index) {
                            candidates.entry(*def).or_default().insert(index);
                        }
                    }
                }
            }
        }
        let callers = self.parameter_callers(context, &mut candidates, scope)?;
        let mut editable_options = None;
        definitions.retain(|def| def.is_local() || candidates.contains_key(def));
        let mut inspected: FxHashMap<DefId, FxHashSet<ExprId<'g>>> = FxHashMap::default();
        let mut forwarded: FxHashMap<DefId, FxHashMap<ExprId<'g>, usize>> = FxHashMap::default();
        for def in definitions {
            match tcx.def_kind(def) {
                DefKind::Fn | DefKind::AssocFn => {}
                _ => continue,
            }
            let Some(span) = diagnostics::source_span(tcx, def, tcx.def_span(def)) else {
                continue;
            };
            let signature = tcx.fn_sig(def).instantiate_identity().skip_binder();
            let summary = self.graph[summaries[&def]];
            let inputs = signature.inputs().iter().enumerate();
            for (index, ty) in inputs {
                let Some(ident) = tcx.fn_arg_idents(def).get(index).copied().flatten() else {
                    continue;
                };
                let parameter = ident.to_string();
                if let Some(local) = def.as_local()
                    && let ty::Adt(adt, _) = ty.peel_refs().kind()
                    && tcx.is_diagnostic_item(sym::Option, adt.did())
                {
                    let mut chain = Vec::new();
                    let mut current = def;
                    let mut argument = index;
                    let mut visited = FxHashSet::default();
                    while visited.insert(current) {
                        let Some(body) = summaries.get(&current) else {
                            break;
                        };
                        let body = self.graph[*body];
                        let parameter_value =
                            self.graph.intern_expr(ExprNode::Argument(argument))?;
                        let inspections = inspected.entry(current).or_insert_with(|| {
                            self.graph.items(body.inspections).copied().collect()
                        });
                        if inspections.contains(&parameter_value) {
                            if !chain.is_empty() {
                                let map = tcx.sess.source_map();
                                let links = chain.into_iter().map(|hop: Consumer| {
                                    let file = map.lookup_source_file(hop.span.lo());
                                    if !map.ensure_source_file_source_present(&file) {
                                        return None;
                                    }
                                    let mut origin = hop.source(tcx, context.sources);
                                    origin.label.message = format!(
                                        "`{}` receives the same optional value",
                                        diagnostics::item(tcx, hop.def)
                                    );
                                    Some(origin)
                                });
                                let Some(chain) = links.collect::<Option<Vec<_>>>() else {
                                    break;
                                };
                                findings.push((
                                    local,
                                    states::Finding {
                                        span,
                                        evidence: CompilerEvidence::OptionBoundary {
                                            parameter: parameter.clone(),
                                            chain,
                                        },
                                    },
                                ));
                            }
                            break;
                        }
                        if crate::sequence::Sequences::len(self.graph.as_ref(), body.returns) != 1 {
                            break;
                        }
                        let Some(returned) =
                            crate::sequence::Sequences::get(self.graph.as_ref(), body.returns, 0)
                                .copied()
                        else {
                            unreachable!("a singleton return exists")
                        };
                        let ExprNode::Call(target, values, _) = self.graph[returned.value] else {
                            break;
                        };
                        let Some(callee) = target.definition(self.graph) else {
                            break;
                        };
                        let BehaviorNode::Calls(calls) = body.behavior else {
                            break;
                        };
                        if self.graph.sole_function(calls) != Some(callee)
                            || crate::sequence::Sequences::len(self.graph.as_ref(), body.loops) != 0
                            || crate::sequence::Sequences::len(
                                self.graph.as_ref(),
                                body.requirements,
                            ) != 0
                        {
                            break;
                        }
                        let positions = forwarded.entry(current).or_insert_with(|| {
                            let mut positions = FxHashMap::default();
                            let arguments = self.graph.items(values).enumerate();
                            for (index, value) in arguments {
                                positions.entry(*value).or_insert(index);
                            }
                            positions
                        });
                        let Some(&position) = positions.get(&parameter_value) else {
                            break;
                        };
                        let Some(origin_span) =
                            diagnostics::source_span(tcx, callee, tcx.def_span(callee))
                        else {
                            break;
                        };
                        chain.push(Consumer {
                            def: callee,
                            span: origin_span,
                            operation: Operation::Condition,
                        });
                        current = callee;
                        argument = position;
                    }
                }
                let Some(indices) = candidates.get(&def) else {
                    continue;
                };
                if !indices.contains(&index) {
                    continue;
                }
                let Some(callers) = &callers else {
                    continue;
                };
                let Some(sites) = callers.complete(tcx, def) else {
                    continue;
                };
                let mut location = def.as_local().map(|local| (local, span));
                let mut supplied = None;
                let mut call_sites = Vec::new();
                let mut complete = Some(());
                for (caller, call) in sites {
                    let guards = self.resolve_guards(&call.guards)?;
                    if self
                        .graph
                        .conjunction(&guards, &crate::sequence::Sequence::EMPTY)?
                        == Truth::Refuted
                    {
                        continue;
                    }
                    let value = match crate::sequence::Sequences::get(
                        self.graph.as_ref(),
                        call.arguments,
                        index,
                    )
                    .copied()
                    {
                        Some(value) => self.resolve_expression(value, &guards)?,
                        None => self.graph.intern_expr(ExprNode::Unknown)?,
                    };
                    let alternative = match &self.graph[value] {
                        ExprNode::Number(0) if ty.is_bool() => Some(Alternative::False),
                        ExprNode::Number(_) if ty.is_bool() => Some(Alternative::True),
                        ExprNode::Variant(owner, variant, _) => Some(Alternative::Variant(
                            tcx.adt_def(*owner).variants()
                                [rustc_abi::VariantIdx::from_usize(*variant)]
                            .def_id,
                        )),
                        _ => None,
                    };
                    match (&supplied, alternative) {
                        (None, Some(value)) => supplied = Some(value),
                        (Some(previous), Some(value)) if previous == &value => {}
                        _ => complete = None,
                    }
                    if let Some(call_span) = diagnostics::source_span(tcx, *caller, call.span) {
                        if let (None, Some(local)) = (&location, caller.as_local()) {
                            location = Some((local, call_span));
                        }
                        call_sites.push(Consumer {
                            def: *caller,
                            span: call.span,
                            operation: Operation::Condition,
                        });
                    } else {
                        complete = None;
                    }
                }
                if let (Some(()), Some(supplied), Some((local, finding_span))) =
                    (complete, supplied, location)
                    && !call_sites.is_empty()
                {
                    if let Alternative::Variant(variant) = supplied
                        && Some(variant) == tcx.lang_items().option_some_variant()
                        && def.is_local()
                    {
                        let editable = editable_options.get_or_insert_with(|| {
                            crate::hir_rules::editable_option_parameters(tcx, &candidates)
                        });
                        let Some(wrappers) =
                            editable.get(&def).and_then(|params| params.get(&index))
                        else {
                            continue;
                        };
                        let Some(span) = diagnostics::source_span(tcx, def, ident.span) else {
                            continue;
                        };
                        let mut callers = Vec::new();
                        for &wrapper in wrappers {
                            let mut caller = Consumer {
                                def: tcx.hir_enclosing_body_owner(wrapper).to_def_id(),
                                span: tcx.hir_span(wrapper),
                                operation: Operation::Condition,
                            }
                            .source(tcx, context.sources);
                            caller.label.message =
                                format!("remove this Some wrapper for `{parameter}`");
                            callers.push(caller);
                        }
                        callers.sort_by_key(|caller| {
                            (caller.input.name.clone(), caller.label.span.start)
                        });
                        callers.dedup_by(|a, b| {
                            a.input.name == b.input.name && a.label.span == b.label.span
                        });
                        if !callers.is_empty() {
                            findings.push((
                                local,
                                states::Finding {
                                    span,
                                    evidence: CompilerEvidence::UnnecessaryOptionality {
                                        parameter,
                                        callers,
                                    },
                                },
                            ));
                        }
                        continue;
                    }
                    let mut callers: Vec<_> = call_sites
                        .into_iter()
                        .map(|site| site.source(tcx, context.sources))
                        .collect();
                    if !def.is_local() {
                        let file = tcx.sess.source_map().lookup_source_file(span.lo());
                        if !tcx
                            .sess
                            .source_map()
                            .ensure_source_file_source_present(&file)
                        {
                            continue;
                        }
                        let mut declaration = Consumer {
                            def,
                            span,
                            operation: Operation::Condition,
                        }
                        .source(tcx, context.sources);
                        declaration.label.message = format!(
                            "`{parameter}` is declared in `{}`",
                            diagnostics::item(tcx, def)
                        );
                        callers.push(declaration);
                    }
                    callers
                        .sort_by_key(|caller| (caller.input.name.clone(), caller.label.span.start));
                    let supplied = match supplied {
                        Alternative::False => false.to_string(),
                        Alternative::True => true.to_string(),
                        Alternative::Variant(variant) => tcx.item_name(variant).to_string(),
                    };
                    findings.push((
                        local,
                        states::Finding {
                            span: finding_span,
                            evidence: CompilerEvidence::UnusedCapability {
                                parameter,
                                supplied,
                                callers,
                            },
                        },
                    ));
                }
            }
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
