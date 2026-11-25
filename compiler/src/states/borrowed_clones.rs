use crate::contracts::{Consumer, Operation};
use crate::{diagnostics, states};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{
    Body, Local, Location, Operand, Place, Rvalue, StatementKind, TerminatorKind,
};
use rustc_middle::ty::{self, TyCtxt};
use shapelint::CompilerEvidence;

enum CloneStorage {
    Buffer,
    Handle,
}

#[derive(Default)]
struct LocalUses {
    locations: Vec<Location>,
    definitions: usize,
}

#[derive(Default)]
struct Uses {
    locals: FxHashMap<Local, LocalUses>,
    visits: usize,
}

impl<'tcx> Visitor<'tcx> for Uses {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        if let PlaceContext::NonUse(_) = context {
            return;
        }
        self.visits = self.visits.saturating_add(1);
        let uses = self.locals.entry(place.local).or_default();
        if let PlaceContext::MutatingUse(
            rustc_middle::mir::visit::MutatingUseContext::Store
            | rustc_middle::mir::visit::MutatingUseContext::Call,
        ) = context
        {
            uses.definitions += 1;
        }
        uses.locations.push(location);
        self.super_place(place, context, location);
    }
}

enum CloneOrigin {
    Visiting,
    Resolved(Option<Local>),
}

#[derive(Default)]
struct Origins(FxHashMap<Local, CloneOrigin>);

impl Origins {
    fn resolve(
        &mut self,
        mut local: Local,
        body: &Body<'_>,
        uses: &Uses,
        work: &mut states::Work,
    ) -> Option<Local> {
        let mut path = Vec::new();
        let origin = loop {
            work.clone_origin_lookups = work.clone_origin_lookups.saturating_add(1);
            if local.index() <= body.arg_count {
                break match local.index() {
                    0 => None,
                    _ => Some(local),
                };
            }
            match self.0.get(&local) {
                Some(CloneOrigin::Resolved(origin)) => break *origin,
                Some(CloneOrigin::Visiting) => break None,
                None => {}
            }
            self.0.insert(local, CloneOrigin::Visiting);
            path.push(local);
            let Some(uses) = uses.locals.get(&local) else {
                break None;
            };
            let mut definitions = uses.locations.iter().filter_map(|location| {
                work.clone_origin_lookups = work.clone_origin_lookups.saturating_add(1);
                let statement = body.basic_blocks[location.block]
                    .statements
                    .get(location.statement_index)?;
                match &statement.kind {
                    StatementKind::Assign(assignment) if assignment.0.local == local => {
                        Some(&assignment.1)
                    }
                    _ => None,
                }
            });
            match (definitions.next(), definitions.next()) {
                (Some(Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, place)), None)
                | (Some(Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)), None) => {
                    local = place.local
                }
                _ => break None,
            }
        };
        for local in path {
            self.0.insert(local, CloneOrigin::Resolved(origin));
        }
        origin
    }
}

pub fn borrowed_clones<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    sources: &crate::diagnostics::Sources,
    work: &mut states::Work,
) -> Vec<states::Finding> {
    let mut uses = Uses::default();
    uses.visit_body(body);
    work.clone_use_visits = work.clone_use_visits.saturating_add(uses.visits);
    let mut origins = Origins::default();
    let mut call_count = None;
    let mut findings = Vec::new();
    let blocks = body.basic_blocks.iter_enumerated();
    for (block, data) in blocks {
        let TerminatorKind::Call {
            func,
            args,
            destination,
            ..
        } = &data.terminator().kind
        else {
            continue;
        };
        let ty::FnDef(def, _) = func.ty(&body.local_decls, tcx).kind() else {
            continue;
        };
        let owner = tcx.trait_of_assoc(*def).or_else(|| {
            tcx.trait_impl_of_assoc(*def)
                .and_then(|owner| tcx.impl_opt_trait_id(owner))
        });
        if owner != tcx.lang_items().clone_trait() {
            continue;
        }
        let [argument] = args.as_ref() else { continue };
        let ty::Ref(_, receiver, rustc_hir::Mutability::Not) =
            argument.node.ty(&body.local_decls, tcx).kind()
        else {
            continue;
        };
        let ty::Adt(adt, generic) = receiver.kind() else {
            continue;
        };
        let diagnostic_name = match tcx.get_diagnostic_name(adt.did()) {
            Some(name) => Some(name),
            None if tcx.lang_items().string() == Some(adt.did()) => Some(rustc_span::sym::String),
            None => None,
        };
        let permitted = match diagnostic_name.as_ref().map(|name| name.as_str()) {
            Some("String") => Some(CloneStorage::Buffer),
            Some("Arc" | "Rc") if generic.type_at(0).is_freeze(tcx, body.typing_env(tcx)) => {
                Some(CloneStorage::Handle)
            }
            Some("Vec")
                if generic.type_at(0).is_integral()
                    || generic.type_at(0).is_bool()
                    || generic.type_at(0).is_char() =>
            {
                Some(CloneStorage::Buffer)
            }
            _ => None,
        };
        let Some(storage) = permitted else { continue };
        let Some(source) = argument.node.place() else {
            continue;
        };
        let Some(source) = origins.resolve(source.local, body, &uses, work) else {
            continue;
        };
        // A shared, frozen input cannot change while its cloned buffer is being read.
        work.clone_argument_lookups = work.clone_argument_lookups.saturating_add(1);
        match body.local_decls[source].ty.kind() {
            ty::Ref(_, inner, rustc_hir::Mutability::Not) => match storage {
                CloneStorage::Buffer if inner.is_freeze(tcx, body.typing_env(tcx)) => {}
                CloneStorage::Handle if *inner == *receiver => {}
                CloneStorage::Buffer | CloneStorage::Handle => continue,
            },
            _ => continue,
        }
        let creation = Location {
            block,
            statement_index: data.statements.len(),
        };
        let mut pending = vec![destination.local];
        let mut visited = FxHashSet::default();
        let mut reads = Vec::new();
        let mut calls = FxHashSet::from_iter([block]);
        let mut supported = Some(());
        while let Some(local) = pending.pop() {
            if !visited.insert(local) {
                continue;
            }
            if local.index() == 0 {
                supported = None;
                break;
            }
            let Some(uses) = uses.locals.get(&local) else {
                supported = None;
                break;
            };
            if uses.definitions != 1 {
                supported = None;
                break;
            }
            for location in &uses.locations {
                if *location == creation {
                    continue;
                }
                let data = &body.basic_blocks[location.block];
                if let Some(statement) = data.statements.get(location.statement_index) {
                    match &statement.kind {
                        StatementKind::Assign(assignment) => match &assignment.1 {
                            Rvalue::Ref(_, rustc_middle::mir::BorrowKind::Shared, place)
                                if place.local == local =>
                            {
                                pending.push(assignment.0.local)
                            }
                            Rvalue::Use(Operand::Copy(place) | Operand::Move(place), _)
                                if place.local == local && body.local_decls[local].ty.is_ref() =>
                            {
                                pending.push(assignment.0.local)
                            }
                            _ if assignment.0.local == local && local != destination.local => {}
                            _ => supported = None,
                        },
                        StatementKind::PlaceMention(_) => {}
                        _ => supported = None,
                    }
                } else {
                    match &data.terminator().kind {
                        TerminatorKind::Drop { place, .. } if place.local == local => {}
                        TerminatorKind::Call {
                            func,
                            args,
                            destination,
                            ..
                        } => {
                            if destination.local == local {
                                continue;
                            }
                            let ty::FnDef(callee, _) = func.ty(&body.local_decls, tcx).kind()
                            else {
                                supported = None;
                                continue;
                            };
                            let [argument] = args.as_ref() else {
                                supported = None;
                                continue;
                            };
                            if argument.node.place().map(|place| place.local) != Some(local) {
                                supported = None;
                                continue;
                            }
                            if callee.is_local()
                                || !["alloc", "core"]
                                    .contains(&tcx.crate_name(callee.krate).as_str())
                            {
                                supported = None;
                                continue;
                            }
                            calls.insert(location.block);
                            let name = tcx.item_name(*callee);
                            let receiver = argument.node.ty(&body.local_decls, tcx).peel_refs();
                            let owner = match receiver.kind() {
                                ty::Adt(adt, _) if tcx.lang_items().string() == Some(adt.did()) => {
                                    Some("String".into())
                                }
                                ty::Adt(adt, _) => tcx
                                    .get_diagnostic_name(adt.did())
                                    .map(|name| name.to_string()),
                                _ => None,
                            };
                            match (name.as_str(), owner.as_deref()) {
                                ("len" | "is_empty", Some("String" | "Vec")) => {
                                    reads.push(data.terminator().source_info.span)
                                }
                                ("deref", Some("String" | "Vec" | "Arc" | "Rc"))
                                    if !callee.is_local() =>
                                {
                                    pending.push(destination.local)
                                }
                                ("len" | "is_empty", _)
                                    if receiver.is_str() || receiver.is_slice() =>
                                {
                                    reads.push(data.terminator().source_info.span)
                                }
                                _ => supported = None,
                            }
                        }
                        _ => supported = None,
                    }
                }
            }
        }
        if let CloneStorage::Handle = storage {
            let total = *call_count.get_or_insert_with(|| {
                let mut count = 0;
                for data in body.basic_blocks.iter() {
                    work.clone_call_block_visits = work.clone_call_block_visits.saturating_add(1);
                    if let TerminatorKind::Call { .. } = data.terminator().kind {
                        count += 1;
                    }
                }
                count
            });
            work.clone_call_set_checks = work.clone_call_set_checks.saturating_add(1);
            // Every recorded block is a call in this body, so equal counts prove coverage.
            if calls.len() != total {
                supported = None;
            }
        }
        if let Some(()) = supported
            && !reads.is_empty()
        {
            let def = body.source.def_id();
            let span = data.terminator().source_info.span;
            if let None = diagnostics::source_span(tcx, def, span) {
                continue;
            }
            reads.sort_by_key(|span| span.lo());
            reads.dedup();
            let uses = reads
                .into_iter()
                .map(|span| {
                    let mut usage = Consumer {
                        def,
                        span,
                        operation: Operation::Condition,
                    }
                    .source(tcx, sources);
                    usage.label.message = "only reads through a shared borrow".into();
                    usage
                })
                .collect();
            findings.push(states::Finding {
                span,
                evidence: CompilerEvidence::BorrowedClone { uses },
            });
        }
    }
    findings
}
