use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_middle::mir::visit::{PlaceContext, Visitor};
use rustc_middle::mir::{
    Body, Local, Location, Operand, Place, RETURN_PLACE, Rvalue, StatementKind,
};
use rustc_middle::ty::{self, TyCtxt};

#[derive(Default)]
struct Places(FxHashSet<Local>);

impl<'tcx> Visitor<'tcx> for Places {
    fn visit_place(&mut self, place: &Place<'tcx>, context: PlaceContext, location: Location) {
        self.0.insert(place.local);
        self.super_place(place, context, location);
    }
}

pub struct Demand(FxHashSet<Location>);

impl Demand {
    pub fn new<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> Self {
        let mut roots = Places::default();
        roots.0.insert(RETURN_PLACE);
        let mut dependencies: FxHashMap<Local, Vec<Local>> = FxHashMap::default();
        let mut candidates = Vec::new();
        for (block, data) in body.basic_blocks.iter_enumerated() {
            let statements = data.statements.iter().enumerate();
            for (statement_index, statement) in statements {
                let location = Location {
                    block,
                    statement_index,
                };
                match &statement.kind {
                    StatementKind::Assign(assignment) => {
                        let mut uses = Places::default();
                        uses.visit_rvalue(&assignment.1, location);
                        if let Some(local) = pure_scalar(tcx, body, assignment.0, &assignment.1) {
                            dependencies.entry(local).or_default().extend(uses.0);
                            candidates.push((location, local));
                        } else {
                            roots.0.insert(assignment.0.local);
                            roots.0.extend(uses.0);
                            roots.visit_place(
                                &assignment.0,
                                PlaceContext::MutatingUse(
                                    rustc_middle::mir::visit::MutatingUseContext::Store,
                                ),
                                location,
                            );
                        }
                    }
                    _ => roots.visit_statement(statement, location),
                }
            }
            roots.visit_terminator(
                data.terminator(),
                Location {
                    block,
                    statement_index: data.statements.len(),
                },
            );
        }
        let mut pending: Vec<_> = roots.0.iter().copied().collect();
        while let Some(local) = pending.pop() {
            if let Some(uses) = dependencies.remove(&local) {
                for used in uses {
                    if roots.0.insert(used) {
                        pending.push(used);
                    }
                }
            }
        }
        Self(
            candidates
                .into_iter()
                .filter_map(|(location, local)| match roots.0.contains(&local) {
                    true => None,
                    false => Some(location),
                })
                .collect(),
        )
    }

    pub fn assignment(&self, location: Location) -> Option<()> {
        match self.0.contains(&location) {
            true => None,
            false => Some(()),
        }
    }
}

fn pure_scalar<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    place: Place<'tcx>,
    value: &Rvalue<'tcx>,
) -> Option<Local> {
    if !place.projection.is_empty() || place.local.index() <= body.arg_count {
        return None;
    }
    match place.ty(&body.local_decls, tcx).ty.kind() {
        ty::Bool | ty::Char | ty::Int(_) | ty::Uint(_) | ty::Float(_) => {}
        _ => return None,
    }
    let copy = |operand: &Operand<'tcx>| match operand {
        Operand::Copy(place) if place.projection.is_empty() => Some(()),
        Operand::Constant(_) => Some(()),
        Operand::Copy(_) | Operand::Move(_) | Operand::RuntimeChecks(_) => None,
    };
    match value {
        Rvalue::Use(operand, _) | Rvalue::UnaryOp(_, operand) => copy(operand)?,
        Rvalue::BinaryOp(_, operands) => {
            copy(&operands.0)?;
            copy(&operands.1)?;
        }
        _ => return None,
    }
    Some(place.local)
}
