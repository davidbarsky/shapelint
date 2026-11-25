use crate::contracts::graph::{CapacityError, Graph};
use crate::contracts::summaries::SummaryId;
use rustc_hir::def_id::LocalDefId;
use rustc_middle::mir::{Body, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;
use rustc_span::{Span, Symbol};

use crate::states;

pub struct Session {
    graph: Graph<'static>,
    analyses: std::sync::Mutex<Vec<Analysis<'static>>>,
}

impl Session {
    pub fn new() -> Self {
        Self {
            graph: Graph::new(),
            analyses: std::sync::Mutex::new(Vec::new()),
        }
    }

    pub fn capture<'tcx>(
        &self,
        tcx: TyCtxt<'tcx>,
        def: LocalDefId,
        body: &Body<'tcx>,
        protocols: &[Symbol],
        sources: &crate::diagnostics::Sources,
    ) -> Result<(), Error> {
        let mut graph = self.graph.fork();
        let analysis = analyze(tcx, def, body, &mut graph, protocols, sources)?;
        match self.analyses.lock() {
            Ok(mut analyses) => analyses.push(analysis),
            Err(error) => tcx
                .dcx()
                .fatal(format!("shapelint analysis collection: {error}")),
        }
        Ok(())
    }

    pub fn finish<R>(
        &self,
        tcx: TyCtxt<'_>,
        f: impl for<'g> FnOnce(&mut Graph<'g>, Vec<Analysis<'g>>) -> R,
    ) -> R {
        let analyses = match self.analyses.lock() {
            Ok(mut analyses) => std::mem::take(&mut *analyses),
            Err(error) => tcx
                .dcx()
                .fatal(format!("shapelint analysis collection: {error}")),
        };
        let mut graph = self.graph.fork();
        f(&mut graph, analyses)
    }
}

impl Default for Session {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Capacity(#[from] CapacityError),
}

pub struct Analysis<'g> {
    pub def: LocalDefId,
    pub span: Span,
    pub contracts: SummaryId<'g>,
    pub findings: Vec<states::Finding>,
    pub invariants: Vec<states::Invariant>,
    pub constructions: Vec<states::Construction>,
    pub work: states::Work,
}

pub fn analyze<'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
    body: &Body<'tcx>,
    graph: &mut Graph<'g>,
    protocols: &[Symbol],
    sources: &crate::diagnostics::Sources,
) -> Result<Analysis<'g>, Error> {
    let mut body = body.clone();
    for block in body.basic_blocks.as_mut() {
        // False edges belong to borrow checking. Both analyses use this one execution graph,
        // retaining unwind, coroutine-drop, and resume edges.
        if let TerminatorKind::FalseEdge { real_target, .. }
        | TerminatorKind::FalseUnwind { real_target, .. } = block.terminator().kind
        {
            block.terminator_mut().kind = TerminatorKind::Goto {
                target: real_target,
            };
        }
        block.statements.retain(|statement| match statement.kind {
            StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::FakeRead(_)
            | StatementKind::AscribeUserType(..)
            | StatementKind::Coverage(_)
            | StatementKind::ConstEvalCounter
            | StatementKind::Nop
            | StatementKind::BackwardIncompatibleDropHint { .. } => false,
            StatementKind::Assign(_)
            | StatementKind::SetDiscriminant { .. }
            | StatementKind::PlaceMention(_)
            | StatementKind::Intrinsic(_) => true,
        });
    }
    let states::Capture { observations, work } =
        states::analyze(tcx, &body, graph, protocols, sources)?;
    let states::Observations {
        writes: _,
        contracts,
        findings,
        invariants,
        constructions,
    } = observations;
    let contracts = graph.freeze(contracts)?;
    let analysis = Analysis {
        def,
        span: tcx.def_span(tcx.typeck_root_def_id(def.to_def_id())),
        contracts,
        findings,
        invariants,
        constructions,
        work,
    };
    Ok(analysis)
}
