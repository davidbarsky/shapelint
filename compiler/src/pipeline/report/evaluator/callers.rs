use rustc_data_structures::fx::FxHashSet;
use rustc_hir::def_id::DefId;
use rustc_span::Span;

use crate::contracts::CheckBasis;
use crate::contracts::graph::summaries::CallNode;
use crate::contracts::graph::{
    ArgumentContextId, CapacityError, ExprNode, GuardContextId, TargetNode,
};
use crate::pipeline::report::evaluator::{Answer, Evaluator, Query, schedule};

impl<'a, 'tcx, 'g> Evaluator<'a, 'tcx, 'g> {
    pub fn resolved_calls(
        &mut self,
        owners: &FxHashSet<DefId>,
        descend: &FxHashSet<DefId>,
    ) -> Result<Vec<(DefId, CallNode<'g>)>, CapacityError> {
        let roots: Vec<_> = self
            .definitions
            .iter()
            .filter(|(owner, _)| owners.contains(owner))
            .flat_map(|&(owner, summary)| {
                self.graph
                    .items(self.graph[summary].calls)
                    .copied()
                    .map(move |call| (owner, call))
            })
            .collect();
        enum Visit<'g> {
            Root(DefId, Span, CallNode<'g>),
            Call(DefId, Span, CallNode<'g>),
            Leave(DefId),
        }
        let mut pending = Vec::new();
        let mut output = Vec::new();
        let mut visited = FxHashSet::default();
        let mut active = FxHashSet::default();
        for (owner, call) in roots {
            let span = call.span;
            let query = Query::Materialized(
                call.target,
                ArgumentContextId::from(call.arguments),
                GuardContextId::from(call.guards),
                match &call.basis {
                    CheckBasis::Expression => CheckBasis::Expression,
                    CheckBasis::ControlFlow(basis) => {
                        CheckBasis::ControlFlow(GuardContextId::from(*basis))
                    }
                },
                call.span,
            );
            let Answer::Calls(calls) = schedule::evaluate(self, query)?.value else {
                unreachable!("materialized query result")
            };
            for call in self.graph.scan(calls) {
                if let TargetNode::Direct(callable) = call.target {
                    self.recursion.insert(owner, self.graph[callable].def)?;
                }
                pending.push(Visit::Root(owner, span, call));
            }
        }
        while let Some(visit) = pending.pop() {
            let (owner, span, call) = match visit {
                Visit::Root(owner, span, call) => {
                    active.insert(owner);
                    pending.push(Visit::Leave(owner));
                    (owner, span, call)
                }
                Visit::Call(owner, span, call) => (owner, span, call),
                Visit::Leave(def) => {
                    active.remove(&def);
                    continue;
                }
            };
            output.push((owner, CallNode { span, ..call }));
            let TargetNode::Direct(callable) = call.target else {
                continue;
            };
            let callee = self.graph[callable].def;
            if !descend.contains(&callee) {
                continue;
            }
            let mut arguments = crate::sequence::Sequence::EMPTY;
            let mut input = self.graph.scan(call.arguments);
            while let Some(argument) = input.next() {
                let argument = self.graph.provenance(argument)?;
                arguments = self.graph.push(arguments, argument)?;
            }
            if let None =
                self.graph
                    .items(arguments)
                    .find(|argument| match &self.graph[**argument] {
                        ExprNode::Unknown => false,
                        _ => true,
                    })
            {
                continue;
            }
            if !active.insert(callee) {
                let unknown = self.graph.intern_expr(ExprNode::Unknown)?;
                output.push((
                    owner,
                    CallNode {
                        basis: call.basis,
                        target: TargetNode::Indirect(unknown),
                        arguments,
                        guards: crate::sequence::Sequence::EMPTY,
                        span,
                    },
                ));
                continue;
            }
            pending.push(Visit::Leave(callee));
            if !visited.insert((owner, span, callable, arguments, call.basis)) {
                continue;
            }
            self.work.caller_expansions = self.work.caller_expansions.saturating_add(1);
            let arguments = ArgumentContextId::from(arguments);
            let Answer::Calls(calls) =
                schedule::evaluate(self, Query::Contextual(callable, arguments))?.value
            else {
                unreachable!("contextual query result")
            };
            for mut nested in self.graph.scan(calls) {
                nested.basis = self.graph.combine_bases(&call.basis, &nested.basis)?;
                pending.push(Visit::Call(owner, span, nested));
            }
        }
        Ok(output)
    }
}
