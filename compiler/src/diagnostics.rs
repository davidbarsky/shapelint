use parking_lot::Mutex;
use rustc_data_structures::fx::FxHashMap;

use rustc_hir::def::DefKind;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::TyCtxt;

pub use crate::contracts::describe::{Condition, Description};

pub struct Finding {
    pub span: rustc_span::Span,
    pub evidence: shapelint::CompilerEvidence,
}

pub struct Located {
    pub def: rustc_hir::def_id::LocalDefId,
    pub item_span: rustc_span::Span,
    pub span: rustc_span::Span,
    pub evidence: shapelint::CompilerEvidence,
}

/// Shares source text and owner syntax indexes within one compiler session.
///
/// File identity includes the original content hash, so source maps with reused
/// positions or filenames cannot return another revision's text. Failed loads are
/// not retained: rustc may populate an external source later in the session.
#[derive(Default)]
pub struct Sources {
    inputs: Mutex<
        FxHashMap<
            (rustc_span::StableSourceFileId, rustc_span::SourceFileHash),
            shapelint::SourceInput,
        >,
    >,
    owners: Mutex<FxHashMap<rustc_hir::OwnerId, std::sync::Arc<OwnerSource>>>,
}

pub(crate) enum ExpressionKind {
    Binary,
    Other,
}

pub(crate) struct ExpressionName {
    pub(crate) expression_kind: ExpressionKind,
    span: rustc_span::Span,
    text: std::sync::OnceLock<String>,
}

#[derive(Clone, Copy)]
pub(crate) enum CheckPolarity {
    Direct,
    Negated,
}

#[derive(Clone, Copy)]
pub(crate) struct SourceCheck {
    pub span: rustc_span::Span,
    pub polarity: CheckPolarity,
}

pub(crate) struct OwnerSource {
    pub(crate) expressions: FxHashMap<rustc_span::Span, ExpressionName>,
    pub(crate) checks: FxHashMap<rustc_span::Span, SourceCheck>,
}

impl ExpressionName {
    pub(crate) fn text(&self, tcx: TyCtxt<'_>) -> &str {
        self.text.get_or_init(|| {
            match tcx
                .sess
                .source_map()
                .span_to_snippet(self.span.source_callsite())
            {
                Ok(text) => text,
                Err(error) => tcx
                    .dcx()
                    .fatal(format!("could not read expression source: {error:?}")),
            }
        })
    }
}

impl Sources {
    pub(crate) fn owner(
        &self,
        tcx: TyCtxt<'_>,
        owner: rustc_hir::OwnerId,
    ) -> std::sync::Arc<OwnerSource> {
        let nodes = tcx.hir_owner_nodes(owner);
        let mut owners = self.owners.lock();
        std::sync::Arc::clone(owners.entry(owner).or_insert_with(|| {
            let mut expressions = FxHashMap::default();
            let mut checks = FxHashMap::default();
            for node in nodes.nodes.iter() {
                let rustc_hir::Node::Expr(expression) = node.node else {
                    continue;
                };
                if expression.span.from_expansion() {
                    continue;
                }
                if let rustc_hir::ExprKind::If(condition, ..) = expression.kind
                    && !condition.span.from_expansion()
                {
                    let mut candidate = condition;
                    let mut polarity = CheckPolarity::Direct;
                    loop {
                        checks.insert(
                            candidate.span,
                            SourceCheck {
                                span: condition.span,
                                polarity,
                            },
                        );
                        match candidate.kind {
                            rustc_hir::ExprKind::Unary(rustc_hir::UnOp::Not, operand)
                                if !operand.span.from_expansion()
                                    && tcx.typeck(owner.def_id).expr_ty(operand).is_bool() =>
                            {
                                candidate = operand;
                                polarity = match polarity {
                                    CheckPolarity::Direct => CheckPolarity::Negated,
                                    CheckPolarity::Negated => CheckPolarity::Direct,
                                };
                            }
                            _ => break,
                        }
                    }
                }
                let expression_kind = match expression.kind {
                    rustc_hir::ExprKind::Binary(..) => ExpressionKind::Binary,
                    rustc_hir::ExprKind::Path(_)
                    | rustc_hir::ExprKind::Lit(_)
                    | rustc_hir::ExprKind::Field(..)
                    | rustc_hir::ExprKind::Index(..)
                    | rustc_hir::ExprKind::Call(..)
                    | rustc_hir::ExprKind::MethodCall(..)
                    | rustc_hir::ExprKind::Unary(..)
                    | rustc_hir::ExprKind::Cast(..)
                    | rustc_hir::ExprKind::AddrOf(..) => ExpressionKind::Other,
                    _ => continue,
                };
                expressions
                    .entry(expression.span)
                    .or_insert(ExpressionName {
                        expression_kind,
                        span: expression.span,
                        text: std::sync::OnceLock::new(),
                    });
            }
            std::sync::Arc::new(OwnerSource {
                expressions,
                checks,
            })
        }))
    }

    pub fn input(
        &self,
        file: &rustc_span::SourceFile,
    ) -> Result<shapelint::SourceInput, shapelint::LintError> {
        let mut inputs = self.inputs.lock();
        match inputs.entry((file.stable_id, file.src_hash)) {
            std::collections::hash_map::Entry::Occupied(entry) => Ok(entry.get().clone()),
            std::collections::hash_map::Entry::Vacant(entry) => {
                let input = shapelint::SourceInput::try_from(file)?;
                Ok(entry.insert(input).clone())
            }
        }
    }
}

pub fn source_span(
    tcx: TyCtxt<'_>,
    def: DefId,
    span: rustc_span::Span,
) -> Option<rustc_span::Span> {
    let mut owner = Some(def);
    let mut current = span;
    loop {
        for expansion in current.macro_backtrace() {
            match expansion.kind {
                rustc_span::hygiene::ExpnKind::Macro(..) => return None,
                rustc_span::hygiene::ExpnKind::Root
                | rustc_span::hygiene::ExpnKind::AstPass(_)
                | rustc_span::hygiene::ExpnKind::Desugaring(_) => {}
            }
        }
        let Some(def) = owner else { break };
        if tcx.is_automatically_derived(def) {
            return None;
        }
        current = tcx.def_span(def);
        owner = tcx.opt_parent(def);
    }
    Some(span.source_callsite())
}

pub fn operand(
    tcx: TyCtxt<'_>,
    body: &rustc_middle::mir::Body<'_>,
    operand: &rustc_middle::mir::Operand<'_>,
) -> Option<String> {
    let span = match operand {
        rustc_middle::mir::Operand::Copy(place) | rustc_middle::mir::Operand::Move(place) => {
            body.local_decls[place.local].source_info.span
        }
        rustc_middle::mir::Operand::Constant(value) => value.span,
        rustc_middle::mir::Operand::RuntimeChecks(_) => return None,
    };
    if span.is_dummy() {
        return None;
    }
    match tcx
        .sess
        .source_map()
        .span_to_snippet(span.source_callsite())
    {
        Ok(text) => Some(text),
        Err(error) => tcx
            .dcx()
            .fatal(format!("could not read operand source: {error:?}")),
    }
}

pub fn item(tcx: TyCtxt<'_>, def: DefId) -> String {
    enum Work {
        Item(DefId),
        Prefix(&'static str),
        Suffix(Vec<String>),
    }
    let mut pending = vec![Work::Item(def)];
    let mut result = String::new();
    let mut prefixes = Vec::new();
    while let Some(work) = pending.pop() {
        match work {
            Work::Prefix(prefix) => prefixes.push(prefix),
            Work::Suffix(mut parts) => {
                parts.reverse();
                if !parts.is_empty() {
                    result.push_str("::");
                    result.push_str(&parts.join("::"));
                }
            }
            Work::Item(def) => {
                match tcx.def_kind(def) {
                    DefKind::Closure | DefKind::SyntheticCoroutineBody => {
                        pending.push(Work::Prefix("closure in "));
                        pending.push(Work::Item(tcx.parent(def)));
                        continue;
                    }
                    DefKind::AnonConst => {
                        pending.push(Work::Prefix("constant in "));
                        pending.push(Work::Item(tcx.parent(def)));
                        continue;
                    }
                    _ => {}
                }
                let mut parts = Vec::new();
                let mut current = Some(def);
                while let Some(def) = current {
                    let Some(parent) = tcx.opt_parent(def) else {
                        break;
                    };
                    match tcx.def_kind(def) {
                        DefKind::Impl { .. } => {
                            parts.push(
                                tcx.type_of(def)
                                    .instantiate_identity()
                                    .skip_normalization()
                                    .to_string(),
                            );
                            break;
                        }
                        DefKind::Closure | DefKind::SyntheticCoroutineBody | DefKind::AnonConst => {
                            pending.push(Work::Suffix(std::mem::take(&mut parts)));
                            pending.push(Work::Item(def));
                            break;
                        }
                        _ => {
                            if let Some(name) = tcx.opt_item_name(def) {
                                parts.push(name.to_string());
                            }
                        }
                    }
                    current = Some(parent);
                }
                parts.reverse();
                result = parts.join("::");
            }
        }
    }
    prefixes.reverse();
    prefixes.push(&result);
    prefixes.concat()
}
