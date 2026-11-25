use rustc_hir::def_id::DefId;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::sym;

use crate::contracts::graph::{
    CapacityError, ConditionId, ConditionNode, ExprId, ExprNode, Graph, TextMatchNode, TokenNode,
};
use crate::contracts::{Arithmetic, Order};
use crate::states::{Method, method};

pub(crate) fn call<'tcx, 'g>(
    tcx: TyCtxt<'tcx>,
    def: DefId,
    arguments: &[ExprId<'g>],
    receiver: ty::Ty<'tcx>,
    types: &[ty::Ty<'tcx>],
    graph: &mut Graph<'g>,
) -> Result<Option<(ExprId<'g>, Vec<ConditionId<'g>>)>, CapacityError> {
    macro_rules! required {
        ($value:expr) => {
            match $value {
                Some(value) => value,
                None => return Ok(None),
            }
        };
    }
    let receiver = receiver.peel_refs();
    let first = *required!(arguments.first());
    if let ty::Uint(_) = receiver.kind()
        && !def.is_local()
        && let Some(owner) = tcx.inherent_impl_of_assoc(def)
        && tcx
            .type_of(owner)
            .instantiate_identity()
            .skip_normalization()
            == receiver
    {
        let size = receiver.int_size_and_signed(tcx).0;
        match tcx.item_name(def).as_str() {
            "wrapping_sub" => {
                let value = graph.intern_expr(ExprNode::Arithmetic(
                    Arithmetic::WrappingSubtract(size.bits()),
                    first,
                    *required!(arguments.get(1)),
                ))?;
                return Ok(Some((value, Vec::new())));
            }
            method @ ("ilog2" | "checked_ilog2") => {
                let result = match graph[first] {
                    ExprNode::Number(bits) => bits
                        .checked_ilog2()
                        .map(|log| ExprNode::Number(u128::from(log))),
                    _ => Some(ExprNode::Range(crate::contracts::Interval {
                        lower: 0,
                        upper: u128::from(size.unsigned_int_max().ilog2()),
                    })),
                };
                let zero = graph.intern_expr(ExprNode::Number(0))?;
                let nonzero =
                    graph.intern_condition(ConditionNode::Compare(Order::NotEqual, first, zero))?;
                if method == "ilog2" {
                    let value = graph.intern_expr(match result {
                        Some(value) => value,
                        None => ExprNode::Unknown,
                    })?;
                    return Ok(Some((value, vec![nonzero])));
                }
                let option = required!(tcx.get_diagnostic_item(sym::Option));
                let none = graph.intern_expr(ExprNode::Variant(
                    option,
                    0,
                    crate::sequence::Sequence::EMPTY,
                ))?;
                let Some(value) = result else {
                    return Ok(Some((none, Vec::new())));
                };
                let value = graph.intern_expr(value)?;
                let fields = graph.push(crate::sequence::Sequence::EMPTY, value)?;
                let some = graph.intern_expr(ExprNode::Variant(option, 1, fields))?;
                let value = graph.intern_expr(ExprNode::Select(nonzero, some, none))?;
                return Ok(Some((value, Vec::new())));
            }
            _ => {}
        }
    }
    if !def.is_local() && tcx.def_path_str(def) == "rustc_lexer::tokenize" {
        let consumed = graph.intern_expr(ExprNode::Number(0))?;
        let value = graph.intern_expr(ExprNode::Tokens {
            text: first,
            consumed,
        })?;
        let length = graph.intern_expr(ExprNode::Length(first))?;
        let maximum = graph.intern_expr(ExprNode::Number(u128::from(u32::MAX)))?;
        let requirement =
            graph.intern_condition(ConditionNode::Compare(Order::LessEqual, length, maximum))?;
        return Ok(Some((value, vec![requirement])));
    }

    if let Some(method) = method(tcx, def) {
        match method {
            Method::Extract(required) => {
                let value = graph.field(graph.downcast(first, required.index()), 0)?;
                let requirement =
                    graph.intern_condition(ConditionNode::Variant(first, required.index()))?;
                return Ok(Some((value, vec![requirement])));
            }
            Method::Predicate(required) => {
                let condition =
                    graph.intern_condition(ConditionNode::Variant(first, required.index()))?;
                let value = graph.intern_expr(ExprNode::Test(condition))?;
                return Ok(Some((value, Vec::new())));
            }
            Method::Borrow => return Ok(Some((first, Vec::new()))),
            Method::Take | Method::Replace => return Ok(Some((first, Vec::new()))),
            Method::VecPush => return Ok(None),
        }
    }
    if tcx.is_diagnostic_item(rustc_span::Symbol::intern("str_len"), def)
        || tcx.lang_items().slice_len_fn() == Some(def)
    {
        return Ok(Some((
            graph.intern_expr(ExprNode::Length(first))?,
            Vec::new(),
        )));
    }
    if receiver.is_str()
        && !def.is_local()
        && let Some(owner) = tcx.inherent_impl_of_assoc(def)
        && tcx
            .type_of(owner)
            .instantiate_identity()
            .skip_normalization()
            .is_str()
    {
        match tcx.item_name(def).as_str() {
            "trim_start" => {
                return Ok(Some((
                    graph.intern_expr(ExprNode::Trimmed(first))?,
                    Vec::new(),
                )));
            }
            "match_indices" if required!(types.get(1)).peel_refs().is_str() => {
                let value = graph.intern_expr(ExprNode::Matches {
                    text: first,
                    pattern: *required!(arguments.get(1)),
                })?;
                return Ok(Some((value, Vec::new())));
            }
            "find"
                if required!(types.get(1)).peel_refs().is_str()
                    || required!(types.get(1)).is_char() =>
            {
                let value = graph.intern_expr(ExprNode::Found {
                    text: first,
                    pattern: *required!(arguments.get(1)),
                })?;
                return Ok(Some((value, Vec::new())));
            }
            _ => {}
        }
    }
    if receiver.is_str()
        && !def.is_local()
        && tcx.item_name(def).as_str() == "is_char_boundary"
        && let Some(owner) = tcx.impl_of_assoc(def)
        && tcx
            .type_of(owner)
            .instantiate_identity()
            .skip_normalization()
            .is_str()
    {
        let condition =
            graph.intern_condition(ConditionNode::Boundary(first, *required!(arguments.get(1))))?;
        return Ok(Some((
            graph.intern_expr(ExprNode::Test(condition))?,
            Vec::new(),
        )));
    }
    let trait_def = tcx.trait_of_assoc(def).or_else(|| {
        tcx.opt_associated_item(def)
            .and_then(|item| item.trait_item_def_id())
            .and_then(|item| tcx.trait_of_assoc(item))
    });

    if trait_def == tcx.lang_items().clone_trait()
        && tcx.item_name(def).as_str() == "clone"
        && !def.is_local()
        && let ty::Adt(adt, _) = receiver.kind()
        && tcx.lang_items().string() == Some(adt.did())
    {
        return Ok(Some((first, Vec::new())));
    }

    if let ExprNode::Tokens { text, consumed } = graph[first]
        && let Some(trait_def) = trait_def
    {
        if tcx.is_diagnostic_item(sym::IntoIterator, trait_def) {
            return Ok(Some((first, Vec::new())));
        }
        if tcx.is_diagnostic_item(sym::Iterator, trait_def) && tcx.item_name(def).as_str() == "next"
        {
            let length = graph.intern_expr(ExprNode::Unknown)?;
            let value = graph.intern_expr(ExprNode::NextToken(TokenNode {
                text,
                start: consumed,
                length,
            }))?;
            return Ok(Some((value, Vec::new())));
        }
    }
    if let ExprNode::Matches { text, pattern } = graph[first]
        && let Some(trait_def) = trait_def
    {
        if tcx.is_diagnostic_item(sym::IntoIterator, trait_def) {
            return Ok(Some((first, Vec::new())));
        }
        if tcx.is_diagnostic_item(sym::Iterator, trait_def) && tcx.item_name(def).as_str() == "next"
        {
            let occurrence = graph.intern_expr(ExprNode::Unknown)?;
            let value = graph.intern_expr(ExprNode::MatchEntry(TextMatchNode {
                text,
                pattern,
                occurrence,
            }))?;
            return Ok(Some((value, Vec::new())));
        }
    }
    if receiver.is_slice()
        && !def.is_local()
        && tcx.item_name(def).as_str() == "partition_point"
        && let Some(owner) = tcx.inherent_impl_of_assoc(def)
        && tcx
            .type_of(owner)
            .instantiate_identity()
            .skip_normalization()
            .is_slice()
    {
        let value = graph.intern_expr(ExprNode::Partition {
            sequence: first,
            predicate: *required!(arguments.get(1)),
        })?;
        return Ok(Some((value, Vec::new())));
    }
    enum Sequence {
        Elements,
        Text,
    }
    let sequence = match receiver.kind() {
        ty::Str => Sequence::Text,
        ty::Slice(_) | ty::Array(..) => Sequence::Elements,
        ty::Adt(adt, _) if tcx.is_diagnostic_item(sym::Vec, adt.did()) => Sequence::Elements,
        ty::Adt(adt, _) if tcx.lang_items().string() == Some(adt.did()) => Sequence::Text,
        _ => return Ok(None),
    };
    if trait_def == tcx.lang_items().deref_trait() {
        return Ok(Some((first, Vec::new())));
    }
    if !def.is_local()
        && let Some(owner) = tcx.impl_of_assoc(def)
    {
        let owner = tcx
            .type_of(owner)
            .instantiate_identity()
            .skip_normalization();
        if let ty::Adt(adt, _) = owner.kind()
            && (tcx.is_diagnostic_item(sym::Vec, adt.did())
                || tcx.lang_items().string() == Some(adt.did()))
        {
            match (tcx.item_name(def).as_str(), trait_def) {
                ("len", None) => {
                    return Ok(Some((
                        graph.intern_expr(ExprNode::Length(first))?,
                        Vec::new(),
                    )));
                }
                ("as_slice" | "as_str", None) => return Ok(Some((first, Vec::new()))),
                (_, Some(trait_def)) if Some(trait_def) == tcx.lang_items().deref_trait() => {
                    return Ok(Some((first, Vec::new())));
                }
                _ => {}
            }
        }
    }
    if trait_def != tcx.lang_items().index_trait()
        && trait_def != tcx.lang_items().index_mut_trait()
    {
        return Ok(None);
    }
    let index = required!(types.get(1));
    let second = *required!(arguments.get(1));
    let length = graph.intern_expr(ExprNode::Length(first))?;
    let mut requirements = Vec::new();
    let result;
    match *index.kind() {
        ty::Uint(_) => {
            result = graph.intern_expr(ExprNode::Element(first, second))?;
            requirements.push(graph.intern_condition(ConditionNode::Compare(
                Order::Less,
                second,
                length,
            ))?);
        }
        ty::Adt(adt, _) => {
            let (start, end) = if tcx.lang_items().range_struct() == Some(adt.did()) {
                (graph.field(second, 0)?, graph.field(second, 1)?)
            } else if tcx.lang_items().range_from_struct() == Some(adt.did()) {
                (graph.field(second, 0)?, length)
            } else if tcx.lang_items().range_to_struct() == Some(adt.did()) {
                (
                    graph.intern_expr(ExprNode::Number(0))?,
                    graph.field(second, 0)?,
                )
            } else if tcx.lang_items().range_full_struct() == Some(adt.did()) {
                (graph.intern_expr(ExprNode::Number(0))?, length)
            } else {
                return Ok(None);
            };
            result = graph.intern_expr(ExprNode::Slice {
                text: first,
                start,
                end,
            })?;
            requirements.push(graph.intern_condition(ConditionNode::Compare(
                Order::LessEqual,
                start,
                end,
            ))?);
            requirements.push(graph.intern_condition(ConditionNode::Compare(
                Order::LessEqual,
                end,
                length,
            ))?);
            match sequence {
                Sequence::Text => {
                    requirements
                        .push(graph.intern_condition(ConditionNode::Boundary(first, start))?);
                    requirements.push(graph.intern_condition(ConditionNode::Boundary(first, end))?);
                }
                Sequence::Elements => {}
            }
        }
        _ => return Ok(None),
    }
    Ok(Some((result, requirements)))
}
