pub mod artifacts;
pub mod report;

use crate::analysis::Analysis;
use crate::callers::CallIndex;
use crate::contracts::graph::{CapacityError, Graph};
use crate::pipeline::report::evaluator::{Evaluator, ReportDemand, RequirementReport};
use crate::{Located, diagnostics, regions};
use rustc_data_structures::fx::FxHashMap;
use rustc_hir::def_id::LocalDefId;
use rustc_index::IndexVec;
use rustc_span::{BytePos, Span};
use shapelint::CompilerEvidence;

pub struct Summaries<'g> {
    pub definitions: rustc_data_structures::fx::FxHashMap<
        rustc_hir::def_id::DefId,
        crate::contracts::summaries::SummaryId<'g>,
    >,
    pub coverage: rustc_data_structures::fx::FxHashSet<rustc_hir::def_id::CrateNum>,
}

impl<'g> Summaries<'g> {
    pub fn link(analyses: &[Analysis<'g>], imported: artifacts::Imported<'g>) -> Self {
        let mut summaries = Self::from(imported);
        summaries.definitions.extend(
            analyses
                .iter()
                .map(|analysis| (analysis.def.to_def_id(), analysis.contracts)),
        );
        summaries
    }
}

pub fn evaluate_crate<'g>(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    graph: &mut Graph<'g>,
    summaries: &Summaries<'g>,
) -> Result<crate::contracts::Work, CapacityError> {
    let definitions = &summaries.definitions;
    let calls = CallIndex::try_new(tcx, definitions, graph)?;
    let mut ordered: Vec<_> = definitions.iter().map(|(&def, &id)| (def, id)).collect();
    ordered.sort_by_cached_key(|&(def, _)| (tcx.def_span(def).lo(), tcx.def_path_hash(def)));
    let mut evaluator = Evaluator::try_new(tcx, &ordered, graph, &calls)?;
    for &(def, _) in &ordered {
        for (span, mut cursor) in
            evaluator.resolve_requirements(def, ReportDemand::LocalFindings)?
        {
            while let Some(requirement) = evaluator.next_requirement(&mut cursor)? {
                if let RequirementReport::Pending(id) = requirement {
                    evaluator.report_requirement(&mut cursor, id, span)?;
                }
            }
        }
    }
    Ok(evaluator.finish_work())
}

pub struct SourceFindings {
    pub input: shapelint::SourceInput,
    pub findings: Vec<shapelint::Finding>,
}

impl SourceFindings {
    pub fn collect(
        tcx: rustc_middle::ty::TyCtxt<'_>,
        source_inputs: &crate::diagnostics::Sources,
        config: &shapelint::Config,
        local: Vec<Located>,
    ) -> Result<Vec<Self>, shapelint::LintError> {
        let map = tcx.sess.source_map();
        let mut spans: Vec<_> = tcx
            .iter_local_def_id()
            .map(|def| tcx.def_span(def))
            .collect();
        tcx.hir_for_each_module(|module| {
            spans.push(tcx.hir_get_module(module).0.spans.inner_span);
        });
        let mut files = rustc_data_structures::fx::FxIndexMap::default();
        for span in spans {
            if span.is_dummy() {
                continue;
            }
            let file = map.lookup_source_file(span.lo());
            if file.is_imported() {
                continue;
            }
            let name = file.name.prefer_local_unconditionally().to_string();
            if let Some(shapelint::Language::Rust) = shapelint::Language::of(&name) {
                files.entry(file.start_pos).or_insert((file, Vec::new()));
            }
        }
        for crate::Located {
            def,
            item_span,
            span,
            evidence,
        } in crate::hir_rules::findings(tcx)
            .into_iter()
            .chain(crate::architecture::findings(tcx, source_inputs)?)
            .chain(local)
        {
            let Some(span) = crate::diagnostics::source_span(tcx, def.to_def_id(), span) else {
                continue;
            };
            let item_span = item_span.source_callsite();
            let file = map.lookup_source_file(span.lo());
            if file.is_imported() {
                continue;
            }
            let item_span = match (file.contains(item_span.lo()), file.contains(item_span.hi())) {
                (true, true) => item_span,
                _ => span,
            };
            let finding = shapelint::CompilerFinding {
                item: crate::diagnostics::item(tcx, def.to_def_id()),
                item_span: shapelint::Span {
                    start: file.original_relative_byte_pos(item_span.lo()).0,
                    end: file.original_relative_byte_pos(item_span.hi()).0,
                },
                span: shapelint::Span {
                    start: file.original_relative_byte_pos(span.lo()).0,
                    end: file.original_relative_byte_pos(span.hi()).0,
                },
                evidence,
            };
            let (_, findings) = files
                .entry(file.start_pos)
                .or_insert_with(|| (file, Vec::new()));
            findings.push(finding);
        }
        let mut inputs = Vec::new();
        let mut evidence = Vec::new();
        for (file, findings) in files.into_values() {
            inputs.push(source_inputs.input(file.as_ref())?);
            evidence.push(findings);
        }
        let findings = shapelint::lint_sources(&inputs, config)?;
        let mut sources = Vec::with_capacity(inputs.len());
        for ((input, evidence), mut findings) in inputs.into_iter().zip(evidence).zip(findings) {
            findings.extend(shapelint::lint_compiler(&input, config, &evidence)?);
            findings.sort_by_key(|finding| finding.primary.span);
            sources.push(Self { input, findings });
        }
        Ok(sources)
    }
}

/// The source spans emitted by `regions::candidates` are nested or disjoint.
/// Keep active ancestors on a stack and index their matched source spans by
/// original owner instead of rescanning every ancestor for each candidate.
#[doc(hidden)]
pub struct CoveredIndex {
    active: Vec<ActiveCovered>,
    owners: FxHashMap<LocalDefId, TreeId>,
    trees: IndexVec<TreeId, ContainmentTree>,
}

rustc_index::newtype_index! {
    #[max = 0xffff_ffff]
    struct TreeId {}
}

#[derive(Clone, Copy)]
struct ActiveCovered {
    tree: TreeId,
    key: (BytePos, usize),
    outer: Span,
}

#[derive(Default)]
struct ContainmentTree {
    root: Option<Box<ContainmentNode>>,
    comparisons: usize,
}

struct ContainmentNode {
    key: (BytePos, usize),
    high: BytePos,
    maximum_high: BytePos,
    maximum_key: (BytePos, usize),
    priority: u64,
    left: Option<Box<ContainmentNode>>,
    right: Option<Box<ContainmentNode>>,
}

impl Default for CoveredIndex {
    fn default() -> Self {
        Self {
            active: Vec::new(),
            owners: FxHashMap::default(),
            trees: IndexVec::new(),
        }
    }
}

impl CoveredIndex {
    /// Expires source ancestors that no longer contain the next candidate.
    pub fn advance(&mut self, next: Span) {
        while let Some(active) = self.active.last().copied() {
            let touching_empty = active.outer.hi() == next.lo() && next.lo() == next.hi();
            if active.outer.hi() > next.lo() || touching_empty {
                break;
            }
            self.active.pop();
            let tree = &mut self.trees[active.tree];
            tree.root = remove_node(tree.root.take(), active.key);
        }
    }

    // shapelint: allow(shallow-helper) The owner map is the containment index boundary.
    /// Finds the greatest original end covering a candidate span for one owner.
    pub fn covering_end(&mut self, owner: LocalDefId, span: Span) -> Option<BytePos> {
        let tree = *self.owners.get(&owner)?;
        self.trees[tree].covering_end(span)
    }

    /// Adds one source ancestor and its original span to the owner index.
    pub fn insert(&mut self, owner: LocalDefId, outer: Span, original_outer: Span) {
        let tree = *self
            .owners
            .entry(owner)
            .or_insert_with(|| self.trees.push(ContainmentTree::default()));
        let key = self.trees[tree].insert(original_outer, self.active.len());
        self.active.push(ActiveCovered { tree, key, outer });
    }

    // shapelint: allow(shallow-helper) The work counter is an explicit audit observation.
    /// Returns the number of containment-tree nodes inspected for one owner.
    pub fn comparisons(&self, owner: LocalDefId) -> usize {
        self.owners
            .get(&owner)
            .map_or(0, |&tree| self.trees[tree].comparisons)
    }
}

impl ContainmentTree {
    fn insert(&mut self, span: Span, depth: usize) -> (BytePos, usize) {
        let key = (span.lo(), depth);
        let node = Box::new(ContainmentNode {
            key,
            high: span.hi(),
            maximum_high: span.hi(),
            maximum_key: key,
            priority: priority(key.1),
            left: None,
            right: None,
        });
        self.root = insert_node(self.root.take(), node);
        key
    }

    fn covering_end(&mut self, span: Span) -> Option<BytePos> {
        let Some(high) = max_prefix(&self.root, span.lo(), &mut self.comparisons) else {
            return None;
        };
        match high >= span.hi() {
            true => Some(high),
            false => None,
        }
    }
}

fn priority(id: usize) -> u64 {
    let mut value = (id as u64).wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn update_maximum(node: &mut ContainmentNode) {
    node.maximum_high = node
        .high
        .max(
            node.left
                .as_ref()
                .map_or(node.high, |child| child.maximum_high),
        )
        .max(
            node.right
                .as_ref()
                .map_or(node.high, |child| child.maximum_high),
        );
    node.maximum_key = node
        .right
        .as_ref()
        .map_or(node.key, |right| right.maximum_key);
}

// shapelint: allow(option-plumbing) Recursive treap splitting owns optional child subtrees.
fn split_node(
    node: Option<Box<ContainmentNode>>,
    key: (BytePos, usize),
) -> (Option<Box<ContainmentNode>>, Option<Box<ContainmentNode>>) {
    let Some(mut node) = node else {
        return (None, None);
    };
    if node.key < key {
        let (left, right) = split_node(node.right.take(), key);
        node.right = left;
        update_maximum(&mut node);
        (Some(node), right)
    } else {
        let (left, right) = split_node(node.left.take(), key);
        node.left = right;
        update_maximum(&mut node);
        (left, Some(node))
    }
}

// shapelint: allow(option-plumbing) Recursive treap merging owns optional child subtrees.
fn merge_nodes(
    left: Option<Box<ContainmentNode>>,
    right: Option<Box<ContainmentNode>>,
) -> Option<Box<ContainmentNode>> {
    match (left, right) {
        (None, right) => right,
        (left, None) => left,
        (Some(mut left), Some(right)) if left.priority >= right.priority => {
            left.right = merge_nodes(left.right.take(), Some(right));
            update_maximum(&mut left);
            Some(left)
        }
        (Some(left), Some(mut right)) => {
            right.left = merge_nodes(Some(left), right.left.take());
            update_maximum(&mut right);
            Some(right)
        }
    }
}

// shapelint: allow(option-plumbing) Recursive treap insertion owns optional roots.
fn insert_node(
    root: Option<Box<ContainmentNode>>,
    node: Box<ContainmentNode>,
) -> Option<Box<ContainmentNode>> {
    let Some(mut root) = root else {
        return Some(node);
    };
    if node.priority > root.priority {
        let (left, right) = split_node(Some(root), node.key);
        let mut node = node;
        node.left = left;
        node.right = right;
        update_maximum(&mut node);
        Some(node)
    } else if node.key < root.key {
        root.left = insert_node(root.left.take(), node);
        update_maximum(&mut root);
        Some(root)
    } else {
        root.right = insert_node(root.right.take(), node);
        update_maximum(&mut root);
        Some(root)
    }
}

// shapelint: allow(option-plumbing) Recursive treap removal owns optional roots.
fn remove_node(
    root: Option<Box<ContainmentNode>>,
    key: (BytePos, usize),
) -> Option<Box<ContainmentNode>> {
    let Some(mut root) = root else {
        return None;
    };
    if key == root.key {
        merge_nodes(root.left.take(), root.right.take())
    } else if key < root.key {
        root.left = remove_node(root.left.take(), key);
        update_maximum(&mut root);
        Some(root)
    } else {
        root.right = remove_node(root.right.take(), key);
        update_maximum(&mut root);
        Some(root)
    }
}

fn max_prefix(
    node: &Option<Box<ContainmentNode>>,
    low: BytePos,
    comparisons: &mut usize,
) -> Option<BytePos> {
    let Some(node) = node else {
        return None;
    };
    *comparisons = comparisons.saturating_add(1);
    if node.maximum_key.0 <= low {
        return Some(node.maximum_high);
    }
    if node.key.0 > low {
        return max_prefix(&node.left, low, comparisons);
    }
    let left_max = node.left.as_ref().map(|left| left.maximum_high);
    let right_max = max_prefix(&node.right, low, comparisons);
    Some(node.high).max(left_max).max(right_max)
}

#[derive(Debug, thiserror::Error)]
pub enum LocalError {
    #[error(transparent)]
    Regions(#[from] regions::matching::Error),
    #[error(transparent)]
    Source(#[from] shapelint::LintError),
}

pub fn local_findings(
    mut analyses: Vec<Analysis<'_>>,
    tcx: rustc_middle::ty::TyCtxt<'_>,
    source_inputs: &diagnostics::Sources,
) -> Result<Vec<Located>, LocalError> {
    analyses.sort_by_key(|analysis| analysis.span.lo());
    let mut evidence = Vec::new();
    let map = tcx.sess.source_map();
    regions::matching::with_matcher(|originals| -> Result<(), LocalError> {
        for Analysis {
            def,
            span,
            regions,
            findings,
            ..
        } in analyses
        {
            if let Some(regions::Captured {
                body,
                mut candidates,
            }) = regions
            {
                candidates
                    .sort_by_key(|region| (region.span.lo(), std::cmp::Reverse(region.span.hi())));
                let body = originals.register(body)?;
                let mut covered = CoveredIndex::default();
                for region in candidates {
                    if let None = diagnostics::source_span(tcx, def.to_def_id(), region.span) {
                        continue;
                    }
                    covered.advance(region.span);
                    let (original_def, original_span) = match originals.insert(body, region)? {
                        None => continue,
                        Some(original) => (original.owner, original.span),
                    };
                    // Nested regions covered by the same larger match add no review evidence.
                    // Source spans are an ancestor stack here, so `covering_end` only needs the
                    // original-span containment index for this matched owner.
                    if let Some(_) = covered.covering_end(original_def, original_span) {
                        continue;
                    }
                    if def == original_def
                        && (region.span.contains(original_span)
                            || original_span.contains(region.span))
                    {
                        continue;
                    }
                    covered.insert(original_def, region.span, original_span);
                    let original_span = original_span.source_callsite();
                    let original_file = map.lookup_source_file(original_span.lo());
                    let input = source_inputs.input(original_file.as_ref())?;
                    evidence.push(Located {
                        def,
                        item_span: span,
                        span: region.span,
                        evidence: CompilerEvidence::Duplicate {
                            original: shapelint::Related {
                                input,
                                label: shapelint::Label {
                                    span: shapelint::Span {
                                        start: original_file
                                            .original_relative_byte_pos(original_span.lo())
                                            .0,
                                        end: original_file
                                            .original_relative_byte_pos(original_span.hi())
                                            .0,
                                    },
                                    message: format!(
                                        "implementation in `{}`",
                                        diagnostics::item(tcx, original_def.to_def_id())
                                    ),
                                },
                            },
                        },
                    });
                }
            }

            for finding in findings {
                evidence.push(Located {
                    def,
                    item_span: span,
                    span: finding.span,
                    evidence: finding.evidence,
                });
            }
        }
        Ok(())
    })?;
    Ok(evidence)
}
