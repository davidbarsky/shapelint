pub mod artifacts;
pub(crate) mod report;

use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_index::IndexVec;
use rustc_middle::ty::TyCtxt;
use rustc_span::{BytePos, Span};
use shapelint::{
    CompilerEvidence, CompilerFinding, Config, Finding, Language, LintError, SourceInput,
    lint_compiler, lint_sources,
};

use crate::contracts::graph::Graph;
use crate::{analysis, architecture, callers, contracts, diagnostics, hir_rules, regions, states};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Source(#[from] LintError),
    #[error(transparent)]
    Capacity(#[from] contracts::graph::CapacityError),
    #[error(transparent)]
    Regions(#[from] regions::matching::Error),
}

pub use crate::diagnostics::Located;

struct Local {
    def: LocalDefId,
    span: Span,
    regions: Option<regions::Captured>,
    findings: Vec<states::Finding>,
    invariants: Vec<states::Invariant>,
    constructions: Vec<states::Construction>,
}

pub struct Collected<'g> {
    analyses: Vec<Local>,
    summaries: FxHashMap<DefId, crate::contracts::summaries::SummaryId<'g>>,
}

pub struct Linked<'g> {
    analyses: Vec<Local>,
    summaries: Summaries<'g>,
}

pub struct Summaries<'g> {
    pub definitions: FxHashMap<DefId, crate::contracts::summaries::SummaryId<'g>>,
    pub coverage: FxHashSet<rustc_hir::def_id::CrateNum>,
}

pub struct Analyzed<'g> {
    summaries: Summaries<'g>,
    sources: Vec<SourceFindings>,
    pub work: contracts::Work,
}

pub struct SourceFindings {
    pub input: SourceInput,
    pub findings: Vec<Finding>,
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

impl<'g> From<Vec<analysis::Analysis<'g>>> for Collected<'g> {
    fn from(mut analyses: Vec<analysis::Analysis<'g>>) -> Self {
        analyses.sort_by_key(|analysis| analysis.span.lo());
        let mut summaries = FxHashMap::default();
        let mut locals = Vec::new();
        for analysis::Analysis {
            def,
            span,
            regions,
            contracts,
            findings,
            invariants,
            constructions,
            work: _,
        } in analyses
        {
            summaries.insert(def.to_def_id(), contracts);
            locals.push(Local {
                def,
                span,
                regions,
                findings,
                invariants,
                constructions,
            });
        }
        locals.sort_by_key(|analysis| analysis.span.lo());
        Self {
            analyses: locals,
            summaries,
        }
    }
}

impl<'g> Collected<'g> {
    pub fn link(self, imported: artifacts::Imported<'g>) -> Linked<'g> {
        let Self {
            analyses,
            mut summaries,
        } = self;
        let Summaries {
            definitions: imported,
            coverage,
        } = Summaries::from(imported);
        summaries.extend(imported);
        Linked {
            analyses,
            summaries: Summaries {
                definitions: summaries,
                coverage,
            },
        }
    }
}

impl<'g> AsRef<Summaries<'g>> for Linked<'g> {
    fn as_ref(&self) -> &Summaries<'g> {
        &self.summaries
    }
}

impl<'g> AsRef<Summaries<'g>> for Analyzed<'g> {
    fn as_ref(&self) -> &Summaries<'g> {
        &self.summaries
    }
}

/// Selects whether unresolved and unsupported checks are included in the report.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum AnalysisGaps {
    #[default]
    Hide,
    Show,
}

impl<'g> Linked<'g> {
    pub fn analyze(
        self,
        tcx: TyCtxt<'_>,
        graph: &mut Graph<'g>,
        scope: callers::Scope,
        gaps: AnalysisGaps,
        config: &Config,
        source_inputs: &diagnostics::Sources,
    ) -> Result<Analyzed<'g>, Error> {
        let contracts::Analysis { findings, work } =
            report::findings(tcx, &self.summaries, graph, scope, gaps, source_inputs)?;
        let Self {
            analyses,
            summaries,
        } = self;
        let mut variant_sites = FxHashSet::default();
        for analysis in analyses.iter() {
            for finding in &analysis.findings {
                match &finding.evidence {
                    CompilerEvidence::InvalidVariant { .. }
                    | CompilerEvidence::UnencodedInvariant { .. } => {
                        variant_sites.insert((analysis.def, finding.span));
                    }
                    _ => {}
                }
            }
        }
        let mut evidence: Vec<_> = findings
            .into_iter()
            .filter_map(|(def, finding)| {
                match &finding.evidence {
                    CompilerEvidence::InvalidPrecondition { .. }
                    | CompilerEvidence::UnprovenPrecondition { .. }
                        if variant_sites.contains(&(def, finding.span)) =>
                    {
                        return None;
                    }
                    _ => {}
                }
                Some(Located {
                    def,
                    item_span: tcx.def_span(tcx.typeck_root_def_id(def.to_def_id())),
                    span: finding.span,
                    evidence: finding.evidence,
                })
            })
            .collect();
        let mut invariants = FxHashMap::default();
        let mut constructions = Vec::new();
        let map = tcx.sess.source_map();
        regions::matching::with_matcher(|originals| -> Result<(), Error> {
            for Local {
                def,
                span,
                regions,
                findings,
                invariants: local_invariants,
                constructions: local_constructions,
            } in analyses
            {
                if let Some(regions::Captured {
                    body,
                    mut candidates,
                }) = regions
                {
                    candidates.sort_by_key(|region| {
                        (region.span.lo(), std::cmp::Reverse(region.span.hi()))
                    });
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
                for invariant in local_invariants {
                    invariants
                        .entry((invariant.owner, invariant.field))
                        .or_insert_with(Vec::new)
                        .push((def, invariant));
                }
                constructions.extend(
                    local_constructions
                        .into_iter()
                        .map(|construction| (def, span, construction)),
                );
            }
            Ok(())
        })?;
        let mut reported = FxHashSet::default();
        for (def, item_span, construction) in constructions {
            for (field, actual) in &construction.fields {
                let states::Fact::Variant(actual) = actual else {
                    continue;
                };
                let Some(invariants) = invariants.get(&(construction.owner, *field)) else {
                    continue;
                };
                for (consumer, invariant) in invariants {
                    if let None =
                        diagnostics::source_span(tcx, consumer.to_def_id(), invariant.span)
                    {
                        continue;
                    }
                    if *actual == invariant.required {
                        continue;
                    }
                    if let Some(_) = invariant
                        .guards
                        .iter()
                        .find(|(index, fact)| construction.fields.get(index) != Some(fact))
                    {
                        continue;
                    }
                    if !reported.insert((def, *consumer, invariant.span)) {
                        continue;
                    }
                    let guard = invariant
                        .guards
                        .iter()
                        .map(|(index, fact)| {
                            states::describe(tcx, construction.owner.definition, *index, *fact)
                        })
                        .collect::<Vec<_>>()
                        .join(" and ");
                    let actual = states::describe(
                        tcx,
                        construction.owner.definition,
                        invariant.field,
                        states::Fact::Variant(*actual),
                    );
                    let required = states::describe(
                        tcx,
                        construction.owner.definition,
                        invariant.field,
                        states::Fact::Variant(invariant.required),
                    );
                    let location = map.lookup_char_pos(invariant.span.lo());
                    evidence.push(Located {
                        def,
                        item_span,
                        span: construction.span,
                        evidence: CompilerEvidence::InconsistentConstruction {
                            assumption: format!(
                                "returned {guard} and {actual}; consumer requires {required}"
                            ),
                            consumer: format!(
                                "{} at {}:{}",
                                diagnostics::item(tcx, consumer.to_def_id()),
                                location.file.name.prefer_local_unconditionally(),
                                location.line
                            ),
                        },
                    });
                }
            }
        }
        evidence.extend(hir_rules::findings(tcx));
        evidence.extend(architecture::findings(tcx, source_inputs)?);
        evidence.sort_by_key(|finding| finding.span.lo());
        let mut sources = FxIndexMap::default();
        let mut spans: Vec<_> = tcx
            .iter_local_def_id()
            .map(|def| tcx.def_span(def))
            .collect();
        tcx.hir_for_each_module(|module| {
            spans.push(tcx.hir_get_module(module).0.spans.inner_span);
        });
        for span in spans {
            if span.is_dummy() {
                continue;
            }
            let file = map.lookup_source_file(span.lo());
            if file.is_imported() {
                continue;
            }
            let name = file.name.prefer_local_unconditionally().to_string();
            if let Some(Language::Rust) = Language::of(&name) {
                sources.entry(file.start_pos).or_insert((file, Vec::new()));
            }
        }
        for Located {
            def,
            item_span,
            span,
            evidence,
        } in evidence
        {
            let Some(span) = diagnostics::source_span(tcx, def.to_def_id(), span) else {
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
            let finding = CompilerFinding {
                item: diagnostics::item(tcx, def.to_def_id()),
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
            let (_, findings) = sources
                .entry(file.start_pos)
                .or_insert_with(|| (file, Vec::new()));
            findings.push(finding);
        }
        let mut inputs = Vec::new();
        let mut evidence = Vec::new();
        for (_, (file, findings)) in sources {
            let input = source_inputs.input(file.as_ref())?;
            inputs.push(input);
            evidence.push(findings);
        }
        let findings = lint_sources(&inputs, config)?;
        let sources = inputs.into_iter().zip(evidence).zip(findings);
        let mut analyzed = Vec::new();
        for ((input, evidence), mut findings) in sources {
            findings.extend(lint_compiler(&input, config, &evidence)?);
            findings.sort_by_key(|finding| finding.primary.span);
            analyzed.push(SourceFindings { input, findings });
        }
        Ok(Analyzed {
            summaries,
            sources: analyzed,
            work,
        })
    }
}

impl IntoIterator for Analyzed<'_> {
    type Item = SourceFindings;
    type IntoIter = std::vec::IntoIter<SourceFindings>;

    fn into_iter(self) -> Self::IntoIter {
        self.sources.into_iter()
    }
}

impl AsRef<[SourceFindings]> for Analyzed<'_> {
    fn as_ref(&self) -> &[SourceFindings] {
        &self.sources
    }
}
