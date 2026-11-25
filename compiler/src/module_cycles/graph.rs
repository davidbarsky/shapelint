use std::collections::{VecDeque, hash_map::Entry};
use std::sync::Arc;

use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexMap};
use rustc_data_structures::graph::{scc::Sccs, vec_graph::VecGraph};
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_middle::ty::TyCtxt;
use shapelint::{CompilerEvidence, CompilerFinding, Config, Label, Related, lint_compiler};
use shapelint_driver::{diagnostics, pipeline::SourceFindings};

use crate::module_cycles::references::{References, Site};

pub(crate) struct Graph {
    names: Vec<String>,
    edges: VecGraph<usize>,
    sites: FxHashMap<(usize, usize), Site>,
}

impl Graph {
    pub(crate) fn collect(tcx: TyCtxt<'_>) -> Self {
        let mut modules = Vec::new();
        let crate_name = tcx.crate_name(LOCAL_CRATE);
        tcx.hir_for_each_module(|module| {
            let path = tcx
                .def_path(module.to_def_id())
                .to_string_no_crate_verbose();
            modules.push((format!("{crate_name}{path}"), module));
        });
        modules.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        let (names, modules): (Vec<_>, Vec<_>) = modules.into_iter().unzip();
        let indices: FxHashMap<_, _> = modules.iter().copied().zip(0..).collect();
        let paths: Vec<Vec<usize>> = modules
            .into_iter()
            .map(|mut module| {
                let mut path = Vec::new();
                while !module.is_top_level_module() {
                    path.push(indices[&module]);
                    module = tcx.parent_module_from_def_id(module.to_local_def_id());
                }
                path.reverse();
                path
            })
            .collect();

        let mut sites = FxHashMap::<_, Site>::default();
        for ((from, to), site) in References::collect(tcx) {
            // The first differing children share a parent. Exhausting either
            // path means the reference stayed in one branch.
            let siblings = paths[indices[&from]]
                .iter()
                .zip(&paths[indices[&to]])
                .find(|(left, right)| left != right);
            if let Some((&left, &right)) = siblings {
                let earliest = sites.entry((left, right)).or_insert(site);
                if (site.span.lo(), site.span.hi()) < (earliest.span.lo(), earliest.span.hi()) {
                    *earliest = site;
                }
            }
        }
        let edges = VecGraph::new(names.len(), sites.keys().copied().collect());
        Self {
            names,
            edges,
            sites,
        }
    }

    pub(crate) fn baseline(&self) -> Vec<Vec<&str>> {
        let groups = self.groups();
        groups
            .into_iter()
            .map(|group| {
                group
                    .into_iter()
                    .map(|id| self.names[id].as_str())
                    .collect()
            })
            .collect()
    }

    fn groups(&self) -> Vec<Vec<usize>> {
        let components = Sccs::<usize, usize>::new(&self.edges);
        let mut groups = vec![Vec::new(); components.num_sccs()];
        for node in 0..self.names.len() {
            groups[components.scc(node)].push(node);
        }
        groups.retain(|members| members.len() > 1);
        groups.sort_unstable();
        groups
    }

    // Shortest closed path through the first member. VecGraph visits successors
    // in index order, so equal-length witnesses are resolved by module name.
    fn witness(&self, members: &[usize]) -> Vec<(usize, usize)> {
        let start = members[0];
        let mut queue = VecDeque::from([start]);
        let mut parents = FxHashMap::default();
        while let Some(node) = queue.pop_front() {
            for &next in self.edges.successors(node) {
                if next == start {
                    let mut path = vec![(node, start)];
                    let mut child = node;
                    while child != start {
                        let parent = parents[&child];
                        path.push((parent, child));
                        child = parent;
                    }
                    path.reverse();
                    return path;
                }
                if let Ok(_) = members.binary_search(&next)
                    && let Entry::Vacant(entry) = parents.entry(next)
                {
                    entry.insert(node);
                    queue.push_back(next);
                }
            }
        }
        unreachable!("every member of a nontrivial strongly connected component lies on a cycle")
    }

    pub(crate) fn reports(
        &self,
        tcx: TyCtxt<'_>,
        accepted: &[FxHashSet<String>],
    ) -> Result<Vec<SourceFindings>, shapelint::LintError> {
        let sources = diagnostics::Sources::default();
        let mut files = FxIndexMap::default();
        for group in self.groups() {
            if accepted
                .iter()
                .any(|old| group.iter().all(|&id| old.contains(&self.names[id])))
            {
                continue;
            }
            let (file, finding) = self.evidence(tcx, &sources, &group)?;
            let (_, evidence) = files
                .entry(file.start_pos)
                .or_insert_with(|| (file, Vec::new()));
            evidence.push(finding);
        }
        let mut reports = Vec::new();
        for (file, evidence) in files.into_values() {
            let input = sources.input(&file)?;
            let findings = lint_compiler(&input, &Config::default(), &evidence)?;
            if !findings.is_empty() {
                reports.push(SourceFindings { input, findings });
            }
        }
        Ok(reports)
    }

    fn evidence(
        &self,
        tcx: TyCtxt<'_>,
        sources: &diagnostics::Sources,
        members: &[usize],
    ) -> Result<(Arc<rustc_span::SourceFile>, CompilerFinding), shapelint::LintError> {
        let map = tcx.sess.source_map();
        let witness = self.witness(members);
        let mut links = witness.into_iter().map(|(from, to)| {
            let Site { span, owner } = self.sites[&(from, to)];
            let file = map.lookup_source_file(span.lo());
            let label = Label {
                span: shapelint::Span {
                    start: file.original_relative_byte_pos(span.lo()).0,
                    end: file.original_relative_byte_pos(span.hi()).0,
                },
                message: format!("{} uses {}", self.names[from], self.names[to]),
            };
            (owner, file, label)
        });
        let (owner, file, first) = links.next().expect("a cycle has a first edge");
        let item_span = tcx.hir_span_with_body(owner.into()).source_callsite();
        let item_span = if file.contains(item_span.lo()) && file.contains(item_span.hi()) {
            shapelint::Span {
                start: file.original_relative_byte_pos(item_span.lo()).0,
                end: file.original_relative_byte_pos(item_span.hi()).0,
            }
        } else {
            first.span
        };
        let return_path = links
            .map(|(_, file, label)| {
                Ok(Related {
                    input: sources.input(&file)?,
                    label,
                })
            })
            .collect::<Result<_, shapelint::LintError>>()?;
        let evidence = CompilerFinding {
            item: diagnostics::item(tcx, owner.to_def_id()),
            item_span,
            span: first.span,
            evidence: CompilerEvidence::ModuleCycle {
                members: members.iter().map(|&id| self.names[id].clone()).collect(),
                first_edge: first.message,
                return_path,
            },
        };
        Ok((file, evidence))
    }
}
