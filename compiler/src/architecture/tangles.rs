use std::collections::{VecDeque, hash_map::Entry};

use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_data_structures::graph::{scc::Sccs, vec_graph::VecGraph};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LOCAL_CRATE, LocalDefId};
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Body, Expr, ExprKind, HirId, Item, ItemKind, Node, Path, QPath};
use rustc_middle::hir::nested_filter::OnlyBodies;
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_span::Span;
use shapelint::{CompilerEvidence, LintError};

use crate::architecture::{Site, owner};
use crate::diagnostics::{self, Located, Sources};

// deslop-please's tangle rule also reports a single-module cycle above HELD_IN_MIND.
const HELD_IN_MIND: usize = 7;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
enum Boundary {
    AcrossModules,
    WithinModule,
}

#[derive(Clone, Copy)]
struct Edge {
    boundary: Boundary,
    site: Site,
}

struct Cycle {
    members: Vec<String>,
    first: (Site, String),
    return_path: Vec<(Site, String)>,
}

pub(crate) struct Tangles {
    components: FxHashMap<LocalDefId, usize>,
    cycles: Vec<Cycle>,
}

impl Tangles {
    pub(crate) fn common_component(&self, first: LocalDefId, second: LocalDefId) -> Option<usize> {
        let component = *self.components.get(&first)?;
        match self.components.get(&second) {
            Some(&other) if component == other => Some(component),
            _ => None,
        }
    }

    pub(crate) fn collect(tcx: TyCtxt<'_>) -> Self {
        let mut references = References {
            tcx,
            typeck: None,
            owners: FxHashMap::default(),
            edges: FxHashMap::default(),
        };
        tcx.hir_visit_all_item_likes_in_crate(&mut references);
        let defs: FxHashSet<_> = references.edges.keys().flat_map(|&(a, b)| [a, b]).collect();
        let crate_name = tcx.crate_name(LOCAL_CRATE);
        let mut items: Vec<_> = defs
            .into_iter()
            .map(|def| {
                let path = tcx.def_path(def.to_def_id()).to_string_no_crate_verbose();
                (format!("{crate_name}{path}"), def)
            })
            .collect();
        items.sort_unstable_by(|a, b| a.0.cmp(&b.0));
        let indices: FxHashMap<_, _> = items
            .iter()
            .enumerate()
            .map(|(i, (_, def))| (*def, i))
            .collect();
        let edges: FxHashMap<_, _> = references
            .edges
            .into_iter()
            .map(|((a, b), edge)| ((indices[&a], indices[&b]), edge))
            .collect();
        let graph = VecGraph::new(items.len(), edges.keys().copied().collect());
        let sccs = Sccs::<usize, usize>::new(&graph);
        let mut groups = vec![Vec::new(); sccs.num_sccs()];
        for item in 0..items.len() {
            groups[sccs.scc(item)].push(item);
        }

        let mut components = FxHashMap::default();
        let mut cycles = Vec::new();
        for members in groups {
            let [first, _, ..] = members.as_slice() else {
                continue;
            };
            let group = sccs.scc(*first);
            components.extend(members.iter().map(|&member| (items[member].1, group)));
            // Prefer a witness that actually crosses the reported boundary. A component
            // can also contain a shorter cycle wholly inside one of its modules.
            let first = members
                .iter()
                .flat_map(|&from| graph.successors(from).iter().map(move |&to| (from, to)))
                .filter(|&(_, to)| sccs.scc(to) == group)
                .min_by_key(|&pair| (edges[&pair].boundary, pair))
                .expect("a nontrivial strongly connected component contains an edge");
            if edges[&first].boundary == Boundary::WithinModule && members.len() <= HELD_IN_MIND {
                continue;
            }
            let label = |(a, b): (usize, usize)| {
                (
                    edges[&(a, b)].site,
                    format!("{} uses {}", items[a].0, items[b].0),
                )
            };
            cycles.push(Cycle {
                members: members
                    .into_iter()
                    .map(|index| items[index].0.clone())
                    .collect(),
                first: label(first),
                return_path: return_path(&graph, &sccs, first)
                    .into_iter()
                    .map(label)
                    .collect(),
            });
        }
        Self { components, cycles }
    }

    pub(crate) fn findings(
        &self,
        tcx: TyCtxt<'_>,
        sources: &Sources,
    ) -> Result<Vec<Located>, LintError> {
        self.cycles
            .iter()
            .map(|cycle| {
                let (site, first_edge) = &cycle.first;
                let return_path = cycle
                    .return_path
                    .iter()
                    .map(|(site, message)| site.related(tcx, sources, message.clone()))
                    .collect::<Result<_, _>>()?;
                let finding = Located {
                    def: site.def,
                    item_span: site.item_span(tcx),
                    span: site.span,
                    evidence: CompilerEvidence::Tangle {
                        members: cycle.members.clone(),
                        first_edge: first_edge.clone(),
                        return_path,
                    },
                };
                Ok(finding)
            })
            .collect()
    }
}

fn return_path(
    graph: &VecGraph<usize>,
    components: &Sccs<usize, usize>,
    (start, next): (usize, usize),
) -> Vec<(usize, usize)> {
    let group = components.scc(start);
    let mut queue = VecDeque::from([next]);
    let mut parents = FxHashMap::default();
    parents.insert(next, next);
    while let Some(from) = queue.pop_front() {
        for &to in graph.successors(from) {
            if components.scc(to) == group
                && let Entry::Vacant(entry) = parents.entry(to)
            {
                entry.insert(from);
                if to == start {
                    let mut path = Vec::new();
                    let mut node = start;
                    while node != next {
                        let parent = parents[&node];
                        path.push((parent, node));
                        node = parent;
                    }
                    path.reverse();
                    return path;
                }
                queue.push_back(to);
            }
        }
    }
    unreachable!("the endpoints of a component edge have a return path")
}

struct References<'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck: Option<&'tcx TypeckResults<'tcx>>,
    owners: FxHashMap<LocalDefId, Option<LocalDefId>>,
    edges: FxHashMap<(LocalDefId, LocalDefId), Edge>,
}

impl References<'_> {
    fn record(&mut self, id: HirId, target: DefId, span: Span) {
        if span.is_dummy() || span.from_expansion() {
            return;
        }
        let Some(target) = target.as_local() else {
            return;
        };
        let [Some(from), Some(to)] = [id.owner.def_id, target].map(|def| {
            *self
                .owners
                .entry(def)
                .or_insert_with(|| owner(self.tcx, def))
        }) else {
            return;
        };
        if from == to {
            return;
        }
        let home = self.tcx.parent_module_from_def_id(from);
        let boundary = if home != self.tcx.parent_module_from_def_id(to)
            || home != self.tcx.parent_module(id)
        {
            Boundary::AcrossModules
        } else {
            Boundary::WithinModule
        };
        let key = (from, to);
        if let Some(Edge {
            boundary: old,
            site,
        }) = self.edges.get(&key)
            && (*old, site.span.lo(), site.span.hi()) <= (boundary, span.lo(), span.hi())
        {
            return;
        }
        if let Some(span) = diagnostics::source_span(self.tcx, id.owner.to_def_id(), span) {
            self.edges.insert(
                key,
                Edge {
                    boundary,
                    site: Site {
                        def: id.owner.def_id,
                        span,
                    },
                },
            );
        }
    }

    fn associated(&mut self, id: HirId, target: DefId, span: Span) {
        self.record(id, target, span);
        // The first generic argument of a trait item is Self.
        if let Some(_) = self.tcx.trait_of_assoc(target)
            && let Some(args) = self.typeck.and_then(|types| types.node_args_opt(id))
            && let Some(ty) = args.first().and_then(|arg| arg.as_type())
            && let Some(adt) = ty.peel_refs().ty_adt_def()
        {
            self.record(id, adt.did(), span);
        }
    }
}

impl<'tcx> Visitor<'tcx> for References<'tcx> {
    type NestedFilter = OnlyBodies;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        match item.kind {
            ItemKind::Use(..) | ItemKind::ExternCrate(..) => {}
            _ => intravisit::walk_item(self, item),
        }
    }

    fn visit_body(&mut self, body: &Body<'tcx>) {
        let enclosing = self.typeck.replace(self.tcx.typeck_body(body.id()));
        intravisit::walk_body(self, body);
        self.typeck = enclosing;
    }

    fn visit_path(&mut self, path: &Path<'tcx>, id: HirId) {
        intravisit::walk_path(self, path);
        let Res::Def(kind, target) = path.res else {
            return;
        };
        // An alias spelling the impl's own local type introduces its methods.
        // Treating that spelling as an outgoing edge would manufacture a cycle.
        if kind == DefKind::TyAlias
            && let Node::Item(item) = self.tcx.hir_node_by_def_id(id.owner.def_id)
            && let ItemKind::Impl(implementation) = item.kind
            && implementation.self_ty.peel_refs().hir_id == id
            && let Some(adt) = self
                .tcx
                .type_of(id.owner.def_id)
                .instantiate_identity()
                .skip_normalization()
                .peel_refs()
                .ty_adt_def()
            && adt.did().is_local()
        {
            return;
        }
        if let Some(last) = path.segments.last() {
            self.associated(id, target, last.ident.span);
        }
    }

    fn visit_qpath(&mut self, path: &'tcx QPath<'tcx>, id: HirId, _: Span) {
        if let QPath::TypeRelative(_, segment) = path {
            let typeck = self.typeck.or_else(|| {
                self.tcx
                    .has_typeck_results(id.owner.def_id)
                    .then(|| self.tcx.typeck(id.owner.def_id))
            });
            if let Some(target) = typeck.and_then(|types| types.type_dependent_def_id(id)) {
                self.associated(id, target, segment.ident.span);
            }
        }
        intravisit::walk_qpath(self, path, id);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match (self.typeck, expr.kind) {
            (Some(types), ExprKind::MethodCall(segment, ..)) => {
                if let Some(target) = types.type_dependent_def_id(expr.hir_id) {
                    self.associated(expr.hir_id, target, segment.ident.span);
                }
            }
            (Some(types), ExprKind::Field(receiver, field)) => {
                if let Some(adt) = types
                    .expr_ty_adjusted_opt(receiver)
                    .and_then(|ty| ty.peel_refs().ty_adt_def())
                {
                    self.record(expr.hir_id, adt.did(), field.span);
                }
            }
            _ => {}
        }
        intravisit::walk_expr(self, expr);
    }
}
