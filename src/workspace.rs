//! Rules that need facts from more than one Rust source.
//!
//! The parser produces owned facts in the parser thread. The workspace pass then compares those
//! facts without attempting name resolution, so its count is explicitly limited to the supplied
//! source corpus. Trait aliases and macro-generated items remain unknown to this syntax-only
//! pass.

use crate::rust_syntax::RustFile;
use rustc_ast::{
    ast,
    visit::{self, Visitor},
};
use rustc_hash::FxHashMap;

use crate::Span;
use crate::diagnostic::{Report, Sink};
use crate::suggest::Code;

#[derive(Default)]
pub(crate) struct Facts {
    pub(crate) path: String,
    traits: Vec<Trait>,
    impls: Vec<Impl>,
}
#[derive(Debug)]
struct Trait {
    name: String,
    span: Span,
    name_span: Span,
    scope: Vec<String>,
}
#[derive(Debug)]
struct Impl {
    trait_path: String,
    self_ty: String,
    span: Span,
    scope: Vec<String>,
    target: ImplTarget,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ImplTarget {
    Concrete,
    Generic,
}

/// Collects declarations and implementations from one parsed source.
pub(crate) fn collect(file: &RustFile<'_>) -> Facts {
    let mut collector = Collector {
        file,
        facts: Facts::default(),
        scope: Vec::new(),
    };
    collector.visit_crate(file.krate);
    collector.facts
}

struct Collector<'a> {
    file: &'a RustFile<'a>,
    facts: Facts,
    scope: Vec<String>,
}

impl<'ast> Visitor<'ast> for Collector<'_> {
    fn visit_item(&mut self, item: &'ast ast::Item) {
        match &item.kind {
            ast::ItemKind::Fn(_) => return,
            ast::ItemKind::Trait(trait_) => {
                self.facts.traits.push(Trait {
                    name: trait_.ident.name.to_string(),
                    span: self.file.span(item.span),
                    name_span: self.file.span(trait_.ident.span),
                    scope: self.scope.clone(),
                });
                return;
            }
            ast::ItemKind::Impl(implementation) => {
                if let Some(header) = &implementation.of_trait
                    && let ast::ImplPolarity::Positive = header.polarity
                {
                    self.facts.impls.push(Impl {
                        trait_path: header
                            .trait_ref
                            .path
                            .segments
                            .iter()
                            .map(|segment| segment.ident.name.to_string())
                            .collect::<Vec<_>>()
                            .join("::"),
                        self_ty: self
                            .file
                            .text(implementation.self_ty.span)
                            .split_whitespace()
                            .collect::<Vec<_>>()
                            .join(" "),
                        span: self.file.span(item.span),
                        scope: self.scope.clone(),
                        target: match implementation.generics.params.as_slice() {
                            [] => ImplTarget::Concrete,
                            _ => ImplTarget::Generic,
                        },
                    });
                }
                return;
            }
            ast::ItemKind::Mod(_, ident, _) => {
                self.scope.push(ident.name.to_string());
                visit::walk_item(self, item);
                self.scope.pop();
                return;
            }
            _ => {}
        }
        visit::walk_item(self, item);
    }
}

pub(crate) struct Index<'a> {
    declarations: Declarations<'a>,
    implementations: FxHashMap<String, Vec<(&'a Facts, &'a Impl)>>,
    implementations_by_owner_scope: FxHashMap<(String, String, String), Vec<(&'a Facts, &'a Impl)>>,
}

impl<'a> Index<'a> {
    pub(crate) fn new(all: &[&'a Facts]) -> Index<'a> {
        let mut implementations: FxHashMap<String, Vec<(&Facts, &Impl)>> = FxHashMap::default();
        let mut implementations_by_owner_scope: FxHashMap<
            (String, String, String),
            Vec<(&Facts, &Impl)>,
        > = FxHashMap::default();
        for &facts in all {
            for implementation in &facts.impls {
                let Some(name) = implementation.trait_path.rsplit("::").next() else {
                    continue;
                };
                implementations
                    .entry(name.to_string())
                    .or_default()
                    .push((facts, implementation));
                if !implementation.trait_path.contains("::") {
                    implementations_by_owner_scope
                        .entry((
                            name.to_string(),
                            crate_root(&facts.path),
                            implementation.scope.join("\u{1f}"),
                        ))
                        .or_default()
                        .push((facts, implementation));
                }
            }
        }
        Index {
            declarations: declarations(all),
            implementations,
            implementations_by_owner_scope,
        }
    }

    pub(crate) fn lint(&self, sink: &mut Sink, own: &Facts) {
        for trait_ in &own.traits {
            let Some(all_candidates) = self.implementations.get(&trait_.name) else {
                continue;
            };
            let declarations = match self.declarations.by_name.get(&trait_.name) {
                Some(declarations) => declarations.as_slice(),
                None => &[],
            };
            let (candidates, include_qualified) = match declarations {
                [_, _, ..] => (
                    self.implementations_by_owner_scope
                        .get(&(
                            trait_.name.clone(),
                            crate_root(&own.path),
                            trait_.scope.join("\u{1f}"),
                        ))
                        .map(Vec::as_slice)
                        .unwrap_or(&[]),
                    Some(()),
                ),
                [_] | [] => (all_candidates.as_slice(), None),
            };
            let qualified =
                all_candidates
                    .iter()
                    .filter(move |&(_, implementation)| match include_qualified {
                        Some(()) => implementation.trait_path.contains("::"),
                        None => false,
                    });
            let mut implementations =
                candidates
                    .iter()
                    .chain(qualified)
                    .filter_map(|&(facts, implementation)| {
                        resolves_to(implementation, facts, trait_, own, &self.declarations)
                            .map(|()| (facts, implementation))
                    });
            let Some((implementation_facts, implementation)) = implementations.next() else {
                continue;
            };
            let None = implementations.next() else {
                continue;
            };
            emit_single_impl(sink, own, trait_, implementation_facts, implementation);
        }
    }
}

fn emit_single_impl(
    sink: &mut Sink,
    own: &Facts,
    trait_: &Trait,
    implementation_facts: &Facts,
    implementation: &Impl,
) {
    let mut report = Report::new(
        format!(
            "trait {} has one implementation in the supplied sources",
            Code(&trait_.name)
        ),
        trait_.name_span,
        "single implementation found",
    );
    match implementation.target {
        ImplTarget::Concrete => {}
        ImplTarget::Generic => {
            report = report.note("the implementation is generic and may cover multiple types");
        }
    }
    if implementation.self_ty.contains("dyn ") {
        report =
            report.note("the implementation target is a trait object; this count is syntax-only");
    }
    report = report.note(
        "the count covers only the supplied sources; implementations outside this corpus are unknown",
    );
    report = report.note(
        "matching uses written trait paths and syntax scopes; Rust name resolution is not performed",
    );
    let target = format!(
        "`impl {} for {}`",
        implementation.trait_path, implementation.self_ty
    );
    if implementation_facts.path == own.path {
        report = report.label(implementation.span, target);
    } else {
        report = report.note(format!(
            "Found {target} in `{}`.",
            implementation_facts.path
        ));
    }
    sink.emit(
        "single-impl-trait",
        trait_.span,
        format!("trait {}", trait_.name),
        report.help(
            "Look for trait objects, generic callers, test implementations, and downstream implementors. Keep the trait when callers depend on that boundary. Use the concrete type when it serves every caller directly.",
        ),
    );
}

#[derive(Clone, Copy)]
struct Declaration<'a> {
    facts: &'a Facts,
    trait_: &'a Trait,
}

#[derive(Default)]
struct Declarations<'a> {
    by_name: FxHashMap<String, Vec<Declaration<'a>>>,
    by_name_scope: FxHashMap<(String, String, String), Vec<Declaration<'a>>>,
}

fn declarations<'a>(all: &[&'a Facts]) -> Declarations<'a> {
    let mut out = Declarations::default();
    for &facts in all {
        for trait_ in &facts.traits {
            let declaration = Declaration { facts, trait_ };
            out.by_name
                .entry(trait_.name.clone())
                .or_default()
                .push(declaration);
            out.by_name_scope
                .entry(scope_key(&trait_.name, facts, &trait_.scope))
                .or_default()
                .push(declaration);
        }
    }
    out
}

fn resolves_to(
    implementation: &Impl,
    implementation_owner: &Facts,
    trait_: &Trait,
    owner: &Facts,
    declarations: &Declarations<'_>,
) -> Option<()> {
    let Some(path_name) = implementation.trait_path.rsplit("::").next() else {
        return None;
    };
    if path_name != trait_.name {
        return None;
    }

    let path = &implementation.trait_path;
    let path_parts: Vec<&str> = path.split("::").collect();
    let qualified = path_parts.len() > 1;
    let implementation_scope = effective_scope(implementation_owner, &implementation.scope);
    let trait_scope = effective_scope(owner, &trait_.scope);
    if qualified {
        return qualified_path_matches(
            &path_parts,
            trait_,
            &implementation_scope,
            &trait_scope,
            implementation_owner,
            owner,
        );
    }

    if implementation.scope == trait_.scope && implementation_owner.path == owner.path {
        return Some(());
    }

    // An unqualified path can refer to a declaration in another source only when its name is
    // unique in the supplied corpus. This avoids treating `a::Thing` and `b::Thing` as one trait.
    let Some(candidates) = declarations.by_name.get(trait_.name.as_str()) else {
        return None;
    };
    let in_scope = declarations
        .by_name_scope
        .get(&scope_key(
            trait_.name.as_str(),
            implementation_owner,
            &implementation.scope,
        ))
        .map(Vec::as_slice)
        .unwrap_or(&[]);
    match in_scope {
        [candidate] => (candidate.facts.path == owner.path && candidate.trait_.span == trait_.span)
            .then_some(()),
        _ => match candidates.as_slice() {
            [candidate] => (crate_root(&candidate.facts.path)
                == crate_root(&implementation_owner.path)
                && candidate.facts.path == owner.path
                && candidate.trait_.span == trait_.span)
                .then_some(()),
            _ => None,
        },
    }
}

// shapelint: allow(tuple-return) This compound key is the map's complete workspace identity.
fn scope_key(name: &str, facts: &Facts, scope: &[String]) -> (String, String, String) {
    (
        name.to_owned(),
        crate_root(&facts.path),
        effective_scope(facts, scope).join("\u{1f}"),
    )
}

fn qualified_path_matches(
    path_parts: &[&str],
    trait_: &Trait,
    implementation_scope: &[String],
    trait_scope: &[String],
    implementation_owner: &Facts,
    owner: &Facts,
) -> Option<()> {
    let (qualifier, prefix) = match path_parts {
        ["self", rest @ ..] => (Some("self"), rest),
        ["crate", rest @ ..] => (Some("crate"), rest),
        ["super", rest @ ..] => (Some("super"), rest),
        rest => (None, rest),
    };
    if prefix.last().copied() != Some(trait_.name.as_str()) {
        return None;
    }
    let module_prefix = &prefix[..prefix.len().saturating_sub(1)];
    let mut target_scope = match qualifier {
        Some("self") => implementation_scope.to_vec(),
        Some("crate") | None => Vec::new(),
        Some("super") => {
            let Some(parent_len) = implementation_scope.len().checked_sub(1) else {
                return None;
            };
            implementation_scope[..parent_len].to_vec()
        }
        Some(_) => return None,
    };
    target_scope.extend(module_prefix.iter().map(|part| (*part).to_string()));
    if trait_scope != target_scope.as_slice() {
        return None;
    }
    (crate_root(&implementation_owner.path) == crate_root(&owner.path)).then_some(())
}

fn effective_scope(facts: &Facts, scope: &[String]) -> Vec<String> {
    let mut effective = file_module_scope(&facts.path);
    effective.extend_from_slice(scope);
    effective
}

fn file_module_scope(path: &str) -> Vec<String> {
    let normalized = path.replace('\\', "/");
    let mut parts: Vec<&str> = normalized.split('/').collect();
    let Some(file) = parts.pop() else {
        return Vec::new();
    };
    let Some(stem) = file.strip_suffix(".rs") else {
        return Vec::new();
    };
    match stem {
        "lib" | "main" => return Vec::new(),
        _ => {}
    }
    if stem != "mod" {
        parts.push(stem);
    }
    let mut suffix = parts.iter().copied();
    let modules = match suffix.find(|part| *part == "src") {
        Some(_) => suffix,
        None => parts.iter().copied(),
    };
    modules.map(str::to_owned).collect()
}

fn crate_root(path: &str) -> String {
    let path = path.replace('\\', "/");
    match path.rsplit_once("/src/") {
        Some((root, _)) => root.to_string(),
        None => match path.rsplit_once("/tests/") {
            Some((root, _)) => root.to_string(),
            None => match path.rsplit_once('/') {
                Some((root, _)) if root != "src" && root != "tests" => root.to_string(),
                _ => String::new(),
            },
        },
    }
}
