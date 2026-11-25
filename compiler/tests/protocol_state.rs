#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use shapelint_driver::contracts::graph::with_graph;
use shapelint_driver::protocols::{Flow, State, with_stores};

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Resource {
    First,
    Second,
    Untracked,
}

impl Resource {
    fn local(self) -> rustc_middle::mir::Local {
        rustc_middle::mir::Local::from_usize(match self {
            Self::First => 1,
            Self::Second => 2,
            Self::Untracked => 3,
        })
    }
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Action {
    Forget(Resource),
    ProjectedWrite(Resource),
    MergeForgotten(Resource),
    RestoreForgotten(Resource),
    DistinctCall,
    AliasedCall,
}

#[derive(Debug, hegel::DefaultGenerator)]
struct Actions(Vec<Action>);

#[hegel::test(print_blob = true)]
fn indexed_protocol_state_matches_flat_forgetting_and_alias_model(tc: hegel::TestCase) {
    let actions = tc.draw(hegel::generators::default::<Actions>());
    struct Analyze(Actions);
    impl rustc_driver::Callbacks for Analyze {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let owner = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "run")
                .expect("run")
                .to_def_id();
            let callee = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "callee")
                .expect("callee")
                .to_def_id();
            let body = tcx.optimized_mir(owner);
            let names = [
                rustc_span::Symbol::intern("durability"),
                rustc_span::Symbol::intern("visibility"),
            ];
            let projected = |resource: Resource| {
                rustc_middle::mir::Place::from(resource.local())
                    .project_deeper(&[rustc_middle::mir::ProjectionElem::Deref], tcx)
            };
            with_graph(|mut graph| {
                with_stores(&mut graph, |stores, graph| {
                    let mut state =
                        State::initial(stores, graph, tcx, body, &names).expect("initial");
                    let wide_names: Vec<_> = (0..64)
                        .map(|index| rustc_span::Symbol::intern(&format!("protocol_{index}")))
                        .collect();
                    let wide = State::initial(stores, graph, tcx, body, &wide_names)
                        .expect("wide initial");
                    let reference_args = body
                        .args_iter()
                        .filter(|local| body.local_decls[*local].ty.is_ref())
                        .count();
                    let dense_pairs = reference_args * wide_names.len();
                    assert_eq!(dense_pairs, 2 * 64);
                    assert_eq!(wide.storage_entries(stores), 2 + 64);
                    assert!(wide.storage_entries(stores) < dense_pairs);
                    assert_eq!(wide.returns(stores, 2).len(), 2 * 64);
                    let incoming = graph.intern_flow(Flow::Incoming).expect("incoming");
                    let unknown = graph.intern_flow(Flow::Unknown).expect("unknown");
                    let condition = graph
                        .intern_condition(
                            shapelint_driver::contracts::graph::ConditionNode::Unknown,
                        )
                        .expect("condition");
                    let first_place = rustc_middle::mir::Place::from(Resource::First.local());
                    let mut left_default = state.clone();
                    let mut right_forgotten = state.clone();
                    right_forgotten.forget(stores, first_place).unwrap();
                    left_default
                        .merge(
                            stores,
                            graph,
                            &right_forgotten,
                            shapelint_driver::contracts::Join::Hull,
                            Some(condition),
                        )
                        .expect("default-left merge");
                    let left_flow = left_default
                        .returns(stores, 2)
                        .into_iter()
                        .find(|returned| returned.name == names[0] && returned.argument == 0)
                        .expect("left merged return")
                        .flow;
                    match &graph[left_flow] {
                        Flow::Select(got, yes, no) => {
                            assert_eq!(*got, condition);
                            assert_eq!(*yes, incoming);
                            assert_eq!(*no, unknown);
                        }
                        _ => panic!("expected left-oriented select"),
                    }
                    let mut right_default = state.clone();
                    right_default.forget(stores, first_place).unwrap();
                    right_default
                        .merge(
                            stores,
                            graph,
                            &state,
                            shapelint_driver::contracts::Join::Hull,
                            Some(condition),
                        )
                        .expect("default-right merge");
                    let right_flow = right_default
                        .returns(stores, 2)
                        .into_iter()
                        .find(|returned| returned.name == names[0] && returned.argument == 0)
                        .expect("right merged return")
                        .flow;
                    match &graph[right_flow] {
                        Flow::Select(got, yes, no) => {
                            assert_eq!(*got, condition);
                            assert_eq!(*yes, unknown);
                            assert_eq!(*no, incoming);
                        }
                        _ => panic!("expected right-oriented select"),
                    }
                    let mut flat = Vec::new();
                    for resource in [Resource::First, Resource::Second] {
                        for name in names {
                            flat.push((name, projected(resource), incoming));
                        }
                    }
                    for action in &self.0.0 {
                        let snapshot = state.clone();
                        let before = snapshot.returns(stores, 2);
                        match action {
                            Action::Forget(resource) => {
                                state
                                    .forget(
                                        stores,
                                        rustc_middle::mir::Place::from(resource.local()),
                                    )
                                    .unwrap();
                                flat.retain(|(_, place, _)| place.local != resource.local());
                            }
                            Action::ProjectedWrite(resource) => {
                                state.forget(stores, projected(*resource)).unwrap()
                            }
                            Action::MergeForgotten(resource) => {
                                let mut other = state.clone();
                                other
                                    .forget(
                                        stores,
                                        rustc_middle::mir::Place::from(resource.local()),
                                    )
                                    .unwrap();
                                state
                                    .merge(
                                        stores,
                                        graph,
                                        &other,
                                        shapelint_driver::contracts::Join::Widen,
                                        None,
                                    )
                                    .expect("missing right merge");
                                for (_, place, flow) in &mut flat {
                                    if place.local == resource.local() {
                                        *flow = unknown;
                                    }
                                }
                            }
                            Action::RestoreForgotten(resource) => {
                                let previous = state.clone();
                                state
                                    .forget(
                                        stores,
                                        rustc_middle::mir::Place::from(resource.local()),
                                    )
                                    .unwrap();
                                state
                                    .merge(
                                        stores,
                                        graph,
                                        &previous,
                                        shapelint_driver::contracts::Join::Widen,
                                        None,
                                    )
                                    .expect("missing left merge");
                                for (_, place, flow) in &mut flat {
                                    if place.local == resource.local() {
                                        *flow = unknown;
                                    }
                                }
                            }
                            Action::DistinctCall | Action::AliasedCall => {
                                let first = projected(Resource::First);
                                let second = match action {
                                    Action::DistinctCall => projected(Resource::Second),
                                    _ => first,
                                };
                                let resources = [(0, first), (1, second)];
                                state
                                    .call(
                                        stores,
                                        graph,
                                        tcx,
                                        owner,
                                        Some(callee),
                                        &resources,
                                        &names,
                                        tcx.def_span(owner),
                                        &shapelint_driver::sequence::Sequence::EMPTY,
                                    )
                                    .expect("call");
                                for (argument, resource) in resources {
                                    for name in names {
                                        let previous = flat
                                            .iter()
                                            .find(|(other_name, place, _)| {
                                                *other_name == name && *place == resource
                                            })
                                            .map(|(_, _, flow)| *flow)
                                            .unwrap_or(unknown);
                                        let flow = match action {
                                            Action::DistinctCall => graph
                                                .intern_flow(Flow::Call {
                                                    callee,
                                                    argument,
                                                    input: previous,
                                                })
                                                .expect("effect"),
                                            _ => unknown,
                                        };
                                        match flat.iter_mut().find(|(other_name, place, _)| {
                                            *other_name == name && *place == resource
                                        }) {
                                            Some((_, _, value)) => *value = flow,
                                            None => flat.push((name, resource, flow)),
                                        }
                                    }
                                }
                            }
                        }
                        let actual = state.returns(stores, 2);
                        assert_eq!(actual.len(), flat.len(), "{action:?}");
                        for (name, place, flow) in &flat {
                            let returned = actual
                                .iter()
                                .find(|returned| {
                                    returned.name == *name
                                        && returned.argument == place.local.index() - 1
                                })
                                .expect("tracked formal reference");
                            assert_eq!(returned.flow, *flow, "{action:?}");
                        }
                        let after = snapshot.returns(stores, 2);
                        assert_eq!(
                            before
                                .into_iter()
                                .map(|value| (value.name, value.argument, value.flow))
                                .collect::<Vec<_>>(),
                            after
                                .into_iter()
                                .map(|value| (value.name, value.argument, value.flow))
                                .collect::<Vec<_>>(),
                            "snapshot changed after {action:?}"
                        );
                        state
                            .merge(
                                stores,
                                graph,
                                &state.clone(),
                                shapelint_driver::contracts::Join::Hull,
                                None,
                            )
                            .expect("unchanged merge");
                    }
                });
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("state.rs");
    std::fs::write(
        &source,
        "pub fn run(_: &u8, _: &u8) {} pub fn callee(_: &u8, _: &u8) {}",
    )
    .expect("source");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        source.display().to_string(),
    ];
    assert_eq!(
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(
            &args,
            &mut Analyze(actions)
        )),
        std::process::ExitCode::SUCCESS
    );
}
