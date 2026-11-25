#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_data_structures::fx::FxHashMap;
use shapelint_driver::contracts::graph::{ConditionNode, ExprNode, with_graph};
use shapelint_driver::contracts::{Order, Summary};
use shapelint_driver::protocols::{self, Flow};

fn freeze_summaries<'g>(
    graph: &mut shapelint_driver::contracts::graph::Graph<'g>,
    summaries: rustc_data_structures::fx::FxHashMap<
        rustc_hir::def_id::DefId,
        shapelint_driver::contracts::Summary<
            'g,
            shapelint_driver::contracts::graph::ExprId<'g>,
            shapelint_driver::contracts::graph::ConditionId<'g>,
            shapelint_driver::contracts::graph::TargetNode<'g>,
            shapelint_driver::contracts::graph::FlowId<'g>,
        >,
    >,
) -> rustc_data_structures::fx::FxHashMap<
    rustc_hir::def_id::DefId,
    shapelint_driver::contracts::summaries::SummaryId<'g>,
> {
    summaries
        .into_iter()
        .map(|(def, summary)| {
            let id = graph
                .summaries
                .freeze(
                    &mut graph.values,
                    &mut graph.function_sets,
                    &mut graph.input_sets,
                    &mut graph.expression_sequences,
                    summary,
                )
                .unwrap();
            (def, id)
        })
        .collect()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum Atom {
    Incoming,
    Unknown,
    Ready,
    FirstDirty,
    SecondDirty,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Branch {
    Yes,
    No,
    Both,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Callee {
    First,
    Second,
}

impl Callee {
    fn index(self) -> usize {
        match self {
            Self::First => 0,
            Self::Second => 1,
        }
    }
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum Step {
    Select(Branch, Atom),
    Alternatives(Vec<Atom>),
    Call(Callee),
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Returns {
    Incoming,
    Root,
    Recursion,
    Dirty,
    Mixed,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Case {
    initial: Atom,
    steps: Vec<Step>,
    returns: [Returns; 2],
}

#[derive(Clone, Debug)]
enum Node {
    Atom(Atom),
    Select(Branch, usize, usize),
    Alternatives(Vec<usize>),
    Call(Callee, usize),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Effect {
    Incoming,
    Unknown,
    Ready,
    Dirty(usize),
}

fn agree(left: Effect, right: Effect) -> Effect {
    match (left, right) {
        (Effect::Incoming, Effect::Incoming) => Effect::Incoming,
        (Effect::Ready, Effect::Ready) => Effect::Ready,
        (Effect::Dirty(origin), Effect::Dirty(_)) => Effect::Dirty(origin),
        _ => Effect::Unknown,
    }
}

fn aggregate(nodes: &[usize], values: &[Effect]) -> Effect {
    nodes
        .iter()
        .map(|node| values[*node])
        .reduce(agree)
        .unwrap_or(Effect::Unknown)
}

// Deliberately uses whole-table Kleene rounds and flat ordered alternatives.
// It shares neither the production scheduler nor its prefix representation.
fn oracle(nodes: &[Node], returns: &[Vec<usize>; 2], root: usize) -> Option<usize> {
    let mut values = vec![Effect::Unknown; nodes.len()];
    loop {
        let next = nodes
            .iter()
            .map(|node| match node {
                Node::Atom(Atom::Incoming) => Effect::Incoming,
                Node::Atom(Atom::Unknown) => Effect::Unknown,
                Node::Atom(Atom::Ready) => Effect::Ready,
                Node::Atom(Atom::FirstDirty) => Effect::Dirty(0),
                Node::Atom(Atom::SecondDirty) => Effect::Dirty(1),
                Node::Select(Branch::Yes, yes, _) => values[*yes],
                Node::Select(Branch::No, _, no) => values[*no],
                Node::Select(Branch::Both, yes, no) => agree(values[*yes], values[*no]),
                Node::Alternatives(alternatives) => aggregate(alternatives, &values),
                Node::Call(callee, input) => match aggregate(&returns[callee.index()], &values) {
                    Effect::Incoming => values[*input],
                    effect => effect,
                },
            })
            .collect::<Vec<_>>();
        if next == values {
            break;
        }
        values = next;
    }
    let mut pending = vec![root];
    while let Some(node) = pending.pop() {
        match &nodes[node] {
            Node::Select(Branch::Yes, yes, _) => pending.push(*yes),
            Node::Select(Branch::No, _, no) => pending.push(*no),
            Node::Select(Branch::Both, yes, no) => {
                pending.push(*no);
                pending.push(*yes);
            }
            Node::Alternatives(alternatives) => pending.extend(alternatives.iter().rev().copied()),
            Node::Atom(_) | Node::Call(..) => {
                if let Effect::Dirty(origin) = values[node] {
                    return Some(origin);
                }
            }
        }
    }
    None
}

struct Model {
    nodes: Vec<Node>,
    returns: [Vec<usize>; 2],
    root: usize,
}

impl From<&Case> for Model {
    fn from(case: &Case) -> Self {
        let mut nodes = vec![Node::Atom(case.initial)];
        let mut root = 0;
        for step in &case.steps {
            let next = match step {
                Step::Select(branch, atom) => {
                    let other = nodes.len();
                    nodes.push(Node::Atom(*atom));
                    Node::Select(*branch, root, other)
                }
                Step::Alternatives(atoms) => {
                    let mut alternatives = vec![root];
                    for atom in atoms {
                        alternatives.push(nodes.len());
                        nodes.push(Node::Atom(*atom));
                    }
                    Node::Alternatives(alternatives)
                }
                Step::Call(callee) => Node::Call(*callee, root),
            };
            root = nodes.len();
            nodes.push(next);
        }
        let mut returns = [Vec::new(), Vec::new()];
        let entries = case.returns.iter().enumerate();
        for (index, policy) in entries {
            match policy {
                Returns::Incoming => {
                    returns[index].push(nodes.len());
                    nodes.push(Node::Atom(Atom::Incoming));
                }
                Returns::Root => returns[index].push(root),
                Returns::Recursion => {
                    let input = nodes.len();
                    nodes.push(Node::Atom(Atom::Incoming));
                    returns[index].push(nodes.len());
                    nodes.push(Node::Call(
                        match index {
                            0 => Callee::Second,
                            _ => Callee::First,
                        },
                        input,
                    ));
                }
                Returns::Dirty => {
                    returns[index].push(nodes.len());
                    nodes.push(Node::Atom(match index {
                        0 => Atom::FirstDirty,
                        _ => Atom::SecondDirty,
                    }));
                }
                Returns::Mixed => {
                    returns[index].push(nodes.len());
                    nodes.push(Node::Atom(Atom::FirstDirty));
                    returns[index].push(nodes.len());
                    nodes.push(Node::Atom(Atom::SecondDirty));
                }
            }
        }
        let model = Self {
            nodes,
            returns,
            root,
        };
        model
    }
}

#[hegel::test(print_blob = true)]
fn protocol_queries_match_the_flat_fixed_point_and_first_witness_oracle(tc: hegel::TestCase) {
    let case = tc.draw(hegel::generators::default::<Case>());
    analyze(&case);
}

#[test]
fn mutually_recursive_effects_match_the_flat_oracle() {
    analyze(&Case {
        initial: Atom::FirstDirty,
        steps: vec![Step::Call(Callee::First)],
        returns: [Returns::Recursion, Returns::Recursion],
    });
}

#[test]
fn dirty_return_order_matches_the_flat_oracle() {
    analyze(&Case {
        initial: Atom::Ready,
        steps: vec![Step::Call(Callee::First)],
        returns: [Returns::Mixed, Returns::Incoming],
    });
}

fn analyze(case: &Case) {
    struct Analyze<'a>(&'a Case);
    impl rustc_driver::Callbacks for Analyze<'_> {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let definitions: FxHashMap<_, _> = tcx
                .hir_body_owners()
                .map(|def| (tcx.item_name(def.to_def_id()).to_string(), def.to_def_id()))
                .collect();
            let owner = definitions["run"];
            let helpers = [definitions["first"], definitions["second"]];
            let Model {
                nodes,
                returns: returned,
                root,
            } = Model::from(self.0);
            let expected = oracle(&nodes, &returned, root);
            with_graph(|mut graph| {
                let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                let one = graph.intern_expr(ExprNode::Number(1)).expect("one");
                let conditions = [
                    graph
                        .intern_condition(ConditionNode::Compare(Order::Equal, zero, zero))
                        .expect("true"),
                    graph
                        .intern_condition(ConditionNode::Compare(Order::Equal, zero, one))
                        .expect("false"),
                    graph
                        .intern_condition(ConditionNode::Unknown)
                        .expect("unknown"),
                ];
                let mut flows = Vec::new();
                for node in &nodes {
                    let flow = match node {
                        Node::Atom(Atom::Incoming) => Flow::Incoming,
                        Node::Atom(Atom::Unknown) => Flow::Unknown,
                        Node::Atom(Atom::Ready) => Flow::Ready,
                        Node::Atom(Atom::FirstDirty) => Flow::Dirty {
                            def: helpers[0],
                            span: tcx.def_span(helpers[0]),
                        },
                        Node::Atom(Atom::SecondDirty) => Flow::Dirty {
                            def: helpers[1],
                            span: tcx.def_span(helpers[1]),
                        },
                        Node::Select(branch, yes, no) => Flow::Select(
                            conditions[match branch {
                                Branch::Yes => 0,
                                Branch::No => 1,
                                Branch::Both => 2,
                            }],
                            flows[*yes],
                            flows[*no],
                        ),
                        Node::Alternatives(alternatives) => {
                            flows.push(
                                graph
                                    .intern_alternatives(
                                        alternatives.iter().map(|node| flows[*node]),
                                    )
                                    .expect("alternatives"),
                            );
                            continue;
                        }
                        Node::Call(callee, input) => Flow::Call {
                            callee: helpers[callee.index()],
                            argument: 0,
                            input: flows[*input],
                        },
                    };
                    flows.push(graph.intern_flow(flow).expect("flow"));
                }
                let name = rustc_span::Symbol::intern("durability");
                let mut summaries = FxHashMap::default();
                let entries = helpers.into_iter().zip(returned);
                for (helper, returned) in entries {
                    let mut summary = Summary::default();
                    for node in returned {
                        summary.protocol_returns.push(protocols::Return {
                            name,
                            argument: 0,
                            flow: flows[node],
                        });
                    }
                    summaries.insert(helper, summary);
                }
                let mut caller = Summary::default();
                caller.protocol_checks.push(protocols::Obligation {
                    name,
                    span: tcx.def_span(owner),
                    flow: flows[root],
                    guards: Default::default(),
                });
                summaries.insert(owner, caller);
                let summaries = freeze_summaries(&mut graph, summaries);
                let findings =
                    protocols::findings(tcx, &mut graph, &summaries, &Default::default())
                        .expect("findings");
                match expected {
                    None => assert!(findings.is_empty(), "{:#?}", self.0),
                    Some(origin) => {
                        let [(actual_owner, finding)] = findings.as_slice() else {
                            panic!("one dirty witness: {:#?}", self.0);
                        };
                        assert_eq!(*actual_owner, owner.expect_local());
                        let shapelint::CompilerEvidence::ProtocolBypass { origin: actual, .. } =
                            &finding.evidence
                        else {
                            panic!("protocol finding");
                        };
                        let expected = shapelint_driver::contracts::Consumer {
                            def: helpers[origin],
                            span: tcx.def_span(helpers[origin]),
                            operation: shapelint_driver::contracts::Operation::Condition,
                        }
                        .source(tcx, &Default::default());
                        assert_eq!(actual.label.span, expected.label.span, "{:#?}", self.0);
                    }
                }
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("protocol.rs");
    std::fs::write(
        &source,
        "pub fn run() {} pub fn first() {} pub fn second() {}",
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
            &mut Analyze(case)
        )),
        std::process::ExitCode::SUCCESS
    );
}

#[test]
fn a_disconnected_numeric_cycle_keeps_its_effect_on_relevant_comparisons() {
    struct Analyze;
    impl rustc_driver::Callbacks for Analyze {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let owner = tcx.hir_body_owners().next().expect("run").to_def_id();
            with_graph(|mut graph| {
                let x = graph.intern_expr(ExprNode::Argument(0)).expect("x");
                let y = graph.intern_expr(ExprNode::Argument(1)).expect("y");
                let z = graph.intern_expr(ExprNode::Argument(2)).expect("z");
                let three = graph.intern_expr(ExprNode::Number(3)).expect("three");
                let five = graph.intern_expr(ExprNode::Number(5)).expect("five");
                let seven = graph.intern_expr(ExprNode::Number(7)).expect("seven");
                let mut guards = shapelint_driver::sequence::Sequence::default();
                for (left, right) in [(x, five), (five, y), (seven, z), (z, three)] {
                    let condition = graph
                        .intern_condition(ConditionNode::Compare(Order::LessEqual, left, right))
                        .expect("constraint");
                    guards = graph
                        .condition_sequences
                        .push(guards, condition)
                        .expect("guard");
                }
                let condition = graph
                    .intern_condition(ConditionNode::Compare(Order::Less, x, y))
                    .expect("comparison");
                assert_eq!(
                    graph.truth(condition, &guards).expect("truth"),
                    shapelint_driver::contracts::Truth::Proven
                );
                let ready = graph.intern_flow(Flow::Ready).expect("ready");
                let dirty = graph
                    .intern_flow(Flow::Dirty {
                        def: owner,
                        span: tcx.def_span(owner),
                    })
                    .expect("dirty");
                let flow = graph
                    .intern_flow(Flow::Select(condition, ready, dirty))
                    .expect("selection");
                let mut summary = Summary::default();
                summary.protocol_checks.push(protocols::Obligation {
                    name: rustc_span::Symbol::intern("durability"),
                    span: tcx.def_span(owner),
                    flow,
                    guards,
                });
                let summaries = FxHashMap::from_iter([(owner, summary)]);
                let summaries = freeze_summaries(&mut graph, summaries);
                assert!(
                    protocols::findings(tcx, &mut graph, &summaries, &Default::default())
                        .expect("findings")
                        .is_empty()
                );
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("numeric.rs");
    std::fs::write(&source, "pub fn run() {}").expect("source");
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
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Analyze)),
        std::process::ExitCode::SUCCESS
    );
}

#[test]
fn a_false_literal_keeps_its_effect_after_test_merges_it_into_a_scalar_component() {
    struct Analyze;
    impl rustc_driver::Callbacks for Analyze {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let owner = tcx.hir_body_owners().next().expect("run").to_def_id();
            with_graph(|mut graph| {
                let x = graph.intern_expr(ExprNode::Argument(0)).expect("x");
                let y = graph.intern_expr(ExprNode::Argument(1)).expect("y");
                let three = graph.intern_expr(ExprNode::Number(3)).expect("three");
                let five = graph.intern_expr(ExprNode::Number(5)).expect("five");
                let seven = graph.intern_expr(ExprNode::Number(7)).expect("seven");
                let ten = graph.intern_expr(ExprNode::Number(10)).expect("ten");
                let literal = graph
                    .intern_condition(ConditionNode::Compare(Order::LessEqual, seven, three))
                    .expect("false literal");
                let tested = graph
                    .intern_expr(ExprNode::Test(literal))
                    .expect("test expression");
                let mut guards = graph.condition_sequences.from_iter([literal]).unwrap();
                for (left, right) in [(x, five), (five, y), (tested, ten)] {
                    let condition = graph
                        .intern_condition(ConditionNode::Compare(Order::LessEqual, left, right))
                        .expect("constraint");
                    guards = graph
                        .condition_sequences
                        .push(guards, condition)
                        .expect("guard");
                }
                let condition = graph
                    .intern_condition(ConditionNode::Compare(Order::Less, x, y))
                    .expect("comparison");
                assert_eq!(
                    graph.truth(condition, &guards).expect("unprojected proof"),
                    shapelint_driver::contracts::Truth::Proven
                );
                let ready = graph.intern_flow(Flow::Ready).expect("ready");
                let dirty = graph
                    .intern_flow(Flow::Dirty {
                        def: owner,
                        span: tcx.def_span(owner),
                    })
                    .expect("dirty");
                let flow = graph
                    .intern_flow(Flow::Select(condition, ready, dirty))
                    .expect("selection");
                let mut summary = Summary::default();
                summary.protocol_checks.push(protocols::Obligation {
                    name: rustc_span::Symbol::intern("durability"),
                    span: tcx.def_span(owner),
                    flow,
                    guards,
                });
                let summaries = FxHashMap::from_iter([(owner, summary)]);
                let summaries = freeze_summaries(&mut graph, summaries);
                assert!(
                    protocols::findings(tcx, &mut graph, &summaries, &Default::default())
                        .expect("findings")
                        .is_empty()
                );
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("literal.rs");
    std::fs::write(&source, "pub fn run() {}").expect("source");
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
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut Analyze)),
        std::process::ExitCode::SUCCESS
    );
}

#[derive(Clone, Copy)]
enum SharedFamily {
    Prefixes,
    Returns,
    IndependentDiamonds,
}

#[test]
fn growing_noop_prefix_obligations_reuse_completed_prefixes() {
    shared_family(SharedFamily::Prefixes);
}

#[test]
fn distinct_callee_arguments_reuse_the_return_index() {
    shared_family(SharedFamily::Returns);
}

#[test]
fn independent_guard_diamonds_share_the_completed_suffix() {
    shared_family(SharedFamily::IndependentDiamonds);
}

fn shared_family(family: SharedFamily) {
    struct Analyze(SharedFamily);
    impl rustc_driver::Callbacks for Analyze {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let definitions: FxHashMap<_, _> = tcx
                .hir_body_owners()
                .map(|def| (tcx.item_name(def.to_def_id()).to_string(), def.to_def_id()))
                .collect();
            let owner = definitions["run"];
            let helper = definitions["helper"];
            with_graph(|mut graph| {
                let name = rustc_span::Symbol::intern("durability");
                let ready = graph.intern_flow(Flow::Ready).expect("ready");
                let mut caller = Summary::default();
                let mut callee = Summary::default();
                let count = 10_000;
                match self.0 {
                    SharedFamily::Prefixes => {
                        let mut prefix = None;
                        for _ in 0..count {
                            prefix = Some(graph.intern_alternative(prefix, ready).expect("prefix"));
                            let flow = graph.intern_flow(Flow::Alternatives(prefix)).expect("root");
                            caller.protocol_checks.push(protocols::Obligation {
                                name,
                                span: tcx.def_span(owner),
                                flow,
                                guards: Default::default(),
                            });
                        }
                        let alternatives = graph.flow_alternatives().count();
                        assert_eq!(alternatives, count);
                    }
                    SharedFamily::Returns => {
                        for argument in 0..count {
                            callee.protocol_returns.push(protocols::Return {
                                name,
                                argument,
                                flow: ready,
                            });
                            let flow = graph
                                .intern_flow(Flow::Call {
                                    callee: helper,
                                    argument,
                                    input: ready,
                                })
                                .expect("call");
                            caller.protocol_checks.push(protocols::Obligation {
                                name,
                                span: tcx.def_span(owner),
                                flow,
                                guards: Default::default(),
                            });
                        }
                    }
                    SharedFamily::IndependentDiamonds => {
                        let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                        let mut flow = ready;
                        for argument in 0..count {
                            let value = graph
                                .intern_expr(ExprNode::Argument(argument))
                                .expect("argument");
                            let condition = graph
                                .intern_condition(ConditionNode::Compare(Order::Equal, value, zero))
                                .expect("condition");
                            let yes = graph.intern_alternatives([ready, flow]).expect("yes");
                            let no = graph.intern_alternatives([flow, ready]).expect("no");
                            flow = graph
                                .intern_flow(Flow::Select(condition, yes, no))
                                .expect("diamond");
                        }
                        let flows = graph.flows().count();
                        assert_eq!(flows, count * 3);
                        caller.protocol_checks.push(protocols::Obligation {
                            name,
                            span: tcx.def_span(owner),
                            flow,
                            guards: Default::default(),
                        });
                    }
                }
                let summaries = FxHashMap::from_iter([(owner, caller), (helper, callee)]);
                let summaries = freeze_summaries(&mut graph, summaries);
                assert!(
                    protocols::findings(tcx, &mut graph, &summaries, &Default::default())
                        .expect("shared queries")
                        .is_empty()
                );
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("shared.rs");
    std::fs::write(&source, "pub fn run() {} pub fn helper() {}").expect("source");
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
            &mut Analyze(family)
        )),
        std::process::ExitCode::SUCCESS
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum PredicateFamily {
    Boundary,
    Variant,
    Returned,
    CompositeComparison,
}

#[hegel::test(print_blob = true)]
fn protocol_projection_keeps_all_predicate_families_and_composite_dependencies(
    tc: hegel::TestCase,
) {
    let family = tc.draw(hegel::generators::default::<PredicateFamily>());
    struct Analyze(PredicateFamily);
    impl rustc_driver::Callbacks for Analyze {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: rustc_middle::ty::TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let owner = tcx.hir_body_owners().next().expect("run").to_def_id();
            with_graph(|mut graph| {
                let input = graph.intern_expr(ExprNode::Argument(0)).expect("input");
                let index = graph.intern_expr(ExprNode::Argument(1)).expect("index");
                let field = graph.intern_expr(ExprNode::Field(input, 0)).expect("field");
                let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                let returned_arguments = graph.expression_sequences.from_iter([index]).unwrap();
                let condition = graph
                    .intern_condition(match self.0 {
                        PredicateFamily::Boundary => ConditionNode::Boundary(field, index),
                        PredicateFamily::Variant => ConditionNode::Variant(field, 2),
                        PredicateFamily::Returned => ConditionNode::Returned(
                            shapelint_driver::contracts::graph::TargetNode::Indirect(field),
                            returned_arguments,
                        ),
                        PredicateFamily::CompositeComparison => {
                            ConditionNode::Compare(Order::LessEqual, field, index)
                        }
                    })
                    .expect("predicate");
                let guards = graph.condition_sequences.from_iter([condition]).unwrap();
                assert_eq!(
                    graph.truth(condition, &guards).expect("unprojected proof"),
                    shapelint_driver::contracts::Truth::Proven
                );
                let ready = graph.intern_flow(Flow::Ready).expect("ready");
                let dirty = graph
                    .intern_flow(Flow::Dirty {
                        def: owner,
                        span: tcx.def_span(owner),
                    })
                    .expect("dirty");
                let selected = graph
                    .intern_flow(Flow::Select(condition, ready, dirty))
                    .expect("guarded selection");
                let unrelated = graph
                    .intern_expr(ExprNode::Argument(2))
                    .expect("unrelated input");
                let unrelated = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, unrelated, zero))
                    .expect("unrelated choice");
                let yes = graph.intern_alternatives([ready, selected]).expect("yes");
                let no = graph.intern_alternatives([selected, ready]).expect("no");
                let flow = graph
                    .intern_flow(Flow::Select(unrelated, yes, no))
                    .expect("shared diamond");
                let mut summary = Summary::default();
                summary.protocol_checks.push(protocols::Obligation {
                    name: rustc_span::Symbol::intern("durability"),
                    span: tcx.def_span(owner),
                    flow,
                    guards,
                });
                let summaries =
                    freeze_summaries(&mut graph, FxHashMap::from_iter([(owner, summary)]));
                assert!(
                    protocols::findings(tcx, &mut graph, &summaries, &Default::default())
                        .expect("findings")
                        .is_empty(),
                    "{:#?}",
                    self.0
                );
            });
            rustc_driver::Compilation::Stop
        }
    }
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("predicates.rs");
    std::fs::write(&source, "pub fn run() {}").expect("source");
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
            &mut Analyze(family)
        )),
        std::process::ExitCode::SUCCESS
    );
}
