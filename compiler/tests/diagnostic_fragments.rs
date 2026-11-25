#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use rustc_middle::ty::{TyCtxt, UintTy};
use shapelint_driver::calls::Type;
use shapelint_driver::contracts::graph::{
    ConditionNode, ExprNode, TargetNode, TextMatchNode, with_graph,
};
use shapelint_driver::contracts::{Arithmetic, Order};

fn render(mut callback: impl rustc_driver::Callbacks + Send) {
    let directory = tempfile::tempdir().expect("source directory");
    let source = directory.path().join("render.rs");
    std::fs::write(&source, "pub fn run() {}").expect("render source");
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
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut callback));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[test]
fn deep_skew_arithmetic_preserves_every_parenthesis_and_operand() {
    struct Render;
    impl rustc_driver::Callbacks for Render {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            with_graph(|mut graph| {
                let mut value = graph.intern_expr(ExprNode::Number(7)).expect("seven");
                let one = graph.intern_expr(ExprNode::Number(1)).expect("one");
                for _ in 0..100_000 {
                    value = graph
                        .intern_expr(ExprNode::Arithmetic(
                            Arithmetic::Add(UintTy::Usize),
                            value,
                            one,
                        ))
                        .expect("addition");
                }
                let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                let condition = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, value, zero))
                    .expect("comparison");
                let actual = shapelint_driver::diagnostics::Condition {
                    restorer: &std::cell::RefCell::new(graph.values.restorer(tcx)),
                    tcx,
                    def: rustc_hir::def_id::LOCAL_CRATE.as_def_id(),
                    condition,
                    graph: &graph,
                }
                .to_string();
                let expected = format!("{}7{} == 0", "(".repeat(100_000), " + 1)".repeat(100_000));
                assert_eq!(actual, expected);
                assert_eq!(graph.expression_count(), 100_003);
            });
            rustc_driver::Compilation::Stop
        }
    }
    render(Render);
}

#[test]
fn shared_children_emit_every_occurrence() {
    struct Render;
    impl rustc_driver::Callbacks for Render {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            with_graph(|mut graph| {
                let mut value = graph.intern_expr(ExprNode::Number(7)).expect("seven");
                let mut expected = "7".to_owned();
                for _ in 0..12 {
                    let fields = graph
                        .expression_sequences
                        .from_iter([value, value])
                        .expect("fields");
                    value = graph
                        .intern_expr(ExprNode::Aggregate(fields))
                        .expect("shared aggregate");
                    expected = format!("fields ({expected}, {expected})");
                }
                let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                let condition = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, value, zero))
                    .expect("comparison");
                let actual = shapelint_driver::diagnostics::Condition {
                    restorer: &std::cell::RefCell::new(graph.values.restorer(tcx)),
                    tcx,
                    def: rustc_hir::def_id::LOCAL_CRATE.as_def_id(),
                    condition,
                    graph: &graph,
                }
                .to_string();
                expected.push_str(" == 0");
                assert_eq!(actual, expected);
                assert_eq!(actual.matches('7').count(), 1 << 12);
                assert_eq!(graph.expression_count(), 14);
            });
            rustc_driver::Compilation::Stop
        }
    }
    render(Render);
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
enum Step {
    Add,
    Subtract,
    WrappingSubtract,
    Element,
    Field,
    Select,
    Matches,
    Partition,
    Trimmed,
    Found,
    MatchIndex,
    MatchEntry,
    Slice,
    Length,
    Call,
    Aggregate,
    Test,
}

#[derive(Clone, Debug, hegel::DefaultGenerator)]
struct Program {
    number: u64,
    steps: Vec<Step>,
}

enum ExpectedValue {
    Number(u64),
    Expression(String),
}

impl std::fmt::Display for ExpectedValue {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Number(number) => number.fmt(formatter),
            Self::Expression(text) => text.fmt(formatter),
        }
    }
}

struct RenderProgram(Program);

impl rustc_driver::Callbacks for RenderProgram {
    fn after_analysis<'tcx>(
        &mut self,
        _: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        let Program { number, steps } = &self.0;
        with_graph(|mut graph| {
            let mut value = graph
                .intern_expr(ExprNode::Number(u128::from(*number)))
                .expect("initial number");
            let mut expected = ExpectedValue::Number(*number);
            let one = graph.intern_expr(ExprNode::Number(1)).expect("one");
            let unknown = graph.intern_expr(ExprNode::Unknown).expect("unknown");
            let condition = graph
                .intern_condition(ConditionNode::Unknown)
                .expect("unknown condition");
            for step in steps {
                let (node, text) = match step {
                    Step::Add => (
                        ExprNode::Arithmetic(Arithmetic::Add(UintTy::Usize), value, one),
                        format!("({expected} + 1)"),
                    ),
                    Step::Subtract => (
                        ExprNode::Arithmetic(Arithmetic::Subtract(UintTy::Usize), value, one),
                        format!("({expected} - 1)"),
                    ),
                    Step::WrappingSubtract => (
                        ExprNode::Arithmetic(Arithmetic::WrappingSubtract(64), value, one),
                        format!("{expected}.wrapping_sub(1)"),
                    ),
                    Step::Element => (ExprNode::Element(value, one), format!("{expected}[1]")),
                    Step::Field => (ExprNode::Field(value, 0), format!("a field of {expected}")),
                    Step::Select => (
                        ExprNode::Select(condition, value, one),
                        match &expected {
                            ExpectedValue::Number(1) => "1".to_owned(),
                            ExpectedValue::Number(0) => {
                                "could not determine the required condition".to_owned()
                            }
                            _ => format!(
                                "(if could not determine the required condition {{ {expected} }} else {{ 1 }})"
                            ),
                        },
                    ),
                    Step::Matches => (
                        ExprNode::Matches {
                            text: value,
                            pattern: one,
                        },
                        format!("{expected}.match_indices(1)"),
                    ),
                    Step::Partition => (
                        ExprNode::Partition {
                            sequence: value,
                            predicate: unknown,
                        },
                        format!("the partition point in {expected}"),
                    ),
                    Step::Trimmed => (ExprNode::Trimmed(value), format!("{expected}.trim_start()")),
                    Step::Found => (
                        ExprNode::Found {
                            text: value,
                            pattern: one,
                        },
                        format!("{expected}.find(1)"),
                    ),
                    Step::MatchIndex => (
                        ExprNode::MatchIndex {
                            text: value,
                            pattern: one,
                            occurrence: unknown,
                        },
                        format!("the position of 1 in {expected}"),
                    ),
                    Step::MatchEntry => (
                        ExprNode::MatchEntry(TextMatchNode {
                            text: value,
                            pattern: one,
                            occurrence: unknown,
                        }),
                        format!("the position of 1 in {expected}"),
                    ),
                    Step::Slice => (
                        ExprNode::Slice {
                            text: value,
                            start: one,
                            end: one,
                        },
                        format!("{expected}[1..1]"),
                    ),
                    Step::Length => (ExprNode::Length(value), format!("{expected}.len()")),
                    Step::Call => (
                        ExprNode::Call(
                            TargetNode::Indirect(unknown),
                            graph
                                .expression_sequences
                                .from_iter([value, unknown, one])
                                .expect("arguments"),
                            None,
                        ),
                        format!("callback({expected}, unknown, 1)"),
                    ),
                    Step::Aggregate => (
                        ExprNode::Aggregate(
                            graph
                                .expression_sequences
                                .from_iter([value, unknown, one])
                                .expect("fields"),
                        ),
                        format!("fields ({expected}, unknown, 1)"),
                    ),
                    Step::Test => {
                        let condition = graph
                            .intern_condition(ConditionNode::Boundary(value, one))
                            .expect("boundary condition");
                        (
                            ExprNode::Test(condition),
                            format!("1 is a UTF-8 boundary in {expected}"),
                        )
                    }
                };
                value = graph.intern_expr(node).expect("expression");
                expected = match (step, expected) {
                    (Step::Select, ExpectedValue::Number(1)) => ExpectedValue::Number(1),
                    _ => ExpectedValue::Expression(text),
                };
            }
            let condition = graph
                .intern_condition(ConditionNode::Compare(Order::Equal, value, unknown))
                .expect("comparison");
            let actual = shapelint_driver::diagnostics::Condition {
                restorer: &std::cell::RefCell::new(graph.values.restorer(tcx)),
                tcx,
                def: rustc_hir::def_id::LOCAL_CRATE.as_def_id(),
                condition,
                graph: &graph,
            }
            .to_string();
            assert_eq!(
                actual,
                format!("could not prove {expected} == the unknown value")
            );
        });
        rustc_driver::Compilation::Stop
    }
}

#[hegel::test(print_blob = true)]
fn mixed_expression_fragments_preserve_exact_spelling(tc: hegel::TestCase) {
    let program = tc.draw(hegel::generators::default::<Program>());
    render(RenderProgram(program));
}

#[test]
fn equal_selection_branches_remain_literal_when_nested() {
    render(RenderProgram(Program {
        number: 1,
        steps: vec![Step::Select, Step::Select, Step::Call],
    }));
}

#[test]
fn boolean_selection_renders_its_condition_when_nested() {
    render(RenderProgram(Program {
        number: 0,
        steps: vec![Step::Select, Step::Select, Step::Call],
    }));
}

#[test]
fn typed_fragments_preserve_boolean_comparison_spelling() {
    struct Render;
    impl rustc_driver::Callbacks for Render {
        fn after_analysis<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            with_graph(|mut graph| {
                let zero = graph.intern_expr(ExprNode::Number(0)).expect("zero");
                let one = graph.intern_expr(ExprNode::Number(1)).expect("one");
                let condition = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, zero, one))
                    .expect("inner comparison");
                let value = graph.intern_expr(ExprNode::Test(condition)).expect("test");
                let ty = graph.values.intern_type(&Type::Bool).expect("type");
                let value = graph
                    .intern_expr(ExprNode::Typed(ty, value))
                    .expect("typed test");
                let condition = graph
                    .intern_condition(ConditionNode::Compare(Order::Equal, value, zero))
                    .expect("comparison");
                let actual = shapelint_driver::diagnostics::Condition {
                    restorer: &std::cell::RefCell::new(graph.values.restorer(tcx)),
                    tcx,
                    def: rustc_hir::def_id::LOCAL_CRATE.as_def_id(),
                    condition,
                    graph: &graph,
                }
                .to_string();
                assert_eq!(actual, "0 == 1 == false");
            });
            rustc_driver::Compilation::Stop
        }
    }
    render(Render);
}
