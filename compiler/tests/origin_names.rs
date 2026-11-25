#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_abi::FieldIdx;
use rustc_middle::mir::visit::MutVisitor;
use rustc_middle::mir::{
    Location, Place, ProjectionElem, TerminatorKind, VarDebugInfo, VarDebugInfoContents,
};
use rustc_middle::ty::TyCtxt;
use shapelint_driver::contracts::graph::{ExprNode, with_graph};

mod support;

#[derive(Clone, Copy, Debug, PartialEq, Eq, hegel::DefaultGenerator)]
enum Field {
    First,
    Second,
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum NamedPlace {
    Base,
    Field(Field),
}

#[derive(Debug, hegel::DefaultGenerator)]
struct DebugNames {
    entries: Vec<NamedPlace>,
    query: Field,
}

#[hegel::test(print_blob = true)]
fn captured_call_origins_use_longest_prefix_and_last_equal_debug_entry(tc: hegel::TestCase) {
    struct Capture(DebugNames);
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let def = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "run")
                .expect("fixture function");
            let mut body = tcx.mir_promoted(def).0.borrow().clone();
            let variable = body
                .var_debug_info
                .iter()
                .find(|entry| entry.name.as_str() == "value")
                .expect("tuple variable");
            let VarDebugInfoContents::Place(base) = variable.value else {
                panic!("tuple variable is a place");
            };
            let source_info = variable.source_info;
            let field = match self.0.query {
                Field::First => 0,
                Field::Second => 1,
            };
            let destination = base.project_deeper(
                &[ProjectionElem::Field(
                    FieldIdx::from_usize(field),
                    tcx.types.u8,
                )],
                tcx,
            );
            let original = body
                .basic_blocks
                .iter()
                .find_map(|block| match block.terminator().kind {
                    TerminatorKind::Call { destination, .. } => Some(destination),
                    _ => None,
                })
                .expect("fixture call");
            assert_eq!(original.projection.len(), 0);
            struct Redirect<'tcx> {
                tcx: TyCtxt<'tcx>,
                original: Place<'tcx>,
                destination: Place<'tcx>,
            }
            impl<'tcx> MutVisitor<'tcx> for Redirect<'tcx> {
                fn tcx(&self) -> TyCtxt<'tcx> {
                    self.tcx
                }
                fn visit_place(
                    &mut self,
                    place: &mut Place<'tcx>,
                    _: rustc_middle::mir::visit::PlaceContext,
                    _: Location,
                ) {
                    match place.local {
                        local if local == self.original.local => {
                            *place = self.destination.project_deeper(place.projection, self.tcx);
                        }
                        _ => {}
                    }
                }
            }
            Redirect {
                tcx,
                original,
                destination,
            }
            .visit_body(&mut body);
            body.var_debug_info.clear();
            body.var_debug_info.push(VarDebugInfo {
                name: rustc_span::Symbol::intern("base"),
                source_info,
                composite: None,
                value: VarDebugInfoContents::Place(base),
                argument_index: None,
            });
            let mut expected = ("base".to_owned(), NamedPlace::Base);
            let entries = self.0.entries.iter().enumerate();
            for (index, entry) in entries {
                let name = format!("name_{index}");
                let place = match entry {
                    NamedPlace::Base => base,
                    NamedPlace::Field(field) => {
                        let field = match field {
                            Field::First => 0,
                            Field::Second => 1,
                        };
                        base.project_deeper(
                            &[ProjectionElem::Field(
                                FieldIdx::from_usize(field),
                                tcx.types.u8,
                            )],
                            tcx,
                        )
                    }
                };
                body.var_debug_info.push(VarDebugInfo {
                    name: rustc_span::Symbol::intern(&name),
                    source_info,
                    composite: None,
                    value: VarDebugInfoContents::Place(place),
                    argument_index: None,
                });
                match (entry, expected.1) {
                    (NamedPlace::Base, NamedPlace::Base) => expected = (name, *entry),
                    (NamedPlace::Field(field), _) if *field == self.0.query => {
                        expected = (name, *entry)
                    }
                    _ => {}
                }
            }
            with_graph(|mut graph| {
                let sources = shapelint_driver::diagnostics::Sources::default();
                let observations =
                    shapelint_driver::states::analyze(tcx, &body, &mut graph, &[], &sources)
                        .expect("capture indexed origin")
                        .observations;
                let [call] = observations.contracts.calls.as_slice() else {
                    panic!("fixture has one invocation");
                };
                let shapelint_driver::contracts::graph::TargetNode::Indirect(invoked) =
                    &call.target
                else {
                    panic!("fixture invokes its function-pointer argument");
                };
                let origins: Vec<_> = graph
                    .expressions()
                    .filter_map(|node| match node {
                        ExprNode::Call(
                            shapelint_driver::contracts::graph::TargetNode::Indirect(target),
                            _,
                            Some(origin),
                        ) if target == invoked => {
                            match (expected.1, graph.values[*origin].identity) {
                                (NamedPlace::Base, Some(_)) | (NamedPlace::Field(_), None) => {
                                    Some(graph.values.export_origin(*origin))
                                }
                                _ => None,
                            }
                        }
                        _ => None,
                    })
                    .collect();
                assert_eq!(origins.len(), 1);
                assert_eq!(origins[0].name.as_deref(), Some(expected.0.as_str()));
                match (expected.1, &origins[0].identity) {
                    (NamedPlace::Base, Some(identity)) => {
                        assert_eq!(identity.origin, (def.to_def_id(), base.local))
                    }
                    (NamedPlace::Field(_), None) => {}
                    value => panic!("the selected base fixes the origin identity: {value:?}"),
                }
                let [returned] = observations.contracts.returns.as_slice() else {
                    panic!("fixture has one return");
                };
                let ExprNode::Call(_, _, Some(origin)) = &graph[returned.value] else {
                    panic!(
                        "selected field returns the captured call result: {:?}",
                        graph[returned.value]
                    );
                };
                let origin = graph.values.export_origin(*origin);
                assert_eq!(origin.name.as_deref(), Some(expected.0.as_str()));
                assert_eq!(origin.identity, None);
            });
            rustc_driver::Compilation::Stop
        }
    }
    let mut capture = Capture(tc.draw(hegel::generators::default::<DebugNames>()));
    let directory = tempfile::tempdir().expect("fixture directory");
    let source = directory.path().join("names.rs");
    let selected_field = match capture.0.query {
        Field::First => 0,
        Field::Second => 1,
    };
    std::fs::write(
        &source,
        format!("pub fn run(make: fn() -> u8) -> u8 {{ let mut value=(0u8,0u8); value.1=make(); value.{selected_field} }}"),
    )
    .expect("fixture source");
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
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, &mut capture));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Expression {
    Call,
    CheckedSum,
}

#[hegel::test(print_blob = true)]
fn unnamed_temporaries_keep_their_source_expression_names(tc: hegel::TestCase) {
    let expression = tc.draw(hegel::generators::default::<Expression>());
    let (source, expected) = match expression {
        Expression::Call => (
            "pub fn run(text:&str, make:fn()->usize) -> &str { &text[make()..] }",
            "make()",
        ),
        Expression::CheckedSum => (
            "pub fn run(text:&str, make:fn()->usize) -> &str { &text[(make()+1)..] }",
            "make() + 1",
        ),
    };
    let output =
        support::analyze(source, &["--show-analysis-gaps"]).expect("capture unnamed expression");
    let findings: Vec<serde_json::Value> = output
        .lines()
        .map(|line| serde_json::from_str(line).expect("diagnostic"))
        .collect();
    let messages: Vec<_> = findings
        .iter()
        .filter(|finding| finding["rule"] == "unproven-precondition")
        .map(|finding| finding["primary"]["message"].as_str().expect("message"))
        .collect();
    assert!(
        messages.iter().any(|message| message.contains(expected)),
        "{expression:?}: {output}"
    );
    assert!(!output.contains("field["), "{output}");
}

#[test]
fn closure_capture_names_keep_distinct_projected_variables() {
    let source = "pub struct Range { pub start:usize, pub end:usize }
        pub fn run(text:&str, make:fn()->Range) -> &str {
            let left=make(); let right=make();
            let read=|| &text[left.start..right.end]; read()
        }";
    let output = support::analyze(source, &["--show-analysis-gaps"])
        .expect("capture closure debug projections");
    assert!(output.contains("left.start <= right.end"), "{output}");
    assert!(!output.contains("field["), "{output}");
}

#[test]
fn bodies_with_one_hir_owner_keep_their_own_expression_names() {
    let source = "pub fn run(text:&[u8], left:usize, right:usize) -> (u8,u8) {
        let first=|| text[left]; let second=|| text[right]; (first(),second())
    }";
    let output =
        support::analyze(source, &["--show-analysis-gaps"]).expect("capture sibling closures");
    assert!(output.contains("left < text.len()"), "{output}");
    assert!(output.contains("right < text.len()"), "{output}");
}

#[test]
fn raw_slice_metadata_keeps_the_pointee_length() {
    let source = "pub fn run(text: &[u8], index: usize) -> u8 {\n\
        let pointer = &raw const *text;\n\
        if index < text.len() { unsafe { (&*pointer)[index] } } else { 0 }\n\
    }";
    let output =
        support::analyze(source, &["--show-analysis-gaps"]).expect("capture raw slice metadata");
    assert!(!output.contains("unproven-precondition"), "{output}");
    assert!(!output.contains("invalid-state-use"), "{output}");
}
