#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;

use rustc_hir::Mutability;
use rustc_middle::ty::{self, Ty, TyCtxt, TypingEnv};
use shapelint_driver::values::{Captures, Dispatch, GenericNode, TypeNode, with_values};

#[test]
fn repeated_instances_share_type_capture_work() {
    struct Capture;
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
            let observations = [8, 16, 32].map(|count| {
                let mut ty = tcx.types.u8;
                for _ in 0..count {
                    ty = Ty::new_ref(tcx, tcx.lifetimes.re_erased, ty, Mutability::Not);
                }
                let args = tcx.mk_args(&[ty.into()]);
                with_values(|values| {
                    let mut captures = Captures::new(tcx, values);
                    let first = captures
                        .capture_instance(TypingEnv::fully_monomorphized(), def.to_def_id(), args)
                        .expect("first captured instance");
                    for _ in 1..count {
                        let instance = captures
                            .capture_instance(
                                TypingEnv::fully_monomorphized(),
                                def.to_def_id(),
                                args,
                            )
                            .expect("repeated captured instance");
                        assert_eq!(
                            instance, first,
                            "all captures produce the same canonical instance"
                        );
                    }
                    eprintln!(
                        "shared type depth and captures {count}: {} visits",
                        captures.capture_visits
                    );
                    captures.capture_visits
                })
            });
            assert_eq!(observations, [20, 36, 68]);
            let [small, medium, large] = observations;
            assert_eq!(large - medium, 2 * (medium - small));
            rustc_driver::Compilation::Stop
        }
    }
    run_fixture("pub fn run<T>(_value: T) {}", &mut Capture);
}

// shapelint: allow(identity-string) The source string is the rustc fixture identity under test.
fn run_fixture(source: &str, callbacks: &mut (impl rustc_driver::Callbacks + Send)) {
    let directory = tempfile::tempdir().expect("fixture directory");
    let path = directory.path().join("capture.rs");
    std::fs::write(&path, source).expect("fixture source");
    let args = vec![
        "rustc".into(),
        "--crate-type=lib".into(),
        "--edition=2024".into(),
        "--sysroot".into(),
        env!("SHAPELINT_SYSROOT").into(),
        "--out-dir".into(),
        directory.path().display().to_string(),
        path.display().to_string(),
    ];
    let status =
        rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, callbacks));
    assert_eq!(status, std::process::ExitCode::SUCCESS);
}

#[test]
fn distinct_array_captures_share_their_deep_element_type() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let observations = [8, 16, 32].map(|count| {
                let mut element = tcx.types.u8;
                for _ in 0..count {
                    element = Ty::new_ref(tcx, tcx.lifetimes.re_erased, element, Mutability::Not);
                }
                with_values(|values| {
                    let mut captures = Captures::new(tcx, values.share());
                    let mut restorer = values.restorer(tcx);
                    for length in 0..count {
                        let array = Ty::new_array(tcx, element, length);
                        let id = captures.capture_type(array).expect("captured array");
                        assert_eq!(restorer.restore_type(id), Some(array));
                        let generic = captures
                            .capture_generic(array.into())
                            .expect("captured array argument");
                        assert_eq!(values[generic], GenericNode::Type(id));
                    }
                    captures.capture_visits
                })
            });
            eprintln!("distinct arrays sharing deep element (capture visits): {observations:?}");
            assert_eq!(observations, [90, 178, 354]);
            let [small, medium, large] = observations;
            assert_eq!(large - medium, 2 * (medium - small));
            rustc_driver::Compilation::Stop
        }
    }
    run_fixture("pub fn run() {}", &mut Capture);
}

#[test]
fn capture_caches_remain_with_their_value_owner() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let ty = Ty::new_slice(tcx, tcx.types.u8);
            with_values(|mut first| {
                first.intern(TypeNode::Bool).expect("first arena noise");
                let mut captures = Captures::new(tcx, first.share());
                let id = captures.capture_type(ty).expect("first captured type");
                let mut first_restorer = first.restorer(tcx);
                assert_eq!(first_restorer.restore_type(id), Some(ty));
                with_values(|mut second| {
                    second.intern(TypeNode::Char).expect("second arena noise");
                    second.intern(TypeNode::Never).expect("second arena noise");
                    let mut captures = Captures::new(tcx, second.share());
                    let id = captures.capture_type(ty).expect("second captured type");
                    let mut second_restorer = second.restorer(tcx);
                    assert_eq!(second_restorer.restore_type(id), Some(ty));
                    assert_eq!(captures.capture_visits, 4);
                });
                assert_eq!(captures.capture_type(ty).expect("cached first type"), id);
                assert_eq!(captures.capture_visits, 5);
            });
            rustc_driver::Compilation::Stop
        }
    }
    run_fixture("pub fn run() {}", &mut Capture);
}

#[test]
fn instance_capture_respects_associated_type_environment() {
    struct Capture;
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            let project = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "project")
                .expect("projection source");
            let as_u8 = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "as_u8")
                .expect("u8 environment");
            let as_u16 = tcx
                .hir_body_owners()
                .find(|def| tcx.item_name(def.to_def_id()).as_str() == "as_u16")
                .expect("u16 environment");
            let method = tcx
                .hir_body_owners()
                .find(|def| {
                    tcx.item_name(def.to_def_id()).as_str() == "identify"
                        && tcx.def_kind(tcx.parent(def.to_def_id()))
                            == rustc_hir::def::DefKind::Trait
                })
                .expect("trait method")
                .to_def_id();
            let projection = tcx
                .fn_sig(project)
                .instantiate_identity()
                .skip_binder()
                .output();
            let args = tcx.mk_args(&[projection.into()]);
            let byte_environment = TypingEnv::post_analysis(tcx, as_u8);
            let short_environment = TypingEnv::post_analysis(tcx, as_u16);
            let byte = ty::Instance::try_resolve(tcx, byte_environment, method, args)
                .expect("byte resolution")
                .expect("byte implementation");
            let short = ty::Instance::try_resolve(tcx, short_environment, method, args)
                .expect("short resolution")
                .expect("short implementation");
            assert_ne!(byte.def_id(), short.def_id());
            with_values(|values| {
                let mut captures = Captures::new(tcx, values.share());
                let byte_id = captures
                    .capture_instance(byte_environment, method, args)
                    .expect("byte capture");
                let short_id = captures
                    .capture_instance(short_environment, method, args)
                    .expect("short capture");
                assert_eq!(values[byte_id].def, byte.def_id());
                assert_eq!(values[short_id].def, short.def_id());
                assert_eq!(values[byte_id].dispatch, Dispatch::Item);
                assert_eq!(values[short_id].dispatch, Dispatch::Item);
                assert_ne!(byte_id, short_id);
                assert_eq!(
                    captures
                        .capture_instance(byte_environment, method, args)
                        .expect("cached byte capture"),
                    byte_id
                );
                assert_eq!(
                    captures
                        .capture_instance(short_environment, method, args)
                        .expect("cached short capture"),
                    short_id
                );
            });
            rustc_driver::Compilation::Stop
        }
    }
    run_fixture(
        r#"
        pub trait Identify { fn identify() -> u8 { 0 } }
        impl Identify for u8 { fn identify() -> u8 { 1 } }
        impl Identify for u16 { fn identify() -> u8 { 2 } }
        pub trait Associated { type Out: Identify; }
        pub fn project<T: Associated>() -> T::Out { loop {} }
        pub fn as_u8<T: Associated<Out = u8>>() {}
        pub fn as_u16<T: Associated<Out = u16>>() {}
        "#,
        &mut Capture,
    );
}

#[derive(Clone, Copy, Debug, hegel::DefaultGenerator)]
enum Wrapper {
    SharedReference,
    MutableReference,
    ConstPointer,
    MutablePointer,
    Array(u8),
    Tuple,
}

#[hegel::test(print_blob = true)]
fn shared_type_captures_preserve_rustc_types(tc: hegel::TestCase) {
    struct Capture(Vec<Wrapper>);
    impl rustc_driver::Callbacks for Capture {
        fn after_expansion<'tcx>(
            &mut self,
            _: &rustc_interface::interface::Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> rustc_driver::Compilation {
            with_values(|values| {
                let mut captures = Captures::new(tcx, values.share());
                let mut restorer = values.restorer(tcx);
                let mut ty = tcx.types.u8;
                let original = captures.capture_type(ty).expect("base type");
                for wrapper in &self.0 {
                    ty = match wrapper {
                        Wrapper::SharedReference => {
                            Ty::new_ref(tcx, tcx.lifetimes.re_erased, ty, Mutability::Not)
                        }
                        Wrapper::MutableReference => {
                            Ty::new_ref(tcx, tcx.lifetimes.re_erased, ty, Mutability::Mut)
                        }
                        Wrapper::ConstPointer => Ty::new_ptr(tcx, ty, Mutability::Not),
                        Wrapper::MutablePointer => Ty::new_ptr(tcx, ty, Mutability::Mut),
                        Wrapper::Array(length) => Ty::new_array(tcx, ty, u64::from(*length)),
                        Wrapper::Tuple => Ty::new_tup(tcx, &[ty, tcx.types.bool]),
                    };
                    let id = captures.capture_type(ty).expect("wrapped type");
                    assert_eq!(restorer.restore_type(id), Some(ty));
                    let before = captures.capture_visits;
                    assert_eq!(captures.capture_type(ty).expect("cached wrapped type"), id);
                    assert_eq!(captures.capture_visits, before + 1);
                    let generic = captures
                        .capture_generic(ty.into())
                        .expect("wrapped generic");
                    assert_eq!(values[generic], GenericNode::Type(id));
                    let before = captures.capture_visits;
                    assert_eq!(
                        captures
                            .capture_generic(ty.into())
                            .expect("cached wrapped generic"),
                        generic
                    );
                    assert_eq!(captures.capture_visits, before + 1);
                }
                assert_eq!(restorer.restore_type(original), Some(tcx.types.u8));
            });
            rustc_driver::Compilation::Stop
        }
    }
    let wrappers = tc.draw(hegel::generators::default::<Vec<Wrapper>>());
    run_fixture("pub fn run() {}", &mut Capture(wrappers));
}
