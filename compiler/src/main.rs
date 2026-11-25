#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_mir_transform;

use std::process::ExitCode;
use std::sync::OnceLock;

use rustc_data_structures::steal::Steal;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_index::IndexVec;
use rustc_interface::interface;
use rustc_middle::mir::{Body, Promoted};
use rustc_middle::ty::TyCtxt;
use shapelint_driver::{analysis, protocols};

struct Session {
    analyses: analysis::Session,
    protocols: protocols::Catalog,
    sources: shapelint_driver::diagnostics::Sources,
}

// shapelint: allow(implicit-dependency) The rustc provider signature has no captured context.
// This binary runs one compiler session; only lifetime-free evidence crosses the boundary.
static SESSION: OnceLock<Session> = OnceLock::new();

struct Driver;

impl Callbacks for Driver {
    fn config(&mut self, config: &mut interface::Config) {
        config.override_queries = Some(|_, providers| providers.queries.mir_promoted = capture);
        // Every lint invocation must execute the providers; Buck caches the whole lint action.
        config.opts.incremental = None;
    }

    fn after_expansion<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let session = Session {
            analyses: analysis::Session::new(),
            protocols: protocols::Catalog::collect(tcx),
            sources: shapelint_driver::diagnostics::Sources::default(),
        };
        match SESSION.set(session) {
            Ok(()) => {}
            Err(_) => tcx
                .dcx()
                .fatal("shapelint driver supports one compiler session"),
        }
        // Publish before fn_sig queries, which can reenter the MIR provider.
        SESSION
            .get()
            .expect("after_expansion installed the compiler session")
            .protocols
            .check_signatures(tcx);
        Compilation::Continue
    }

    fn after_analysis<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.dcx().abort_if_errors();
        let session = SESSION
            .get()
            .expect("after_expansion installed the compiler session");
        session.analyses.finish(tcx, |graph, analyses| {
            if let Err(error) = shapelint_driver::pipeline::evaluate_crate(tcx, graph, analyses) {
                tcx.dcx().fatal(error.to_string());
            }
        });
        Compilation::Stop
    }
}

fn capture<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> (
    &'tcx Steal<Body<'tcx>>,
    &'tcx Steal<IndexVec<Promoted, Body<'tcx>>>,
) {
    let mut providers = rustc_middle::util::Providers::default();
    rustc_mir_transform::provide(&mut providers);
    let result = (providers.queries.mir_promoted)(tcx, def);
    let session = SESSION
        .get()
        .expect("after_expansion installs the compiler session before MIR capture");
    if let Err(error) = session.analyses.capture(
        tcx,
        def,
        &result.0.borrow(),
        &session.protocols.names,
        &session.sources,
    ) {
        tcx.dcx().fatal(error.to_string());
    }
    result
}

fn main() -> ExitCode {
    compile(std::env::args().collect(), &mut Driver)
}

fn compile(mut args: Vec<String>, callbacks: &mut (dyn Callbacks + Send)) -> ExitCode {
    match args
        .iter()
        .find(|arg| *arg == "--sysroot" || arg.starts_with("--sysroot="))
    {
        Some(_) => {}
        None => args.extend(["--sysroot".into(), env!("SHAPELINT_SYSROOT").into()]),
    }
    rustc_driver::catch_with_exit_code(|| rustc_driver::run_compiler(&args, callbacks))
}
