#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir_transform;
extern crate rustc_structures;

use std::process::ExitCode;
use std::sync::OnceLock;

use rustc_data_structures::steal::Steal;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::LocalDefId;
use rustc_index::IndexVec;
use rustc_interface::interface;
use rustc_middle::mir::{Body, Promoted};
use rustc_middle::ty::TyCtxt;
use shapelint_driver::{analysis, artifacts, pipeline, protocols};

struct Session {
    analyses: analysis::Session,
    protocols: protocols::Catalog,
    sources: shapelint_driver::diagnostics::Sources,
}

// shapelint: allow(implicit-dependency) The rustc provider signature has no captured context.
// This binary runs one compiler session; only lifetime-free evidence crosses the boundary.
static SESSION: OnceLock<Session> = OnceLock::new();

struct Driver {
    summary_inputs: artifacts::Inputs,
    summary_output: Option<std::path::PathBuf>,
    status: ExitCode,
}

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
        if let Some(_) = self.summary_output
            && !tcx.needs_metadata()
        {
            tcx.dcx()
                .fatal("summary output requires an importable library crate");
        }
        let metadata = if let Some(_) = self.summary_output {
            match rustc_metadata::fs::encode_and_write_metadata(tcx) {
                Ok(metadata) => Some(metadata),
                Err(_) => {
                    self.status = ExitCode::FAILURE;
                    return Compilation::Stop;
                }
            }
        } else {
            None
        };
        session.analyses.finish(tcx, |graph, analyses| {
            let imported = match std::mem::take(&mut self.summary_inputs).import(tcx, graph) {
                Ok(imported) => imported,
                Err(error) => tcx.dcx().fatal(error.to_string()),
            };
            let linked = pipeline::Summaries::link(analyses, imported);
            if let Err(error) = pipeline::evaluate_crate(tcx, graph, &linked) {
                tcx.dcx().fatal(error.to_string());
            }
            if let Some((path, metadata)) = self.summary_output.as_ref().zip(metadata.as_ref()) {
                if let Err(error) =
                    artifacts::export(tcx, &linked, graph, path, metadata.full(), &session.sources)
                {
                    tcx.dcx().fatal(error.to_string());
                }
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
    let mut arguments = std::env::args();
    let mut args: Vec<_> = arguments.next().into_iter().collect();
    let mut summary_paths = Vec::new();
    let mut summary_output = None;
    while let Some(arg) = arguments.next() {
        match arg.as_str() {
            "--summary-input" | "--summary-output" => {
                let Some(path) = arguments.next() else {
                    eprintln!("shapelint-driver: {arg} requires a path");
                    return ExitCode::FAILURE;
                };
                match arg.as_str() {
                    "--summary-input" => summary_paths.push(path.into()),
                    "--summary-output" => summary_output = Some(path.into()),
                    _ => unreachable!("summary option dispatch"),
                }
            }
            _ => args.push(arg),
        }
    }
    let mut summary_inputs = match artifacts::Inputs::try_from(summary_paths.as_slice()) {
        Ok(inputs) => inputs,
        Err(error) => {
            eprintln!("shapelint-driver: {error}");
            return ExitCode::FAILURE;
        }
    };
    args.extend(std::mem::take(&mut summary_inputs.externs));
    let mut driver = Driver {
        summary_inputs,
        summary_output,
        status: ExitCode::SUCCESS,
    };
    match compile(args, &mut driver) {
        ExitCode::SUCCESS => driver.status,
        status => status,
    }
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
