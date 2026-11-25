use std::io::Write;
use std::process::ExitCode;

use rustc_data_structures::fx::FxHashSet;
use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;

use crate::Diagnostics;
use graph::Graph;

mod graph;
mod references;

enum Baseline {
    Emit,
    Check(Vec<FxHashSet<String>>),
}

struct Cycles {
    baseline: Baseline,
    diagnostics: Diagnostics,
    status: ExitCode,
}

impl Callbacks for Cycles {
    fn after_expansion<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        tcx.dcx().abort_if_errors();
        let graph = Graph::collect(tcx);
        tcx.dcx().abort_if_errors();
        match &self.baseline {
            Baseline::Emit => {
                let names = graph.baseline();
                let output = &mut self.diagnostics.writer;
                if let Err(error) = serde_json::to_writer_pretty(&mut *output, &names) {
                    tcx.dcx().fatal(error.to_string());
                }
                if let Err(error) = writeln!(output).and_then(|()| output.flush()) {
                    tcx.dcx().fatal(error.to_string());
                }
            }
            Baseline::Check(accepted) => {
                let reports = match graph.reports(tcx, accepted) {
                    Ok(reports) => reports,
                    Err(error) => tcx.dcx().fatal(error.to_string()),
                };
                if !reports.is_empty() {
                    self.status = ExitCode::FAILURE;
                }
                if let Err(error) = self.diagnostics.write(reports) {
                    tcx.dcx()
                        .fatal(format!("shapelint diagnostics output: {error}"));
                }
            }
        }
        Compilation::Stop
    }
}

pub(crate) fn run(
    mut args: Vec<String>,
    mut arguments: impl Iterator<Item = String>,
    mut diagnostics: Diagnostics,
    style: shapelint::Style,
) -> ExitCode {
    let mut baseline = None;
    while let Some(arg) = arguments.next() {
        match arg.as_str() {
            "--baseline" | "--emit-baseline" if let Some(_) = baseline => {
                eprintln!("shapelint-driver module-cycles: select one baseline option");
                return ExitCode::FAILURE;
            }
            "--emit-baseline" => baseline = Some(Baseline::Emit),
            "--baseline" => {
                let Some(path) = arguments.next() else {
                    eprintln!("shapelint-driver module-cycles: --baseline requires a path");
                    return ExitCode::FAILURE;
                };
                let groups =
                    std::fs::read(&path).and_then(|bytes| Ok(serde_json::from_slice(&bytes)?));
                match groups {
                    Ok(groups) => baseline = Some(Baseline::Check(groups)),
                    Err(error) => {
                        eprintln!(
                            "shapelint-driver module-cycles: could not read baseline {path}: {error}"
                        );
                        return ExitCode::FAILURE;
                    }
                }
            }
            "-h" | "--help" => {
                println!("Usage: shapelint-driver module-cycles [--emit-baseline | --baseline FILE] [--format FORMAT] <rustc arguments>

Checks sibling module cycles in one crate. --emit-baseline writes the current groups as JSON.
--baseline FILE reports groups outside the saved baseline. Findings exit with status 1.");
                return ExitCode::SUCCESS;
            }
            _ => {
                if let Err(error) =
                    diagnostics.parse_or_forward(arg, &mut arguments, &mut args, style)
                {
                    eprintln!("shapelint-driver: {error}");
                    return ExitCode::FAILURE;
                }
            }
        }
    }
    let mut cycles = Cycles {
        baseline: baseline.unwrap_or_else(|| Baseline::Check(Vec::new())),
        diagnostics,
        status: ExitCode::SUCCESS,
    };
    match crate::compile(args, &mut cycles) {
        ExitCode::SUCCESS => cycles.status,
        status => status,
    }
}
