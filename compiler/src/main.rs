#![feature(rustc_private)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir_transform;
extern crate rustc_session;
extern crate rustc_span;
extern crate rustc_structures;

use shapelint::{Style, render};
mod module_cycles;

use std::io::{BufWriter, IsTerminal, Write};

use std::process::ExitCode;
use std::sync::OnceLock;

use rustc_data_structures::steal::Steal;
use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::Res;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::intravisit::{self, Visitor};
use rustc_hir::{Item, ItemKind};
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

enum Output {
    Text(Style),
    Json,
    Record(Option<Style>),
}

#[derive(serde::Serialize)]
#[serde(tag = "record", rename_all = "snake_case")]
enum Record<'a> {
    Header {
        version: u32,
    },
    Source {
        id: usize,
        input: &'a shapelint::SourceInput,
    },
    Finding {
        finding: &'a shapelint::Finding,
        related: Vec<Related>,
        #[serde(skip_serializing_if = "Option::is_none")]
        rendered: Option<String>,
    },
    Workspace {
        facts: WorkspaceFacts,
    },
}

#[derive(serde::Serialize)]
struct WorkspaceFacts {
    traits: Vec<WorkspaceTrait>,
    implementations: Vec<WorkspaceImplementation>,
}

#[derive(serde::Serialize)]
struct WorkspaceTrait {
    identity: [u64; 2],
    path: String,
    span: shapelint::Span,
}

#[derive(serde::Serialize)]
struct WorkspaceImplementation {
    trait_identity: [u64; 2],
    path: String,
    span: shapelint::Span,
}

impl WorkspaceFacts {
    fn collect(tcx: TyCtxt<'_>) -> Self {
        let mut collector = WorkspaceCollector {
            tcx,
            facts: Self {
                traits: Vec::new(),
                implementations: Vec::new(),
            },
        };
        tcx.hir_visit_all_item_likes_in_crate(&mut collector);
        collector.facts
    }
}

struct WorkspaceCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    facts: WorkspaceFacts,
}

impl<'tcx> Visitor<'tcx> for WorkspaceCollector<'tcx> {
    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        match &item.kind {
            ItemKind::Trait { ident, .. } => {
                if let Some((path, span)) = source_location(self.tcx, ident.span) {
                    self.facts.traits.push(WorkspaceTrait {
                        identity: definition_identity(self.tcx, item.owner_id.def_id.to_def_id()),
                        path,
                        span,
                    });
                }
            }
            ItemKind::Impl(implementation) => {
                if let Some(trait_ref) = &implementation.of_trait
                    && let rustc_hir::ImplPolarity::Positive = trait_ref.polarity
                    && let Res::Def(_, trait_def) = trait_ref.trait_ref.path.res
                    && let Some((path, span)) = source_location(self.tcx, item.span)
                {
                    self.facts.implementations.push(WorkspaceImplementation {
                        trait_identity: definition_identity(self.tcx, trait_def),
                        path,
                        span,
                    });
                }
            }
            _ => {}
        }
        intravisit::walk_item(self, item);
    }
}

fn definition_identity(tcx: TyCtxt<'_>, def: rustc_hir::def_id::DefId) -> [u64; 2] {
    let (crate_hash, local_hash) = tcx.def_path_hash(def).0.split();
    [crate_hash.as_u64(), local_hash.as_u64()]
}

fn source_location(tcx: TyCtxt<'_>, span: rustc_span::Span) -> Option<(String, shapelint::Span)> {
    if span.is_dummy() || span.from_expansion() {
        return None;
    }
    let span = span.source_callsite();
    let file = tcx.sess.source_map().lookup_source_file(span.lo());
    if file.is_imported() || !file.contains(span.hi()) {
        return None;
    }
    let name = file.name.prefer_local_unconditionally().to_string();
    Some((
        name,
        shapelint::Span {
            start: file.original_relative_byte_pos(span.lo()).0,
            end: file.original_relative_byte_pos(span.hi()).0,
        },
    ))
}

#[derive(serde::Serialize)]
struct Related {
    source: usize,
    label: shapelint::Label,
}

enum CargoOutput {
    Check,
    Other,
}

struct Driver {
    cargo_output: CargoOutput,
    diagnostics: Diagnostics,
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
        if let CargoOutput::Check = self.cargo_output {
            use rustc_session::config::{OutFileName, OutputType};
            let outputs = &tcx.sess.opts.output_types;
            let actual: rustc_data_structures::fx::FxHashSet<_> = outputs.keys().copied().collect();
            let expected = rustc_data_structures::fx::FxHashSet::from_iter([
                OutputType::DepInfo,
                OutputType::Metadata,
            ]);
            if actual != expected {
                tcx.dcx()
                    .fatal("--cargo-check-only requires dep-info and metadata output");
            }
            for output in expected {
                match tcx.output_filenames(()).path(output) {
                    OutFileName::Real(_) => {}
                    OutFileName::Stdout => tcx
                        .dcx()
                        .fatal("--cargo-check-only requires dep-info and metadata output"),
                }
            }
        }
        let metadata = if let (Some(_), _) | (_, CargoOutput::Check) =
            (&self.summary_output, &self.cargo_output)
        {
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
        let sources = match pipeline::SourceFindings::collect(
            tcx,
            &session.sources,
            &shapelint::Config::default(),
        ) {
            Ok(sources) => sources,
            Err(error) => tcx.dcx().fatal(error.to_string()),
        };
        self.diagnostics.workspace = Some(WorkspaceFacts::collect(tcx));
        if let Err(error) = self.diagnostics.write(sources) {
            tcx.dcx()
                .fatal(format!("shapelint diagnostics output: {error}"));
        }
        if let CargoOutput::Check = self.cargo_output {
            tcx.report_unused_features();
            tcx.dcx().abort_if_errors();
        }
        Compilation::Stop
    }
}

struct Diagnostics {
    output: Output,
    writer: Box<dyn Write + Send>,
    workspace: Option<WorkspaceFacts>,
}

impl Diagnostics {
    fn parse_or_forward(
        &mut self,
        arg: String,
        arguments: &mut impl Iterator<Item = String>,
        rustc: &mut Vec<String>,
        style: Style,
    ) -> Result<(), String> {
        if arg == "--diagnostics-output" {
            let path = arguments
                .next()
                .ok_or("--diagnostics-output requires a path")?;
            let file = std::fs::File::create(&path)
                .map_err(|error| format!("could not create diagnostics output {path}: {error}"))?;
            self.writer = Box::new(BufWriter::new(file));
        } else if arg == "--format" || arg.starts_with("--format=") {
            let format = match arg.strip_prefix("--format=") {
                Some(format) => Some(format.to_owned()),
                None => arguments.next(),
            };
            self.output = match format.as_deref() {
                Some("text") => Output::Text(style),
                Some("json") => Output::Json,
                Some("record") => Output::Record(Some(style)),
                Some("record-json") => Output::Record(None),
                Some(_) | None => {
                    return Err("--format requires text, json, record, or record-json".into());
                }
            };
        } else {
            rustc.push(arg);
        }
        Ok(())
    }

    fn write(
        &mut self,
        sources: impl IntoIterator<Item = pipeline::SourceFindings>,
    ) -> std::io::Result<()> {
        if let Output::Record(_) = self.output {
            serde_json::to_writer(&mut self.writer, &Record::Header { version: 2 })?;
            writeln!(self.writer)?;
            if let Some(facts) = self.workspace.take() {
                serde_json::to_writer(&mut self.writer, &Record::Workspace { facts })?;
                writeln!(self.writer)?;
            }
        }
        let mut source_ids = rustc_data_structures::fx::FxHashMap::default();
        // Keep each source allocation alive while its address identifies it in this stream.
        let mut shared_sources = Vec::new();
        for pipeline::SourceFindings { input, findings } in sources {
            match self.output {
                Output::Text(style) => write!(self.writer, "{}", render(&findings, &input, style))?,
                Output::Json => {
                    for finding in findings {
                        serde_json::to_writer(&mut self.writer, &finding)?;
                        writeln!(self.writer)?;
                    }
                }
                Output::Record(style) => {
                    for mut finding in findings {
                        let rendered = style
                            .map(|style| render(std::slice::from_ref(&finding), &input, style));
                        let mut related = Vec::new();
                        for shapelint::Related { input, label } in
                            std::mem::take(&mut finding.related)
                        {
                            let text: &str = input.as_ref();
                            let key = (input.name.clone(), text.as_ptr() as usize, text.len());
                            let source = match source_ids.entry(key) {
                                std::collections::hash_map::Entry::Occupied(entry) => *entry.get(),
                                std::collections::hash_map::Entry::Vacant(entry) => {
                                    let id = shared_sources.len();
                                    serde_json::to_writer(
                                        &mut self.writer,
                                        &Record::Source { id, input: &input },
                                    )?;
                                    writeln!(self.writer)?;
                                    shared_sources.push(input);
                                    *entry.insert(id)
                                }
                            };
                            related.push(Related { source, label });
                        }
                        let record = Record::Finding {
                            finding: &finding,
                            related,
                            rendered,
                        };
                        serde_json::to_writer(&mut self.writer, &record)?;
                        writeln!(self.writer)?;
                    }
                }
            }
        }
        self.writer.flush()
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
    let style = match std::env::var("SHAPELINT_CARGO_COLOR").as_deref() {
        Ok("always") => Style::Ansi,
        Ok("never") => Style::Plain,
        Err(std::env::VarError::NotPresent) => match std::io::stdout().is_terminal() {
            true => Style::Ansi,
            false => Style::Plain,
        },
        Ok(_) | Err(std::env::VarError::NotUnicode(_)) => {
            eprintln!("shapelint-driver: SHAPELINT_CARGO_COLOR requires always or never");
            return ExitCode::FAILURE;
        }
    };
    let mut diagnostics = Diagnostics {
        output: Output::Text(style),
        writer: Box::new(BufWriter::new(std::io::stdout())),
        workspace: None,
    };
    let mut cargo_output = CargoOutput::Other;
    let mut arguments = std::env::args().peekable();
    let mut args: Vec<_> = arguments.next().into_iter().collect();
    if let Some(_) = arguments.next_if(|arg| arg == "module-cycles") {
        return module_cycles::run(args, arguments, diagnostics, style);
    }
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
            "--cargo-check-only" => cargo_output = CargoOutput::Check,
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
    let mut summary_inputs = match artifacts::Inputs::try_from(summary_paths.as_slice()) {
        Ok(inputs) => inputs,
        Err(error) => {
            eprintln!("shapelint-driver: {error}");
            return ExitCode::FAILURE;
        }
    };
    args.extend(std::mem::take(&mut summary_inputs.externs));
    let mut driver = Driver {
        cargo_output,
        diagnostics,
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
