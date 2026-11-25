use crate::values::{ExportValue, StoreValue};
use std::cell::RefCell;
use std::io::Write;
use std::path::{Path, PathBuf};

use rustc_data_structures::fingerprint::Fingerprint;
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_hir::def_id::{CrateNum, DefId, DefPathHash, LOCAL_CRATE};
use rustc_middle::mir::Local;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::{BytePos, FileName, Span, Symbol};
use serde::{Deserialize, Serialize};

use crate::contracts::graph::{ConditionId, ExprId, FlowNodeId, Graph, NodeId, TargetNode};
use crate::contracts::{self, Summary};
use crate::{calls, protocols};

mod sequences;
mod trees;
use trees::{Expression, Flow, FlowNode, Generic, Node, Predicate};

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("could not read summary {path}: {source}")]
    Read {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("could not create staged artifact beside {path}: {source}")]
    Create {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("could not write staged artifact for {path}: {source}")]
    Stage {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("could not publish artifact {path}: {source}")]
    Publish {
        path: PathBuf,
        #[source]
        source: std::io::Error,
    },
    #[error("invalid summary {path}: {source}")]
    Decode {
        path: PathBuf,
        #[source]
        source: serde_json::Error,
    },
    #[error("could not encode summary: {0}")]
    Encode(#[from] serde_json::Error),
    #[error("incompatible summary: {0}")]
    Incompatible(String),
    #[error("summary type metadata: {0}")]
    TypeStructure(#[from] calls::TypeStructureError),
    #[error(transparent)]
    Capacity(#[from] contracts::graph::CapacityError),
    #[error("summary source: {0}")]
    Source(#[from] shapelint::LintError),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
struct Definition(u64, u64);

impl Definition {
    fn from_def(tcx: TyCtxt<'_>, def: DefId) -> Self {
        let (krate, local) = tcx.def_path_hash(def).0.split();
        Self(krate.as_u64(), local.as_u64())
    }

    fn resolve(self, tcx: TyCtxt<'_>) -> Result<DefId, Error> {
        let hash = DefPathHash(Fingerprint::new(self.0, self.1));
        let crates = std::iter::once(LOCAL_CRATE).chain(tcx.crates(()).iter().copied());
        if let None = crates
            .into_iter()
            .find(|krate| tcx.stable_crate_id(*krate) == hash.stable_crate_id())
        {
            return Err(Error::Incompatible(format!(
                "definition {self:?} belongs to an unavailable crate"
            )));
        }
        tcx.def_path_hash_to_def_id(hash)
            .ok_or_else(|| Error::Incompatible(format!("definition {self:?} is unavailable")))
    }
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Artifact {
    format: String,
    compiler: String,
    target: String,
    producer: Definition,
    crate_hash: String,
    sources: Vec<Source>,
    crates: Vec<(Definition, String)>,
    dependencies: Vec<Dependency>,
    summaries: Vec<(Definition, Function)>,
    nodes: Vec<Node>,
    flows: Vec<FlowNode>,
    guard_sequences: Vec<sequences::Node<Predicate>>,
    argument_sequences: Vec<sequences::Node<Expression>>,
    invalidated_sequences: Vec<sequences::Node<Invalidated>>,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Dependency {
    definition: Definition,
    hash: String,
    metadata: PathBuf,
}

#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Source {
    name: String,
    text: String,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Location {
    source: usize,
    start: u32,
    end: u32,
    origin: Origin,
}
#[derive(Serialize, Deserialize)]
enum Origin {
    Source,
    Macro,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Identity {
    origin: (Definition, usize),
    fields: Vec<usize>,
    calls: Vec<(Definition, usize)>,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ValueOrigin {
    def: Definition,
    name: Option<String>,
    adt: Option<Definition>,
    identity: Option<Identity>,
}
#[derive(Serialize, Deserialize)]
enum Arithmetic {
    Add(Integer),
    Subtract(Integer),
    WrappingSubtract(u64),
}
#[derive(Serialize, Deserialize)]
enum Integer {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
}
#[derive(Serialize, Deserialize)]
enum Order {
    Less,
    LessEqual,
    Equal,
    NotEqual,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
enum Operation {
    Condition,
    Subtraction {
        left: Option<String>,
        right: Option<String>,
    },
    Unsupported(String),
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Consumer {
    def: Definition,
    location: Location,
    operation: Operation,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Invalidated {
    condition: Predicate,
    def: Definition,
    location: Location,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Requirement {
    invalidated: sequences::Root<Invalidated>,
    consumer: Consumer,
    condition: Predicate,
    guards: sequences::Root<Predicate>,
    location: Location,
}
#[derive(Serialize, Deserialize)]
enum Writes {
    None,
    Arguments(Vec<usize>),
    Unknown,
}
#[derive(Serialize, Deserialize)]
enum Behavior {
    Pure,
    Calls(Vec<Definition>),
    Unknown,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Check {
    basis: contracts::CheckBasis<sequences::Root<Predicate>>,
    loop_writes: Option<Writes>,
    condition: Predicate,
    guards: sequences::Root<Predicate>,
    location: Location,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Call {
    basis: contracts::CheckBasis<sequences::Root<Predicate>>,
    target: Target,
    arguments: sequences::Root<Expression>,
    guards: sequences::Root<Predicate>,
    location: Location,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Return {
    value: Expression,
    guards: sequences::Root<Predicate>,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Construction {
    owner: Definition,
    value: Expression,
    guards: sequences::Root<Predicate>,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Obligation {
    name: String,
    location: Location,
    flow: Flow,
    guards: sequences::Root<Predicate>,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ProtocolReturn {
    name: String,
    argument: usize,
    flow: Flow,
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Function {
    protocol_checks: Vec<Obligation>,
    protocol_returns: Vec<ProtocolReturn>,
    inspections: Vec<Expression>,
    escapes: Vec<Definition>,
    escaped_arguments: Vec<usize>,
    behavior: Behavior,
    loops: Vec<Location>,
    checks: Vec<Check>,
    requirements: Vec<Requirement>,
    calls: Vec<Call>,
    returns: Vec<Return>,
    constructions: Vec<Construction>,
    mutations: Vec<Definition>,
    output: Option<Definition>,
}

struct Encoder<'a, 'tcx, 'g> {
    source_inputs: &'a crate::diagnostics::Sources,
    graph: &'a Graph<'g>,
    nodes: RefCell<Vec<Node>>,
    flows: RefCell<Vec<FlowNode>>,
    guard_sequences: RefCell<sequences::Encoder<'g, ConditionId<'g>, Predicate>>,
    argument_sequences: RefCell<sequences::Encoder<'g, ExprId<'g>, Expression>>,
    invalidated_sequences:
        RefCell<sequences::Encoder<'g, contracts::InvalidatedFact<ConditionId<'g>>, Invalidated>>,
    flow_indices: RefCell<FxHashMap<FlowNodeId<'g>, usize>>,
    node_indices: RefCell<FxHashMap<NodeId<'g>, usize>>,
    tcx: TyCtxt<'tcx>,
    sources: RefCell<Vec<Source>>,
    files: RefCell<FxHashMap<BytePos, usize>>,
    referenced: RefCell<FxHashSet<CrateNum>>,
}

impl<'g> Encoder<'_, '_, 'g> {
    fn definition(&self, def: DefId) -> Definition {
        self.referenced.borrow_mut().insert(def.krate);
        Definition::from_def(self.tcx, def)
    }
    fn location(&self, owner: DefId, span: Span) -> Result<Location, Error> {
        let origin = match crate::diagnostics::source_span(self.tcx, owner, span) {
            Some(_) => Origin::Source,
            None => Origin::Macro,
        };
        let span = span.source_callsite();
        let file = self.tcx.sess.source_map().lookup_source_file(span.lo());
        let source = match self.files.borrow().get(&file.start_pos) {
            Some(index) => Some(*index),
            None => None,
        };
        let source = match source {
            Some(index) => index,
            None => {
                let input = self.source_inputs.input(file.as_ref())?;
                let mut sources = self.sources.borrow_mut();
                let index = sources.len();
                sources.push(Source {
                    name: input.name.to_string(),
                    text: input.as_ref().to_owned(),
                });
                self.files.borrow_mut().insert(file.start_pos, index);
                index
            }
        };
        Ok(Location {
            source,
            start: (span.lo() - file.start_pos).0,
            end: (span.hi() - file.start_pos).0,
            origin,
        })
    }
    fn origin(&self, origin: &contracts::Origin) -> ValueOrigin {
        ValueOrigin {
            def: self.definition(origin.def),
            name: origin.name.clone(),
            adt: origin.adt.map(|def| self.definition(def)),
            identity: origin
                .identity
                .as_ref()
                .map(|identity| self.identity(identity)),
        }
    }
    fn identity(&self, identity: &contracts::Identity) -> Identity {
        Identity {
            origin: (
                self.definition(identity.origin.0),
                identity.origin.1.as_usize(),
            ),
            fields: identity.fields.clone(),
            calls: identity
                .calls
                .iter()
                .map(|(def, local)| (self.definition(*def), local.as_usize()))
                .collect(),
        }
    }
    fn function(
        &self,
        owner: DefId,
        summary: crate::contracts::summaries::SummaryId<'g>,
    ) -> Result<Function, Error> {
        let summary = self.graph[summary];
        let mut function = Function {
            protocol_checks: self
                .graph
                .items(summary.protocol_checks)
                .map(|check| {
                    Ok(Obligation {
                        name: check.name.to_string(),
                        location: self.location(owner, check.span)?,
                        flow: self.flow(&check.flow)?,
                        guards: self.guard_sequences.borrow_mut().root(
                            self.graph.as_ref(),
                            check.guards,
                            |value| Ok(self.intern::<Predicate>(value)),
                        )?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            protocol_returns: self
                .graph
                .items(summary.protocol_returns)
                .map(|returned| {
                    Ok(ProtocolReturn {
                        name: returned.name.to_string(),
                        argument: returned.argument,
                        flow: self.flow(&returned.flow)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            inspections: self
                .graph
                .items(summary.inspections)
                .map(|value| self.intern::<Expression>(value))
                .collect(),
            escaped_arguments: self.graph.members(summary.escaped_arguments).collect(),
            escapes: self
                .graph
                .members(summary.escapes)
                .map(|def| self.definition(def))
                .collect(),
            behavior: match summary.behavior {
                contracts::summaries::BehaviorNode::Pure => Behavior::Pure,
                contracts::summaries::BehaviorNode::Unknown => Behavior::Unknown,
                contracts::summaries::BehaviorNode::Calls(defs) => Behavior::Calls(
                    self.graph
                        .members(defs)
                        .map(|def| self.definition(def))
                        .collect(),
                ),
            },
            loops: self
                .graph
                .items(summary.loops)
                .map(|span| self.location(owner, *span))
                .collect::<Result<_, _>>()?,
            checks: self
                .graph
                .items(summary.checks)
                .map(|check| {
                    Ok(Check {
                        basis: match &check.basis {
                            contracts::CheckBasis::Expression => contracts::CheckBasis::Expression,
                            contracts::CheckBasis::ControlFlow(basis) => {
                                contracts::CheckBasis::ControlFlow(
                                    self.guard_sequences.borrow_mut().root(
                                        self.graph.as_ref(),
                                        *basis,
                                        |value| Ok(self.intern::<Predicate>(value)),
                                    )?,
                                )
                            }
                        },
                        loop_writes: check.loop_writes.as_ref().map(|writes| match writes {
                            contracts::Writes::None => Writes::None,
                            contracts::Writes::Unknown => Writes::Unknown,
                            contracts::Writes::Arguments(arguments) => {
                                Writes::Arguments(self.graph.members(*arguments).collect())
                            }
                        }),
                        condition: self.intern::<Predicate>(&check.condition),
                        guards: self.guard_sequences.borrow_mut().root(
                            self.graph.as_ref(),
                            check.guards,
                            |value| Ok(self.intern::<Predicate>(value)),
                        )?,
                        location: self.location(owner, check.span)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            requirements: self
                .graph
                .items(summary.requirements)
                .map(|requirement| {
                    let consumer = self.graph[requirement.consumer];
                    Ok(Requirement {
                        invalidated: self.invalidated_sequences.borrow_mut().root(
                            self.graph.as_ref(),
                            requirement.invalidated,
                            |value| {
                                Ok(Invalidated {
                                    condition: self.intern::<Predicate>(&value.condition),
                                    def: self.definition(value.def),
                                    location: self.location(value.def, value.span)?,
                                })
                            },
                        )?,
                        consumer: Consumer {
                            def: self.definition(consumer.def),
                            location: self.location(consumer.def, consumer.span)?,
                            operation: match consumer.operation {
                                contracts::summaries::OperationNode::Condition => {
                                    Operation::Condition
                                }
                                contracts::summaries::OperationNode::Subtraction {
                                    left,
                                    right,
                                } => Operation::Subtraction {
                                    left: left.map(|id| self.graph[id].to_owned()),
                                    right: right.map(|id| self.graph[id].to_owned()),
                                },
                                contracts::summaries::OperationNode::Unsupported(reason) => {
                                    Operation::Unsupported(self.graph[reason].to_owned())
                                }
                            },
                        },
                        condition: self.intern::<Predicate>(&requirement.condition),
                        guards: self.guard_sequences.borrow_mut().root(
                            self.graph.as_ref(),
                            requirement.guards,
                            |value| Ok(self.intern::<Predicate>(value)),
                        )?,
                        location: self.location(owner, requirement.span)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            calls: self
                .graph
                .items(summary.calls)
                .map(|call| {
                    Ok(Call {
                        basis: match &call.basis {
                            contracts::CheckBasis::Expression => contracts::CheckBasis::Expression,
                            contracts::CheckBasis::ControlFlow(basis) => {
                                contracts::CheckBasis::ControlFlow(
                                    self.guard_sequences.borrow_mut().root(
                                        self.graph.as_ref(),
                                        *basis,
                                        |value| Ok(self.intern::<Predicate>(value)),
                                    )?,
                                )
                            }
                        },
                        target: self.target(&call.target),
                        arguments: self.argument_sequences.borrow_mut().root(
                            self.graph.as_ref(),
                            call.arguments,
                            |value| Ok(self.intern::<Expression>(value)),
                        )?,
                        guards: self.guard_sequences.borrow_mut().root(
                            self.graph.as_ref(),
                            call.guards,
                            |value| Ok(self.intern::<Predicate>(value)),
                        )?,
                        location: self.location(owner, call.span)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            returns: self
                .graph
                .items(summary.returns)
                .map(|value| {
                    Ok(Return {
                        value: self.intern::<Expression>(&value.value),
                        guards: self.guard_sequences.borrow_mut().root(
                            self.graph.as_ref(),
                            value.guards,
                            |value| Ok(self.intern::<Predicate>(value)),
                        )?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            constructions: self
                .graph
                .items(summary.constructions)
                .map(|value| {
                    Ok(Construction {
                        owner: self.definition(value.owner),
                        value: self.intern::<Expression>(&value.value),
                        guards: self.guard_sequences.borrow_mut().root(
                            self.graph.as_ref(),
                            value.guards,
                            |value| Ok(self.intern::<Predicate>(value)),
                        )?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            mutations: self
                .graph
                .members(summary.mutations)
                .map(|def| self.definition(def))
                .collect(),
            output: summary.output.map(|def| self.definition(def)),
        };
        function.escaped_arguments.sort_unstable();
        function.escapes.sort_by_key(|def| (def.0, def.1));
        function.mutations.sort_by_key(|def| (def.0, def.1));
        if let Behavior::Calls(defs) = &mut function.behavior {
            defs.sort_by_key(|def| (def.0, def.1));
        }
        for check in &mut function.checks {
            if let Some(Writes::Arguments(arguments)) = &mut check.loop_writes {
                arguments.sort_unstable();
            }
        }
        Ok(function)
    }
}

impl From<ty::UintTy> for Integer {
    fn from(value: ty::UintTy) -> Self {
        match value {
            ty::UintTy::U8 => Self::U8,
            ty::UintTy::U16 => Self::U16,
            ty::UintTy::U32 => Self::U32,
            ty::UintTy::U64 => Self::U64,
            ty::UintTy::U128 => Self::U128,
            ty::UintTy::Usize => Self::Usize,
        }
    }
}
impl From<Integer> for ty::UintTy {
    fn from(value: Integer) -> Self {
        match value {
            Integer::U8 => Self::U8,
            Integer::U16 => Self::U16,
            Integer::U32 => Self::U32,
            Integer::U64 => Self::U64,
            Integer::U128 => Self::U128,
            Integer::Usize => Self::Usize,
        }
    }
}

struct Decoder<'tcx, 'g> {
    nodes: Vec<NodeId<'g>>,
    flows: Vec<FlowNodeId<'g>>,
    guard_sequences: sequences::Decoder<'g, Predicate, ConditionId<'g>>,
    argument_sequences: sequences::Decoder<'g, Expression, ExprId<'g>>,
    invalidated_sequences:
        sequences::Decoder<'g, Invalidated, contracts::InvalidatedFact<ConditionId<'g>>>,
    tcx: TyCtxt<'tcx>,
    sources: Vec<(BytePos, String)>,
    validated: FxHashSet<CrateNum>,
    definitions: RefCell<FxHashMap<Definition, DefId>>,
}

impl<'g> Decoder<'_, 'g> {
    fn definition(&self, definition: Definition) -> Result<DefId, Error> {
        if let Some(&def) = self.definitions.borrow().get(&definition) {
            return Ok(def);
        }
        let def = definition.resolve(self.tcx)?;
        if !self.validated.contains(&def.krate) {
            return Err(Error::Incompatible(format!(
                "summary definition {definition:?} has no validated crate identity"
            )));
        }
        self.definitions.borrow_mut().insert(definition, def);
        Ok(def)
    }
    fn location(&self, location: Location) -> Result<Span, Error> {
        let (start, text) = self
            .sources
            .get(location.source)
            .ok_or_else(|| Error::Incompatible("summary source index is out of range".into()))?;
        if let None = text.get(location.start as usize..location.end as usize) {
            return Err(Error::Incompatible(
                "summary source range is invalid".into(),
            ));
        }
        let span = Span::with_root_ctxt(
            *start + BytePos(location.start),
            *start + BytePos(location.end),
        );
        Ok(match location.origin {
            Origin::Source => span,
            Origin::Macro => self.tcx.with_stable_hashing_context(|context| {
                let expansion = rustc_span::hygiene::ExpnData::default(
                    rustc_span::hygiene::ExpnKind::Macro(
                        rustc_span::hygiene::MacroKind::Bang,
                        Symbol::intern("imported_macro"),
                    ),
                    span,
                    self.tcx.sess.edition(),
                    None,
                    None,
                );
                let expansion = rustc_span::hygiene::LocalExpnId::fresh(expansion, context);
                span.apply_mark(
                    expansion.to_expn_id(),
                    rustc_span::hygiene::Transparency::Opaque,
                )
            }),
        })
    }
    fn origin(&self, origin: ValueOrigin) -> Result<contracts::Origin, Error> {
        Ok(contracts::Origin {
            def: self.definition(origin.def)?,
            name: origin.name,
            adt: origin.adt.map(|def| self.definition(def)).transpose()?,
            identity: origin
                .identity
                .map(|identity| self.identity(identity))
                .transpose()?,
        })
    }
    fn identity(&self, identity: Identity) -> Result<contracts::Identity, Error> {
        Ok(contracts::Identity {
            origin: (
                self.definition(identity.origin.0)?,
                Local::from_usize(identity.origin.1),
            ),
            fields: identity.fields,
            calls: identity
                .calls
                .into_iter()
                .map(|(def, local)| Ok((self.definition(def)?, Local::from_usize(local))))
                .collect::<Result<_, Error>>()?,
        })
    }
    fn function(
        &self,
        summary: Function,
        graph: &mut Graph<'g>,
    ) -> Result<
        Summary<
            'g,
            ExprId<'g>,
            ConditionId<'g>,
            TargetNode<'g>,
            crate::contracts::graph::FlowId<'g>,
        >,
        Error,
    > {
        Ok(Summary {
            protocol_checks: summary
                .protocol_checks
                .into_iter()
                .map(|check| {
                    Ok(protocols::Obligation {
                        name: Symbol::intern(&check.name),
                        span: self.location(check.location)?,
                        flow: self.flow(check.flow)?,
                        guards: self
                            .guard_sequences
                            .root(crate::sequence::Sequence::EMPTY, check.guards)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            protocol_returns: summary
                .protocol_returns
                .into_iter()
                .map(|returned| {
                    Ok(protocols::Return {
                        name: Symbol::intern(&returned.name),
                        argument: returned.argument,
                        flow: self.flow(returned.flow)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            inspections: summary
                .inspections
                .into_iter()
                .map(|value| self.expression(value))
                .collect::<Result<_, _>>()?,
            escaped_arguments: summary.escaped_arguments.into_iter().collect(),
            escapes: summary
                .escapes
                .into_iter()
                .map(|def| self.definition(def))
                .collect::<Result<_, _>>()?,
            behavior: match summary.behavior {
                Behavior::Pure => contracts::Behavior::Pure,
                Behavior::Unknown => contracts::Behavior::Unknown,
                Behavior::Calls(defs) => contracts::Behavior::Calls(
                    defs.into_iter()
                        .map(|def| self.definition(def))
                        .collect::<Result<_, _>>()?,
                ),
            },
            loops: summary
                .loops
                .into_iter()
                .map(|location| self.location(location))
                .collect::<Result<_, _>>()?,
            checks: summary
                .checks
                .into_iter()
                .map(|check| {
                    Ok(contracts::Check {
                        basis: match check.basis {
                            contracts::CheckBasis::Expression => contracts::CheckBasis::Expression,
                            contracts::CheckBasis::ControlFlow(basis) => {
                                contracts::CheckBasis::ControlFlow(
                                    self.guard_sequences
                                        .root(crate::sequence::Sequence::EMPTY, basis)?,
                                )
                            }
                        },
                        loop_writes: check
                            .loop_writes
                            .map(|writes| -> Result<_, Error> {
                                Ok(match writes {
                                    Writes::None => contracts::Writes::None,
                                    Writes::Unknown => contracts::Writes::Unknown,
                                    Writes::Arguments(arguments) => {
                                        contracts::Writes::Arguments(graph.argument_set(arguments)?)
                                    }
                                })
                            })
                            .transpose()?,
                        condition: self.predicate(check.condition)?,
                        guards: self
                            .guard_sequences
                            .root(crate::sequence::Sequence::EMPTY, check.guards)?,
                        span: self.location(check.location)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            requirements: summary
                .requirements
                .into_iter()
                .map(|requirement| {
                    Ok(contracts::Requirement {
                        invalidated: self
                            .invalidated_sequences
                            .root(crate::sequence::Sequence::EMPTY, requirement.invalidated)?,
                        consumer: contracts::Consumer {
                            def: self.definition(requirement.consumer.def)?,
                            span: self.location(requirement.consumer.location)?,
                            operation: match requirement.consumer.operation {
                                Operation::Condition => contracts::Operation::Condition,
                                Operation::Subtraction { left, right } => {
                                    contracts::Operation::Subtraction { left, right }
                                }
                                Operation::Unsupported(reason) => {
                                    contracts::Operation::Unsupported(reason)
                                }
                            },
                        },
                        condition: self.predicate(requirement.condition)?,
                        guards: self
                            .guard_sequences
                            .root(crate::sequence::Sequence::EMPTY, requirement.guards)?,
                        span: self.location(requirement.location)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            calls: summary
                .calls
                .into_iter()
                .map(|call| {
                    Ok(contracts::Call {
                        basis: match call.basis {
                            contracts::CheckBasis::Expression => contracts::CheckBasis::Expression,
                            contracts::CheckBasis::ControlFlow(basis) => {
                                contracts::CheckBasis::ControlFlow(
                                    self.guard_sequences
                                        .root(crate::sequence::Sequence::EMPTY, basis)?,
                                )
                            }
                        },
                        target: self.target(call.target, graph)?,
                        arguments: self
                            .argument_sequences
                            .root(crate::sequence::Sequence::EMPTY, call.arguments)?,
                        guards: self
                            .guard_sequences
                            .root(crate::sequence::Sequence::EMPTY, call.guards)?,
                        span: self.location(call.location)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            returns: summary
                .returns
                .into_iter()
                .map(|value| {
                    Ok(contracts::Return {
                        value: self.expression(value.value)?,
                        guards: self
                            .guard_sequences
                            .root(crate::sequence::Sequence::EMPTY, value.guards)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            constructions: summary
                .constructions
                .into_iter()
                .map(|value| {
                    Ok(contracts::Construction {
                        owner: self.definition(value.owner)?,
                        value: self.expression(value.value)?,
                        guards: self
                            .guard_sequences
                            .root(crate::sequence::Sequence::EMPTY, value.guards)?,
                    })
                })
                .collect::<Result<_, Error>>()?,
            mutations: summary
                .mutations
                .into_iter()
                .map(|def| self.definition(def))
                .collect::<Result<_, _>>()?,
            output: summary.output.map(|def| self.definition(def)).transpose()?,
        })
    }
}

pub fn export<'g>(
    tcx: TyCtxt<'_>,
    analyzed: &crate::pipeline::Analyzed<'g>,
    graph: &Graph<'g>,
    path: &Path,
    metadata: &[u8],
    source_inputs: &crate::diagnostics::Sources,
) -> Result<(), Error> {
    let crate::pipeline::Summaries {
        definitions: summaries,
        coverage,
    } = analyzed.as_ref();
    let directory = match path.parent() {
        Some(directory) if !directory.as_os_str().is_empty() => directory,
        Some(_) | None => Path::new("."),
    };
    let directory = std::fs::canonicalize(directory).map_err(|source| Error::Read {
        path: directory.to_owned(),
        source,
    })?;
    let stem = path
        .file_stem()
        .ok_or_else(|| Error::Incompatible("summary output path must name a file".into()))?;
    let mut metadata_name = std::ffi::OsString::from("lib");
    metadata_name.push(stem);
    metadata_name.push(format!("-{}.rmeta", tcx.crate_hash(LOCAL_CRATE).to_hex()));
    let metadata_path = directory.join(metadata_name);
    let encoder = Encoder {
        source_inputs,
        graph,
        nodes: RefCell::new(Vec::new()),
        flows: RefCell::new(Vec::new()),
        guard_sequences: RefCell::default(),
        argument_sequences: RefCell::default(),
        invalidated_sequences: RefCell::default(),
        flow_indices: RefCell::new(FxHashMap::default()),
        node_indices: RefCell::new(FxHashMap::default()),
        tcx,
        sources: RefCell::new(Vec::new()),
        files: RefCell::new(FxHashMap::default()),
        referenced: RefCell::new(FxHashSet::default()),
    };
    let mut definitions: Vec<_> = summaries.iter().collect();
    definitions.sort_by_key(|(def, _)| tcx.def_path_hash(**def));
    let summaries = definitions
        .into_iter()
        .map(|(def, summary)| Ok((encoder.definition(*def), encoder.function(*def, *summary)?)))
        .collect::<Result<_, Error>>()?;
    let producer = encoder.definition(LOCAL_CRATE.as_def_id());
    let mut crates: Vec<_> = std::iter::once(LOCAL_CRATE)
        .chain(coverage.iter().copied())
        .map(|krate| {
            (
                encoder.definition(krate.as_def_id()),
                tcx.crate_hash(krate).to_hex(),
            )
        })
        .collect();
    crates.sort_by_key(|(definition, _)| (definition.0, definition.1));
    let mut referenced: Vec<_> = encoder.referenced.borrow().iter().copied().collect();
    referenced.sort_by_key(|krate| tcx.stable_crate_id(*krate));
    let dependencies = referenced
        .into_iter()
        .map(|krate| {
            let metadata = if krate == LOCAL_CRATE {
                metadata_path.clone()
            } else {
                let source = tcx.used_crate_source(krate);
                let metadata = source
                    .rmeta
                    .as_ref()
                    .or(source.rlib.as_ref())
                    .or(source.dylib.as_ref())
                    .ok_or_else(|| {
                        Error::Incompatible(format!(
                            "summary dependency {} has no metadata source",
                            tcx.crate_name(krate)
                        ))
                    })?
                    .clone();
                std::fs::canonicalize(&metadata).map_err(|source| Error::Read {
                    path: metadata,
                    source,
                })?
            };
            Ok(Dependency {
                definition: Definition::from_def(tcx, krate.as_def_id()),
                hash: tcx.crate_hash(krate).to_hex(),
                metadata,
            })
        })
        .collect::<Result<_, Error>>()?;
    let artifact = Artifact {
        format: "shapelint-summary-8".into(),
        compiler: tcx.sess.cfg_version.into(),
        target: tcx.sess.target.llvm_target.to_string(),
        producer,
        crate_hash: tcx.crate_hash(LOCAL_CRATE).to_hex(),
        sources: encoder.sources.into_inner(),
        nodes: encoder.nodes.into_inner(),
        flows: encoder.flows.into_inner(),
        guard_sequences: encoder.guard_sequences.into_inner().nodes,
        argument_sequences: encoder.argument_sequences.into_inner().nodes,
        invalidated_sequences: encoder.invalidated_sequences.into_inner().nodes,
        crates,
        dependencies,
        summaries,
    };
    let bytes = serde_json::to_vec(&artifact)?;
    // A new summary never invalidates the metadata named by an older summary.
    publish(&metadata_path, metadata)?;
    publish(path, &bytes)
}

fn publish(path: &Path, bytes: &[u8]) -> Result<(), Error> {
    let directory = match path.parent() {
        Some(directory) if !directory.as_os_str().is_empty() => directory,
        Some(_) | None => Path::new("."),
    };
    let mut staged =
        tempfile::NamedTempFile::new_in(directory).map_err(|source| Error::Create {
            path: path.to_owned(),
            source,
        })?;
    staged.write_all(bytes).map_err(|source| Error::Stage {
        path: path.to_owned(),
        source,
    })?;
    staged.persist(path).map_err(|error| Error::Publish {
        path: path.to_owned(),
        source: error.error,
    })?;
    Ok(())
}

pub struct Imported<'g> {
    summaries: FxHashMap<DefId, crate::contracts::summaries::SummaryId<'g>>,
    coverage: FxHashSet<CrateNum>,
}

impl<'g> From<Imported<'g>> for crate::pipeline::Summaries<'g> {
    fn from(
        Imported {
            summaries,
            coverage,
        }: Imported<'g>,
    ) -> Self {
        Self {
            definitions: summaries,
            coverage,
        }
    }
}

#[derive(Default)]
pub struct Inputs {
    artifacts: Vec<(PathBuf, Artifact)>,
    pub externs: Vec<String>,
}

impl TryFrom<&[PathBuf]> for Inputs {
    type Error = Error;

    fn try_from(paths: &[PathBuf]) -> Result<Self, Self::Error> {
        let mut artifacts = Vec::with_capacity(paths.len());
        let mut dependencies = FxHashMap::default();
        for path in paths {
            let bytes = std::fs::read(path).map_err(|source| Error::Read {
                path: path.clone(),
                source,
            })?;
            let artifact: Artifact =
                serde_json::from_slice(&bytes).map_err(|source| Error::Decode {
                    path: path.clone(),
                    source,
                })?;
            for dependency in &artifact.dependencies {
                match dependencies.entry(dependency.definition) {
                    std::collections::hash_map::Entry::Vacant(entry) => {
                        entry.insert((dependency.hash.clone(), dependency.metadata.clone()));
                    }
                    std::collections::hash_map::Entry::Occupied(entry) => {
                        if entry.get().0 != dependency.hash {
                            return Err(Error::Incompatible(
                                "summary inputs disagree about a dependency crate hash".into(),
                            ));
                        }
                    }
                }
            }
            artifacts.push((path.clone(), artifact));
        }
        let mut externs = Vec::new();
        if !dependencies.is_empty() {
            externs.push("-Zunstable-options".into());
        }
        let mut dependencies: Vec<_> = dependencies.into_iter().collect();
        dependencies.sort_by_key(|(definition, _)| (definition.0, definition.1));
        for (definition, (_, metadata)) in dependencies {
            externs.push("--extern".into());
            externs.push(format!(
                "force,noprelude,nounused:shapelint_dependency_{:x}={}",
                definition.0,
                metadata.display()
            ));
        }
        Ok(Self { artifacts, externs })
    }
}

impl Inputs {
    pub fn import<'g>(self, tcx: TyCtxt<'_>, graph: &mut Graph<'g>) -> Result<Imported<'g>, Error> {
        let mut summaries = FxHashMap::default();
        let mut coverage = FxHashSet::default();
        for (path, artifact) in self.artifacts {
            if artifact.format != "shapelint-summary-8"
                || artifact.compiler != tcx.sess.cfg_version
                || artifact.target != tcx.sess.target.llvm_target.as_ref()
            {
                return Err(Error::Incompatible(format!(
                    "summary {} uses a different format, compiler, or target",
                    path.display()
                )));
            }
            let mut validated = FxHashSet::default();
            for Dependency {
                definition,
                hash,
                metadata: _,
            } in artifact.dependencies
            {
                let definition = definition.resolve(tcx)?;
                if definition.is_local() || tcx.crate_hash(definition.krate).to_hex() != hash {
                    return Err(Error::Incompatible(format!(
                        "summary {} references an incompatible dependency",
                        path.display()
                    )));
                }
                validated.insert(definition.krate);
            }
            let producer = artifact.producer.resolve(tcx)?;
            if producer.is_local()
                || !validated.contains(&producer.krate)
                || tcx.crate_hash(producer.krate).to_hex() != artifact.crate_hash
            {
                return Err(Error::Incompatible(format!(
                    "summary {} does not match its dependency metadata",
                    path.display()
                )));
            }
            for (definition, hash) in artifact.crates {
                let definition = definition.resolve(tcx)?;
                if definition.is_local()
                    || !validated.contains(&definition.krate)
                    || tcx.crate_hash(definition.krate).to_hex() != hash
                {
                    return Err(Error::Incompatible(format!(
                        "summary {} contains an incompatible dependency",
                        path.display()
                    )));
                }
                coverage.insert(definition.krate);
            }
            let sources = artifact
                .sources
                .into_iter()
                .map(|source| {
                    let file = tcx
                        .sess
                        .source_map()
                        .new_source_file(FileName::Custom(source.name), source.text);
                    let text = file
                        .src
                        .as_ref()
                        .expect("new source file retains its text")
                        .as_str()
                        .to_owned();
                    (file.start_pos, text)
                })
                .collect();
            let mut decoder = Decoder {
                nodes: Vec::new(),
                flows: Vec::new(),
                guard_sequences: sequences::Decoder::default(),
                argument_sequences: sequences::Decoder::default(),
                invalidated_sequences: sequences::Decoder::default(),
                tcx,
                sources,
                validated,
                definitions: RefCell::default(),
            };
            decoder.decode_nodes(artifact.nodes, graph)?;
            decoder.decode_flows(artifact.flows, graph)?;
            decoder.guard_sequences =
                sequences::Decoder::decode(artifact.guard_sequences, graph.as_mut(), |value| {
                    decoder.predicate(value)
                })?;
            decoder.argument_sequences =
                sequences::Decoder::decode(artifact.argument_sequences, graph.as_mut(), |value| {
                    decoder.expression(value)
                })?;
            decoder.invalidated_sequences = sequences::Decoder::decode(
                artifact.invalidated_sequences,
                graph.as_mut(),
                |value: Invalidated| {
                    Ok(contracts::InvalidatedFact {
                        condition: decoder.predicate(value.condition)?,
                        def: decoder.definition(value.def)?,
                        span: decoder.location(value.location)?,
                    })
                },
            )?;
            for (definition, summary) in artifact.summaries {
                let definition = decoder.definition(definition)?;
                if definition.is_local() {
                    return Err(Error::Incompatible(
                        "summary attempts to replace a local definition".into(),
                    ));
                }
                let summary = decoder.function(summary, graph)?;
                let summary = graph.freeze(summary)?;
                summaries.insert(definition, summary);
            }
        }
        let imported = Imported {
            summaries,
            coverage,
        };
        Ok(imported)
    }
}

#[derive(Serialize, Deserialize)]
enum Target {
    Direct(Instance),
    Indirect(Expression),
}
#[derive(Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Instance {
    def: Definition,
    args: Vec<Generic>,
    dispatch: Dispatch,
}
#[derive(Serialize, Deserialize)]
enum Dispatch {
    Item,
    Virtual,
    Shim,
    Unresolved,
}
#[derive(Serialize, Deserialize)]
enum Signed {
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
}
#[derive(Serialize, Deserialize)]
enum Float {
    F16,
    F32,
    F64,
    F128,
}
#[derive(Serialize, Deserialize)]
enum Mutability {
    Shared,
    Mutable,
}

impl<'g> Encoder<'_, '_, 'g> {
    fn target(&self, target: &TargetNode<'g>) -> Target {
        match target {
            TargetNode::Direct(instance) => {
                Target::Direct(self.instance(&self.graph.export_value(*instance)))
            }
            TargetNode::Indirect(value) => Target::Indirect(self.intern::<Expression>(value)),
        }
    }
}

impl<'g> Decoder<'_, 'g> {
    fn target(&self, target: Target, graph: &mut Graph<'g>) -> Result<TargetNode<'g>, Error> {
        Ok(match target {
            Target::Direct(instance) => {
                TargetNode::Direct(graph.intern_value(&self.instance(instance)?)?)
            }
            Target::Indirect(value) => TargetNode::Indirect(self.expression(value)?),
        })
    }
    fn instance(&self, instance: Instance) -> Result<calls::Instance, Error> {
        Ok(calls::Instance {
            def: self.definition(instance.def)?,
            args: instance
                .args
                .into_iter()
                .map(|value| self.generic(value))
                .collect::<Result<_, _>>()?,
            dispatch: match instance.dispatch {
                Dispatch::Item => calls::Dispatch::Item,
                Dispatch::Virtual => calls::Dispatch::Virtual,
                Dispatch::Shim => calls::Dispatch::Shim,
                Dispatch::Unresolved => calls::Dispatch::Unresolved,
            },
        })
    }
}
