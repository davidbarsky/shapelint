#![feature(register_tool, rustc_private)]
#![register_tool(shapelint_tool)]

extern crate rustc_abi;
extern crate rustc_arena;
extern crate rustc_borrowck;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_hir_pretty;
extern crate rustc_index;
extern crate rustc_interface;
extern crate rustc_metadata;
extern crate rustc_middle;
extern crate rustc_mir_transform;
extern crate rustc_span;
extern crate rustc_structures;

pub mod analysis;
mod architecture;
mod arena;
mod arena_induction;
pub use pipeline::artifacts;
pub mod callers;
pub mod calls;
pub mod contracts;
pub mod diagnostics;
pub mod hir_rules;
pub mod loops;
mod memo;
pub mod persistent;
pub mod pipeline;
pub mod protocols;
pub mod regions;
pub mod sequence;
pub mod standard;
pub mod states;
pub mod transfers;
pub mod values;

pub use pipeline::Located;
