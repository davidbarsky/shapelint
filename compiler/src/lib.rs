#![feature(register_tool, rustc_private)]
#![register_tool(shapelint_tool)]

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_span;

pub mod analysis;
mod arena;
pub mod diagnostics;
pub mod protocols;
pub mod standard;
pub mod states;
pub mod transfers;
extern crate rustc_arena;
extern crate rustc_borrowck;
extern crate rustc_hir_pretty;
mod arena_induction;
pub mod callers;
pub mod calls;
pub mod contracts;
pub mod loops;
mod memo;
pub mod persistent;
pub mod pipeline;
pub mod sequence;
pub mod values;
pub use pipeline::artifacts;
pub mod hir_rules;
pub use diagnostics::Located;
mod architecture;
