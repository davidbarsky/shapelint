#![feature(register_tool, rustc_private)]
#![register_tool(shapelint_tool)]

extern crate rustc_abi;
extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_index;
extern crate rustc_middle;
extern crate rustc_span;

mod arena;
pub mod calls;
pub mod contracts;
mod memo;
pub mod persistent;
pub mod sequence;
pub mod values;
