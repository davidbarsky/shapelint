#![feature(register_tool, rustc_private)]
#![register_tool(shapelint_tool)]

extern crate rustc_data_structures;
extern crate rustc_driver;
extern crate rustc_index;

mod arena;
mod memo;
pub mod persistent;
pub mod sequence;
