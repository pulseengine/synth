//! Synth Core - Fundamental data structures and types
//!
//! This crate defines the core data structures used throughout the Synth synthesizer,
//! including representations for WebAssembly components, modules, and the intermediate
//! representation (IR) used for synthesis.

pub mod backend;
pub mod component;
pub mod error;
pub mod ir;
pub mod target;
pub mod wasm_decoder;
pub mod wasm_op;

pub use backend::*;
pub use component::*;
pub use error::{Error, Result};
pub use ir::*;
pub use target::*;
pub use wasm_decoder::{
    decode_wasm_functions, decode_wasm_module, DecodedModule, FunctionOps, WasmMemory,
};
pub use wasm_op::WasmOp;
