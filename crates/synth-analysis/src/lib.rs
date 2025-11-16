//! Synth Analysis - Whole-program analysis
//!
//! This crate performs whole-program analysis on WebAssembly components,
//! including dependency analysis, memory layout, and call graph construction.

pub mod callgraph;
pub mod memory;
pub mod ssa;

// Stub implementations for PoC
pub use callgraph::*;
pub use memory::*;
pub use ssa::*;
