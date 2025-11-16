//! Synth Core - Fundamental data structures and types
//!
//! This crate defines the core data structures used throughout the Synth synthesizer,
//! including representations for WebAssembly components, modules, and the intermediate
//! representation (IR) used for synthesis.

pub mod component;
pub mod error;
pub mod ir;
pub mod target;

pub use component::*;
pub use error::{Error, Result};
pub use ir::*;
pub use target::*;
