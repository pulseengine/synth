//! Synth Core - Fundamental data structures and types
//!
//! This crate defines the core data structures used throughout the Synth synthesizer,
//! including representations for WebAssembly components, modules, and the intermediate
//! representation (IR) used for synthesis.

pub mod backend;
pub mod component;
pub mod dwarf_line;
pub mod error;
pub mod ir;
pub mod provenance;
pub mod safety_manifest;
pub mod sbom;
pub mod static_data_addr;
pub mod target;
pub mod wasm_decoder;
pub mod wasm_op;
pub mod wasm_stack_check;
pub mod wsc_facts;

pub use backend::*;
pub use component::*;
pub use error::{Error, Result};
pub use ir::*;
pub use safety_manifest::SafetyManifest;
pub use sbom::{CycloneDxSbom, SbomInputs};
pub use target::*;
pub use wasm_decoder::{
    CallIndirectGuards, DecodedModule, ElemSegmentInfo, FunctionOps, ImportEntry, ImportKind,
    TableGuards, WasmMemory, decode_wasm_functions, decode_wasm_module,
};
pub use wasm_op::WasmOp;
pub use wsc_facts::{FactKind, WSC_FACTS_SECTION_NAME, WscFact, WscFactsParse, parse_wsc_facts};
