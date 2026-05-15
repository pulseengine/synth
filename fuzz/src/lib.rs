//! Shared utilities for the synth fuzz harnesses.
//!
//! All harnesses operate on `synth_core::WasmOp` sequences. Because the
//! upstream `WasmOp` enum is large (~250 variants, several with `f32`/`f64`
//! payloads which lack the `Eq` impls some derives require), this crate
//! defines a compact `FuzzOp` mirror that:
//!
//!   * Derives `Arbitrary` so libfuzzer can generate it.
//!   * Concentrates on the most-error-prone op surfaces — i32 / i64 /
//!     conversion / control-flow — i.e. the surface where mis-compilations
//!     have historically lived (issues #93, #86, #82).
//!   * Lowers to `WasmOp` via a constant mapping, so a fuzz crash carries
//!     a deterministic, replayable path back to the compiler.
//!
//! Float and SIMD ops are deliberately excluded because:
//!   * Floats kill `Eq` derives downstream,
//!   * SIMD codegen lives in a separate sub-pipeline and is out of scope
//!     for #82's "ARM-backend instruction selection" framing.

pub mod common;

pub use common::{FuzzInput, FuzzOp, lower_arbitrary_to_wasm_ops};
