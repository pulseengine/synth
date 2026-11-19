//! x86-64 (SysV AMD64) host-native backend for synth — lane X1, the skeleton
//! (RQ-91-X86SKEL, #1741; VCR-X86-001, approved 2026-11-18).
//!
//! `synth compile m.wat -b x86_64 [--relocatable]` lowers LEAF functions built
//! from `local.get` (of a parameter), `i32.add`, `return` and `end`, with at
//! most six i32 parameters and at most one i32 result, into a SysV ELF64
//! `ET_REL` (`EM_X86_64`) written by the SHARED object plan
//! (`synth_core::object_plan`). Everything else is refused loudly, by name —
//! except `nop`, which the shared decoder drops before the selector sees it, so
//! it compiles as nothing.
//!
//! Structure, after `synth-backend-aarch64`:
//! - [`inst`]: the instruction type, one variant per emitted form, and its
//!   AT&T printer;
//! - [`encoder`]: one encoding function per form, LLVM's canonical choice;
//! - [`selector`]: wasm ops to instructions, the register contract;
//! - [`backend`]: module checks, the object, the `Backend` registration.
//!
//! The oracles live outside the code they check: `tests/encoding_llvm_mc.rs`
//! (E1, byte equality with `llvm-mc -show-encoding`), `tests/encoding_iced.rs`
//! (E2/E3, iced-x86 decodes every emitted instruction to the requested text
//! and length, inside the baseline ISA level), `tests/decline_skeleton.rs`, and
//! the execution oracle in `crates/synth-oracle` (unicorn x86-64, CPU model
//! pinned to QEMU64, against kiln).
//!
//! The support level stays L3: x86-64 can reach at most L2 (no sound cycle
//! model exists for an out-of-order host, and no vendor x86 semantics exists in
//! Rocq — VCR-X86-001's costs 2 and 3).

pub mod backend;
pub mod encoder;
pub mod inst;
pub mod selector;

pub use backend::{X86_64Backend, X86Function, X86Object, compile_wasm};
pub use selector::{SelectError, select};
