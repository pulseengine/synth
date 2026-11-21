//! x86-64 (SysV AMD64) host-native backend for synth — lanes X1 (the skeleton,
//! RQ-91-X86SKEL), X2 (the straight-line integer core, RQ-91-X86ALU), X3-X4
//! (the frame, locals, division and bit counts, RQ-91-X86FRAME) and X5
//! (structured control flow, RQ-91-X86CTRL); #1741, VCR-X86-001, approved
//! 2026-11-18.
//!
//! `synth compile m.wat -b x86_64 [--relocatable]` lowers LEAF functions of
//! i32/i64 integer code — `local.get`/`set`/`tee` on parameters
//! and zero-initialised locals, `const`, add/sub/mul/and/or/xor, shifts and
//! rotates, compares and `eqz`, the extensions and `wrap`, `div`/`rem` with
//! wasm's traps as explicit `ud2` guards, `clz`/`ctz`/`popcnt` from baseline
//! instructions, `select`, `drop`, `nop`, `return`, `end`, and `block`,
//! `loop`, `if`/`else`, `br`, `br_if`, `br_table` (at most 16 targets) and
//! `unreachable` over block types of zero or one i32/i64 result — with at most
//! six i32/i64 parameters and at most one i32/i64 result, into a SysV ELF64
//! `ET_REL` (`EM_X86_64`) written by the SHARED object plan
//! (`synth_core::object_plan`). Every function has an `rbp` frame; parameters
//! are homed to it and an operand stack deeper than the temporaries spills to
//! it. Everything else is refused loudly, by name: calls, memory, globals,
//! floats, block parameters and multi-value blocks, and a frame above one
//! page. The control-frame bookkeeping is shared with AArch64
//! (`synth_core::lower`).
//!
//! Structure, after `synth-backend-aarch64`:
//! - [`inst`]: the instruction type, one variant per emitted form, and its
//!   AT&T printer;
//! - [`encoder`]: one encoding function per form, LLVM's canonical choice;
//! - [`rules`]: the lowering table, one row per integer op;
//! - [`selector`]: wasm ops to instructions, the frame and register contract;
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
pub mod rules;
pub mod selector;

pub use backend::{X86_64Backend, X86Function, X86Object, compile_wasm};
pub use selector::{BlockSig, SelectError, Ty, select, select_function};
