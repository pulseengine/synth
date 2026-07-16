//! AArch64 (A64) host-native backend for synth — **milestone 1** (#538).
//!
//! Goal (from #538): a minimal A64 integer-subset backend reachable via
//! `-b aarch64`, so synth output runs and debugs natively on arm64 dev hosts
//! (Apple Silicon, arm64 Linux/CI) instead of only under QEMU/Renode — and so a
//! third backend becomes a third differential oracle against the Thumb-2 and RV32
//! lowerings.
//!
//! ## Milestone status
//!
//! - **1a (this crate, now):** the verified A64 *encoder* (integer
//!   data-processing + `movz`/`movk` + `ret`, cross-checked against `clang`) and
//!   a minimal straight-line *selector* (params in `w0..w7`, i32
//!   add/sub/mul/and/or/xor + const, result to `w0`, `ret`). `compile_bytes`
//!   turns a leaf integer function's wasm ops into A64 machine code. Ops outside
//!   the subset return `Unsupported` — an honest loud-skip, never wrong code.
//! - **1b:** an `EM_AARCH64` relocatable-ELF emitter, the `Backend` trait impl,
//!   `-b aarch64` CLI wiring, and the native differential-execution acceptance
//!   probe (`synth compile add.wat -b aarch64` → link + run on the arm64 host,
//!   diff vs wasmtime).
//! - **2 (this milestone):** broaden the covered ops from the i32 core to the
//!   FULL i32 + i64 integer ALU — i64 x-form arithmetic/bitwise + const,
//!   i32/i64 shifts (`shl`/`shr_s`/`shr_u`) and rotates (`rotr`/`rotl`),
//!   `clz`/`ctz`, and the whole compare family (`eq/ne/lt/gt/le/ge` s+u, `eqz`)
//!   via `cmp`+`cset`. Every op is clang-byte-verified and native-differential
//!   green vs wasmtime (`scripts/repro/aarch64_m2_538_*.py`). Division
//!   (`div`/`rem`), `popcnt`, and floats are DELIBERATELY still declined — A64
//!   `SDIV`/`UDIV` don't trap, so a naive division lowering would be a silent
//!   miscompile; those need explicit trap guards in a later milestone.
//! - **3:** scalar floating point — f32/f64 const/add/sub/mul/div, abs/neg/sqrt,
//!   the full compare family, promote/demote, i32→float converts, and the
//!   f32↔i32 reinterprets, on a register-FILE-tagged value stack (GP vs FP).
//! - **4 (this milestone):** the #709-class SOUNDNESS conversions — the
//!   trapping float→int truncations (`i32.trunc_f32_{s,u}`,
//!   `i32.trunc_f64_{s,u}`) lowered behind an explicit WASM §4.3.3 domain guard
//!   (`fcmp` exact boundary + ordered `b.cond` + `brk`; A64 `FCVTZS`/`FCVTZU`
//!   alone SATURATE where WASM traps), plus `f32/f64.min/max` (A64
//!   `FMIN`/`FMAX` = IEEE 754-2019 minimum/maximum ≡ WASM NaN-propagation and
//!   -0<+0, execution-verified vs wasmtime) and `f32/f64.copysign` (GP-file bit
//!   surgery). Boundary-table execution differential:
//!   `scripts/repro/aarch64_m4_trunc_minmax_538_differential.py`.
//! - **later:** division-with-trap-guards, rounding ops, i64↔float converts,
//!   spilling, memory, control flow, calls, DWARF.

pub mod backend;
pub mod elf;
pub mod encoder;
pub mod selector;

pub use backend::AArch64Backend;
pub use selector::{SelectError, select};

/// Lower a single leaf integer function (wasm ops + declared param count) to A64
/// machine-code bytes (little-endian 32-bit words). Convenience over
/// [`selector::select`] for callers that want raw `.text` bytes.
pub fn compile_bytes(ops: &[synth_core::WasmOp], num_params: u32) -> Result<Vec<u8>, SelectError> {
    let words = select(ops, num_params)?;
    Ok(words.iter().flat_map(|w| w.to_le_bytes()).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use synth_core::WasmOp;

    #[test]
    fn compile_bytes_add_is_three_instructions() {
        let ops = vec![
            WasmOp::LocalGet(0),
            WasmOp::LocalGet(1),
            WasmOp::I32Add,
            WasmOp::End,
        ];
        let code = compile_bytes(&ops, 2).unwrap();
        assert_eq!(code.len(), 12); // add, mov, ret
        // last instruction is RET (0xD65F03C0, little-endian)
        assert_eq!(&code[8..12], &0xD65F_03C0u32.to_le_bytes());
    }
}
