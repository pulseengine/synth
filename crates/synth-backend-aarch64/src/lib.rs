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
//! - **1b (next):** an `EM_AARCH64` relocatable-ELF emitter, the `Backend` trait
//!   impl, `-b aarch64` CLI wiring, and the native differential-execution
//!   acceptance probe (`synth compile add.wat -b aarch64` → link + run on the
//!   arm64 host, diff vs wasmtime).
//! - **later:** spilling, i64, floats, memory, control flow, calls, DWARF.

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
