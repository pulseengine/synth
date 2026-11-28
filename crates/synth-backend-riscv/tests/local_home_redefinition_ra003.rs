//! VCR-RA-003 (RV32) refused CORRECT functions that write a frame-resident
//! wasm local twice before reading it.
//!
//! The RV32 validator's spill-slot rule ("a slot is overwritten while its
//! first value is still unreloaded, then reloaded") policed EVERY `sp`
//! offset, including the permanent frame home of a wasm local — which the
//! selector writes at every `local.set`/`local.tee` (and at the #457/#990
//! entry zero-init) and reads at every `local.get`. A redefinition is not an
//! aliased spill, so these functions were refused with
//! `SpillSlotAliased`, and nothing was emitted:
//!
//! - `redefine`: `local.set 1; local.set 1; local.get 1`, the minimal shape;
//! - `zero_init_then_tee`: a local written inside a `br`-targeted block is
//!   zero-initialised at entry (the write does not dominate the read after
//!   the block), and the block's own `local.tee` + `local.get` sit in the
//!   SAME straight-line segment as that zero store — the shape of
//!   `core::fmt::num::<impl Display for i32>::fmt` (func 218 of a Rust
//!   wasip1 hello world) that surfaced this.
//!
//! RED on 56ccaa34: both return `Err(.. VCR-RA-003 .. SpillSlotAliased ..)`.
//! The executed comparison against kiln is
//! `crates/synth-oracle/tests/rv32_local_home_redef_ra003.rs`.

use synth_core::backend::{Backend, CompileConfig};
use synth_core::target::TargetSpec;
use synth_core::wasm_op::WasmOp::{self, *};

fn compile(ops: &[WasmOp]) -> Result<Vec<u8>, String> {
    let cfg = CompileConfig {
        target: TargetSpec::riscv32imac(),
        current_func_param_count: Some(1),
        ..CompileConfig::default()
    };
    synth_backend_riscv::RiscVBackend::new()
        .compile_function("f", ops, &cfg)
        .map(|c| c.code)
        .map_err(|e| e.to_string())
}

fn assert_accepted(what: &str, ops: &[WasmOp]) {
    match compile(ops) {
        Ok(code) => assert!(!code.is_empty(), "{what}: empty code"),
        Err(e) => panic!("{what}: refused: {e}"),
    }
}

#[test]
fn redefine_a_frame_local_before_reading_it_ra003() {
    // (param i32) (result i32) (local i32)
    //   local.get 0  local.set 1
    //   local.get 0  i32.const 1  i32.add  local.set 1
    //   local.get 1
    assert_accepted(
        "redefine",
        &[
            LocalGet(0),
            LocalSet(1),
            LocalGet(0),
            I32Const(1),
            I32Add,
            LocalSet(1),
            LocalGet(1),
            End,
        ],
    );
}

#[test]
fn zero_init_then_tee_in_one_segment_ra003() {
    // (param i32) (result i32) (local i32)
    //   block  local.get 0  local.tee 1  local.get 1  i32.xor  br_if 0  end
    //   local.get 1
    assert_accepted(
        "zero_init_then_tee",
        &[
            Block,
            LocalGet(0),
            LocalTee(1),
            LocalGet(1),
            I32Xor,
            BrIf(0),
            End,
            LocalGet(1),
            End,
        ],
    );
}
