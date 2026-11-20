//! Refs #1763: a declared float local is read and written through the FP
//! register file.
//!
//! The executed comparison is
//! `crates/synth-oracle/tests/float_local_file_1763.rs`; this is the same
//! fact on the default `cargo test --workspace` build, read off the emitted
//! words. Encodings: `ldr d16,[sp]` = 0xFD4003F0, `ldr s16,[sp]` =
//! 0xBD4003F0, `fmov d0,d16` = 0x1E604200, `ldr x9,[sp]` = 0xF94003E9,
//! `mov x0,x9` = 0xAA0903E0.

use synth_backend_aarch64::AArch64Backend;
use synth_core::backend::{Backend, CompileConfig};
use synth_core::target::TargetSpec;
use synth_core::wasm_op::WasmOp;

fn words(ops: &[WasmOp], floats: &[u8]) -> Result<Vec<u32>, String> {
    let cfg = CompileConfig {
        target: TargetSpec::cortex_a53(),
        current_func_param_count: Some(1),
        current_func_declared_float_locals: floats.to_vec(),
        ..CompileConfig::default()
    };
    AArch64Backend::new()
        .compile_function("f", ops, &cfg)
        .map(|c| {
            c.code
                .chunks(4)
                .map(|w| u32::from_le_bytes([w[0], w[1], w[2], w[3]]))
                .collect()
        })
        .map_err(|e| e.to_string())
}

const SUB_SP_16: u32 = 0xD100_43FF;
const STR_XZR_SP: u32 = 0xF900_03FF;
const ADD_SP_16: u32 = 0x9100_43FF;
const RET: u32 = 0xD65F_03C0;
const FMOV_D0_D16: u32 = 0x1E60_4200;

/// `(param i32) (local T) local.get 1`: the result register follows the
/// local's declared type.
#[test]
fn a_never_written_float_local_is_returned_in_v0() {
    let get = [WasmOp::LocalGet(1), WasmOp::End];
    let frame = |load: u32, mov: u32| vec![SUB_SP_16, STR_XZR_SP, load, mov, ADD_SP_16, RET];
    // f64: `ldr d16,[sp]`, `fmov d0,d16`.
    assert_eq!(words(&get, &[8]).unwrap(), frame(0xFD40_03F0, FMOV_D0_D16));
    // f32: `ldr s16,[sp]` (4 bytes), then the same register move.
    assert_eq!(words(&get, &[4]).unwrap(), frame(0xBD40_03F0, FMOV_D0_D16));
    // An integer local, a table with no entry for the local, and any width
    // the decoder does not produce keep the GP read: `ldr x9,[sp]`, `mov x0,x9`.
    let gp = frame(0xF940_03E9, 0xAA09_03E0);
    for table in [&[0u8][..], &[], &[2]] {
        assert_eq!(words(&get, table).unwrap(), gp, "table {table:?}");
    }
}

/// The table is indexed by NON-PARAM local: entry 0 is local `num_params`.
/// A float entry must not turn a parameter read into a slot read.
#[test]
fn the_table_starts_after_the_parameters() {
    let get0 = [WasmOp::LocalGet(0), WasmOp::End];
    // An i32 parameter read: no frame, the value is already in x0.
    assert_eq!(words(&get0, &[8]).unwrap(), words(&get0, &[]).unwrap());
    // Local 2 is the SECOND table entry.
    let get2 = [WasmOp::LocalGet(2), WasmOp::End];
    let second = words(&get2, &[0, 8]).unwrap();
    assert!(
        second.contains(&0xFD40_07F0),
        "ldr d16,[sp,#8]: {second:x?}"
    );
    let first_only = words(&get2, &[8, 0]).unwrap();
    assert!(
        first_only.contains(&0xF940_07E9),
        "ldr x9,[sp,#8]: {first_only:x?}"
    );
}

/// A write to a float local takes an FP operand and stores it at the
/// local's width; the other file is refused, in both directions.
#[test]
fn a_float_local_is_written_from_the_fp_file() {
    let set = |c: WasmOp| [c, WasmOp::LocalSet(1), WasmOp::LocalGet(1), WasmOp::End];
    let d = words(&set(WasmOp::F64Const(1.5)), &[8]).unwrap();
    assert!(d.contains(&0xFD00_03F0), "str d16,[sp]: {d:x?}");
    let f = words(&set(WasmOp::F32Const(1.5)), &[4]).unwrap();
    assert!(f.contains(&0xBD00_03F0), "str s16,[sp]: {f:x?}");
    let tee = [WasmOp::F64Const(1.5), WasmOp::LocalTee(1), WasmOp::End];
    let t = words(&tee, &[8]).unwrap();
    assert!(t.contains(&0xFD00_03F0), "str d16,[sp]: {t:x?}");

    let e = words(&set(WasmOp::I64Const(1)), &[8]).unwrap_err();
    assert!(e.contains("local.set: expected FP operand, got GP"), "{e}");
    let e = words(&set(WasmOp::F64Const(1.5)), &[0]).unwrap_err();
    assert!(e.contains("local.set: expected GP operand, got FP"), "{e}");
    let e = words(
        &[WasmOp::I64Const(1), WasmOp::LocalTee(1), WasmOp::End],
        &[8],
    )
    .unwrap_err();
    assert!(e.contains("local.tee: expected FP operand, got GP"), "{e}");
}
