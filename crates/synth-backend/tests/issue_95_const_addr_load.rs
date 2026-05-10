//! Issue #95 — constant-address load/store fold to base+offset addressing.
//!
//! Verifies that `(i32.const C) (i32.load offset=O)` and analogous store
//! sequences lower to a SINGLE Thumb-2 `LDR.W rd, [R11, #(C+O)]` (4 bytes)
//! instead of the previous `MOVW + MOVT + LDR.W` (10 bytes), when `C+O`
//! fits in the imm12 addressing-mode range and bounds checking is disabled
//! (the bare-metal default).
//!
//! See https://github.com/pulseengine/synth/issues/95

use synth_backend::ArmEncoder;
use synth_synthesis::{ArmOp, InstructionSelector, RuleDatabase, WasmOp};

/// Encode a sequence of ArmOps and return the total byte length.
fn encoded_size(ops: &[ArmOp]) -> usize {
    let enc = ArmEncoder::new_thumb2();
    ops.iter()
        .map(|op| enc.encode(op).expect("encoding failed").len())
        .sum()
}

/// Compile the WASM op sequence using the production stack selector
/// (no bounds checking — bare-metal default), then return all ARM ops
/// (excluding the function prologue Push/Sub-SP / epilogue Pop).
fn compile_body(wasm_ops: &[WasmOp], num_params: u32) -> Vec<ArmOp> {
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let instrs = selector
        .select_with_stack(wasm_ops, num_params)
        .expect("selection failed");
    instrs
        .into_iter()
        .map(|i| i.op)
        .filter(|op| {
            !matches!(
                op,
                ArmOp::Push { .. }
                    | ArmOp::Pop { .. }
                    | ArmOp::Sub {
                        rd: synth_synthesis::Reg::SP,
                        ..
                    }
                    | ArmOp::Add {
                        rd: synth_synthesis::Reg::SP,
                        ..
                    }
                    | ArmOp::Bx { .. }
            )
        })
        .collect()
}

/// Canonical issue-95 sequence: load from a const address with a small offset.
#[test]
fn canonical_const_addr_load_drops_from_10_to_4_bytes() {
    // (i32.const 0x100) (i32.load offset=8) — effective address = 0x108
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I32Load {
            offset: 8,
            align: 2,
        },
        WasmOp::End,
    ];
    let body = compile_body(&wasm, 0);

    // After the fold, the body should contain a SINGLE Ldr — no Movw/Movt
    // for the address.
    let movw_movt_count = body
        .iter()
        .filter(|op| matches!(op, ArmOp::Movw { .. } | ArmOp::Movt { .. }))
        .count();
    assert_eq!(
        movw_movt_count, 0,
        "issue #95 fold: const-addr load must NOT emit Movw/Movt; got body: {body:#?}"
    );

    let ldr_count = body
        .iter()
        .filter(|op| matches!(op, ArmOp::Ldr { .. }))
        .count();
    assert_eq!(ldr_count, 1, "expected exactly one Ldr; got {ldr_count}");

    // Encoded size of the load alone must be 4 bytes (Thumb-2 LDR.W imm12).
    let only_ldr: Vec<_> = body
        .iter()
        .filter(|op| matches!(op, ArmOp::Ldr { .. }))
        .cloned()
        .collect();
    assert_eq!(encoded_size(&only_ldr), 4, "folded LDR.W must be 4 bytes");
}

/// Negative path: when the effective offset exceeds imm12 (4095), the
/// compiler must fall back to the MOVW+MOVT path. This test guards that
/// the optimisation does not corrupt the fallback.
#[test]
fn const_addr_load_falls_back_when_offset_too_large() {
    // Effective address = 0x10008 — does NOT fit in imm12.
    let wasm = vec![
        WasmOp::I32Const(0x10000),
        WasmOp::I32Load {
            offset: 8,
            align: 2,
        },
        WasmOp::End,
    ];
    let body = compile_body(&wasm, 0);

    // Movw must be present (low half of 0x10000); Movt may or may not be
    // emitted depending on the const handler's branch (0x10000 needs Movt
    // too since high16=1).
    let has_movw = body.iter().any(|op| matches!(op, ArmOp::Movw { .. }));
    let has_movt = body.iter().any(|op| matches!(op, ArmOp::Movt { .. }));
    assert!(has_movw, "fallback path must emit Movw for 0x10000");
    assert!(
        has_movt,
        "fallback path must emit Movt for 0x10000 (high16=1)"
    );

    // The Ldr should still be there, with register-offset addressing.
    let ldr = body
        .iter()
        .find_map(|op| match op {
            ArmOp::Ldr { addr, .. } => Some(addr.clone()),
            _ => None,
        })
        .expect("fallback must still emit a Ldr");
    assert!(
        ldr.offset_reg.is_some(),
        "fallback Ldr should use register-offset addressing"
    );
}

/// Const-address store of a const value: the address Movw/Movt must be
/// dropped while the value Movw remains.
#[test]
fn canonical_const_addr_store_folds() {
    // (i32.const 0x100) (i32.const 42) (i32.store offset=4) — eff offset 0x104.
    let wasm = vec![
        WasmOp::I32Const(0x100),
        WasmOp::I32Const(42),
        WasmOp::I32Store {
            offset: 4,
            align: 2,
        },
        WasmOp::End,
    ];
    let body = compile_body(&wasm, 0);

    // Exactly ONE Movw should remain — the value materialization (42).
    let movw_count = body
        .iter()
        .filter(|op| matches!(op, ArmOp::Movw { .. }))
        .count();
    assert_eq!(
        movw_count, 1,
        "value Movw must remain, address Movw must be folded out; got: {body:#?}"
    );

    // Single Str with [R11, #0x104].
    let strs: Vec<_> = body
        .iter()
        .filter_map(|op| match op {
            ArmOp::Str { rd, addr } => Some((rd, addr.clone())),
            _ => None,
        })
        .collect();
    assert_eq!(strs.len(), 1);
    let (_rd, addr) = &strs[0];
    assert_eq!(addr.base, synth_synthesis::Reg::R11);
    assert_eq!(addr.offset, 0x104);
    assert!(addr.offset_reg.is_none());
}

/// Direct before/after byte-count comparison for the canonical issue-95
/// sequence. The fallback (non-folded) path emits MOVW+MOVT (address
/// materialisation, 8 bytes) plus an indexed LDR (4 bytes). The folded
/// path emits a single LDR.W with imm12 (4 bytes) — saving 8 bytes per
/// access. This test verifies the encoded byte count via the real encoder.
#[test]
fn canonical_load_before_vs_after_byte_count() {
    let enc = ArmEncoder::new_thumb2();

    // Folded: single LDR.W [R11, #0x108]
    let folded_seq = [ArmOp::Ldr {
        rd: synth_synthesis::Reg::R3,
        addr: synth_synthesis::MemAddr::imm(synth_synthesis::Reg::R11, 0x108),
    }];
    let folded_bytes: usize = folded_seq
        .iter()
        .map(|op| enc.encode(op).expect("encode").len())
        .sum();

    // Pre-fold (would-have-been): MOVW + MOVT for the address into a reg,
    // then LDR with register-offset addressing and immediate offset 8.
    // This mirrors what the compiler emitted before the fold.
    let unfolded_seq = [
        ArmOp::Movw {
            rd: synth_synthesis::Reg::R12,
            imm16: 0x0100,
        },
        ArmOp::Movt {
            rd: synth_synthesis::Reg::R12,
            imm16: 0x0000,
        },
        ArmOp::Ldr {
            rd: synth_synthesis::Reg::R3,
            addr: synth_synthesis::MemAddr::reg_imm(
                synth_synthesis::Reg::R11,
                synth_synthesis::Reg::R12,
                8,
            ),
        },
    ];
    let unfolded_bytes: usize = unfolded_seq
        .iter()
        .map(|op| enc.encode(op).expect("encode").len())
        .sum();

    // Folded path is 4 bytes. Unfolded was 14 bytes (Movw 4 + Movt 4 +
    // ADD-scratch 4 + LDR.W reg 4) per the encoder's reg_imm Ldr lowering;
    // even taking only the strict 3-instruction sequence as the lower bound,
    // the savings are at least 6 bytes.
    assert_eq!(folded_bytes, 4, "folded LDR.W must be 4 bytes");
    assert!(
        unfolded_bytes >= 10,
        "unfolded path should be at least 10 bytes; got {unfolded_bytes}"
    );
    assert!(
        folded_bytes < unfolded_bytes,
        "fold must reduce byte count: {folded_bytes} < {unfolded_bytes}"
    );

    // Validate against the actual selector output for the canonical sequence.
    let body = compile_body(
        &[
            WasmOp::I32Const(0x100),
            WasmOp::I32Load {
                offset: 8,
                align: 2,
            },
            WasmOp::End,
        ],
        0,
    );
    let selector_bytes: usize = body
        .iter()
        .map(|op| enc.encode(op).expect("encode").len())
        .sum();
    assert_eq!(
        selector_bytes, 4,
        "selector must emit 4 bytes for the folded canonical sequence"
    );
}

/// Sub-word load fold: i32.load8_u, i32.load16_s.
#[test]
fn const_addr_subword_loads_fold() {
    // i32.load8_u
    let wasm = vec![
        WasmOp::I32Const(0x10),
        WasmOp::I32Load8U {
            offset: 0x20,
            align: 1,
        },
        WasmOp::End,
    ];
    let body = compile_body(&wasm, 0);
    let movw = body
        .iter()
        .filter(|o| matches!(o, ArmOp::Movw { .. }))
        .count();
    assert_eq!(movw, 0, "i32.load8_u with const addr should fold");
    let ldrb = body
        .iter()
        .find_map(|op| match op {
            ArmOp::Ldrb { addr, .. } => Some(addr.clone()),
            _ => None,
        })
        .expect("must emit Ldrb");
    assert_eq!(ldrb.base, synth_synthesis::Reg::R11);
    assert_eq!(ldrb.offset, 0x30);

    // i32.load16_s
    let wasm = vec![
        WasmOp::I32Const(0x40),
        WasmOp::I32Load16S {
            offset: 2,
            align: 2,
        },
        WasmOp::End,
    ];
    let body = compile_body(&wasm, 0);
    assert_eq!(
        body.iter()
            .filter(|o| matches!(o, ArmOp::Movw { .. }))
            .count(),
        0
    );
    let ldrsh = body
        .iter()
        .find_map(|op| match op {
            ArmOp::Ldrsh { addr, .. } => Some(addr.clone()),
            _ => None,
        })
        .expect("must emit Ldrsh");
    assert_eq!(ldrsh.base, synth_synthesis::Reg::R11);
    assert_eq!(ldrsh.offset, 0x42);
}
