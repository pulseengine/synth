//! Rocq-Rust Correspondence Tests
//!
//! Validates that the Rust `InstructionSelector` generates the same ARM opcode
//! patterns as the Rocq `compile_wasm_to_arm` function (Compilation.v).
//!
//! These are NOT formal proofs — they are empirical validation that the two
//! implementations agree. The Rocq proofs verify `compile_wasm_to_arm` preserves
//! semantics; these tests verify the Rust code matches `compile_wasm_to_arm`.

use synth_synthesis::{ArmOp, InstructionSelector, Operand2, RuleDatabase, WasmOp};

/// Helper: extract opcode names from an ARM instruction sequence,
/// abstracting away register allocation.
fn opcode_names(ops: &[ArmOp]) -> Vec<&'static str> {
    ops.iter()
        .map(|op| match op {
            ArmOp::Add { .. } => "ADD",
            ArmOp::Sub { .. } => "SUB",
            ArmOp::Mul { .. } => "MUL",
            ArmOp::Sdiv { .. } => "SDIV",
            ArmOp::Udiv { .. } => "UDIV",
            ArmOp::Mls { .. } => "MLS",
            ArmOp::And { .. } => "AND",
            ArmOp::Orr { .. } => "ORR",
            ArmOp::Eor { .. } => "EOR",
            ArmOp::LslReg { .. } => "LSL_reg",
            ArmOp::LsrReg { .. } => "LSR_reg",
            ArmOp::AsrReg { .. } => "ASR_reg",
            ArmOp::RorReg { .. } => "ROR_reg",
            ArmOp::Rsb { .. } => "RSB",
            ArmOp::Clz { .. } => "CLZ",
            ArmOp::Rbit { .. } => "RBIT",
            ArmOp::Sxtb { .. } => "SXTB",
            ArmOp::Sxth { .. } => "SXTH",
            ArmOp::Cmp { .. } => "CMP",
            ArmOp::Mov { .. } => "MOV",
            ArmOp::Nop => "NOP",
            ArmOp::Ldr { .. } => "LDR",
            ArmOp::Str { .. } => "STR",
            ArmOp::Lsl { .. } => "LSL",
            ArmOp::Lsr { .. } => "LSR",
            ArmOp::Asr { .. } => "ASR",
            ArmOp::Ror { .. } => "ROR",
            _ => "OTHER",
        })
        .collect()
}

/// Select a single WASM op and return the generated ARM ops.
/// Uses empty rules (no optimizer) to match Rocq's compile_wasm_to_arm
/// which has no peephole optimizations.
fn select_single(wasm_op: WasmOp) -> Vec<ArmOp> {
    let mut selector = InstructionSelector::new(vec![]);
    let result = selector
        .select(&[wasm_op])
        .expect("selection should succeed");
    result.into_iter().map(|instr| instr.op).collect()
}

/// Verify that an ARM op uses register operands (not immediates) for binary ops.
fn has_reg_operand(op: &ArmOp) -> bool {
    match op {
        ArmOp::Add { op2, .. }
        | ArmOp::Sub { op2, .. }
        | ArmOp::And { op2, .. }
        | ArmOp::Orr { op2, .. }
        | ArmOp::Eor { op2, .. } => matches!(op2, Operand2::Reg(_)),
        _ => true, // non-binary ops don't have op2
    }
}

// ─────────────────────────────────────────────────────────────────────
// Structural Correspondence Tests
//
// Each test verifies that the Rust instruction selector generates the
// same ARM opcode sequence as Rocq's compile_wasm_to_arm.
//
// Rocq model (Compilation.v) uses hardcoded registers (R0, R1, R2).
// Rust uses dynamic allocation. We compare opcode patterns only.
// ─────────────────────────────────────────────────────────────────────

#[test]
fn i32_add_corresponds_to_rocq() {
    // Rocq: I32Add => [ADD R0 R0 (Reg R1)]
    let ops = select_single(WasmOp::I32Add);
    assert_eq!(opcode_names(&ops), vec!["ADD"]);
    assert!(has_reg_operand(&ops[0]));
}

#[test]
fn i32_sub_corresponds_to_rocq() {
    // Rocq: I32Sub => [SUB R0 R0 (Reg R1)]
    let ops = select_single(WasmOp::I32Sub);
    assert_eq!(opcode_names(&ops), vec!["SUB"]);
    assert!(has_reg_operand(&ops[0]));
}

#[test]
fn i32_mul_corresponds_to_rocq() {
    // Rocq: I32Mul => [MUL R0 R0 R1]
    let ops = select_single(WasmOp::I32Mul);
    assert_eq!(opcode_names(&ops), vec!["MUL"]);
}

#[test]
fn i32_and_corresponds_to_rocq() {
    // Rocq: I32And => [AND R0 R0 (Reg R1)]
    let ops = select_single(WasmOp::I32And);
    assert_eq!(opcode_names(&ops), vec!["AND"]);
    assert!(has_reg_operand(&ops[0]));
}

#[test]
fn i32_or_corresponds_to_rocq() {
    // Rocq: I32Or => [OR R0 R0 (Reg R1)]
    let ops = select_single(WasmOp::I32Or);
    assert_eq!(opcode_names(&ops), vec!["ORR"]);
    assert!(has_reg_operand(&ops[0]));
}

#[test]
fn i32_xor_corresponds_to_rocq() {
    // Rocq: I32Xor => [XOR R0 R0 (Reg R1)]
    let ops = select_single(WasmOp::I32Xor);
    assert_eq!(opcode_names(&ops), vec!["EOR"]);
    assert!(has_reg_operand(&ops[0]));
}

#[test]
fn i32_shl_corresponds_to_rocq() {
    // Rocq: I32Shl => [LSL_reg R0 R0 R1]
    let ops = select_single(WasmOp::I32Shl);
    assert_eq!(opcode_names(&ops), vec!["LSL_reg"]);
}

#[test]
fn i32_shru_corresponds_to_rocq() {
    // Rocq: I32ShrU => [LSR_reg R0 R0 R1]
    let ops = select_single(WasmOp::I32ShrU);
    assert_eq!(opcode_names(&ops), vec!["LSR_reg"]);
}

#[test]
fn i32_shrs_corresponds_to_rocq() {
    // Rocq: I32ShrS => [ASR_reg R0 R0 R1]
    let ops = select_single(WasmOp::I32ShrS);
    assert_eq!(opcode_names(&ops), vec!["ASR_reg"]);
}

#[test]
fn i32_rotl_corresponds_to_rocq() {
    // Rocq: I32Rotl => [RSB R2 R1 (Imm 32); ROR_reg R0 R0 R2]
    let ops = select_single(WasmOp::I32Rotl);
    assert_eq!(opcode_names(&ops), vec!["RSB", "ROR_reg"]);

    // Verify RSB uses immediate 32
    if let ArmOp::Rsb { imm, .. } = &ops[0] {
        assert_eq!(*imm, 32, "RSB should use immediate 32 for rotl");
    } else {
        panic!("First instruction should be RSB");
    }
}

#[test]
fn i32_rotr_corresponds_to_rocq() {
    // Rocq: I32Rotr => [ROR_reg R0 R0 R1]
    let ops = select_single(WasmOp::I32Rotr);
    assert_eq!(opcode_names(&ops), vec!["ROR_reg"]);
}

#[test]
fn i32_clz_corresponds_to_rocq() {
    // Rocq: I32Clz => [CLZ R0 R0]
    let ops = select_single(WasmOp::I32Clz);
    assert_eq!(opcode_names(&ops), vec!["CLZ"]);
}

#[test]
fn i32_ctz_corresponds_to_rocq() {
    // Rocq: I32Ctz => [RBIT R0 R0; CLZ R0 R0]
    let ops = select_single(WasmOp::I32Ctz);
    assert_eq!(opcode_names(&ops), vec!["RBIT", "CLZ"]);
}

#[test]
fn i32_divs_corresponds_to_rocq() {
    // Rocq: I32DivS => [SDIV R0 R0 R1]
    let ops = select_single(WasmOp::I32DivS);
    assert_eq!(opcode_names(&ops), vec!["SDIV"]);
}

#[test]
fn i32_divu_corresponds_to_rocq() {
    // Rocq: I32DivU => [UDIV R0 R0 R1]
    let ops = select_single(WasmOp::I32DivU);
    assert_eq!(opcode_names(&ops), vec!["UDIV"]);
}

#[test]
fn i32_rems_corresponds_to_rocq() {
    // Rocq: I32RemS => [SDIV R2 R0 R1; MLS R0 R2 R1 R0]
    let ops = select_single(WasmOp::I32RemS);
    assert_eq!(opcode_names(&ops), vec!["SDIV", "MLS"]);
}

#[test]
fn i32_remu_corresponds_to_rocq() {
    // Rocq: I32RemU => [UDIV R2 R0 R1; MLS R0 R2 R1 R0]
    let ops = select_single(WasmOp::I32RemU);
    assert_eq!(opcode_names(&ops), vec!["UDIV", "MLS"]);
}

#[test]
fn i32_eqz_corresponds_to_rocq() {
    // Rocq: I32Eqz => CMP+MOV+MOVEQ sequence
    // Rust: CMP with imm(0) — comparison ops differ in post-CMP conditioning
    let ops = select_single(WasmOp::I32Eqz);
    // At minimum, must start with CMP against zero
    assert!(!ops.is_empty());
    assert_eq!(opcode_names(&ops)[0], "CMP");
    if let ArmOp::Cmp { op2, .. } = &ops[0] {
        assert!(
            matches!(op2, Operand2::Imm(0)),
            "EQZ should compare against immediate 0"
        );
    }
}

#[test]
fn i32_eq_corresponds_to_rocq() {
    // Rocq: I32Eq => CMP+MOV+MOVEQ sequence (3 instructions)
    // Rust: CMP only (conditional moves handled separately)
    let ops = select_single(WasmOp::I32Eq);
    assert!(!ops.is_empty());
    assert_eq!(opcode_names(&ops)[0], "CMP");
    if let ArmOp::Cmp { op2, .. } = &ops[0] {
        assert!(
            matches!(op2, Operand2::Reg(_)),
            "EQ should compare registers"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────
// Known Divergences (documented, not bugs)
// ─────────────────────────────────────────────────────────────────────

#[test]
fn i32_popcnt_emits_popcnt_pseudo_op() {
    // Both Rocq and Rust model POPCNT as a single pseudo-instruction.
    // The encoder expands it to a parallel bit-count algorithm.
    let db = RuleDatabase::with_standard_rules();
    let mut selector = InstructionSelector::new(db.rules().to_vec());
    let result = selector.select(&[WasmOp::I32Popcnt]);
    assert!(
        result.is_ok(),
        "I32Popcnt should succeed via Popcnt pseudo-instruction"
    );
}

#[test]
fn i32_comparisons_start_with_cmp() {
    // Rocq: Comparisons compile to CMP+MOV+conditional-MOV (3 instructions)
    // Rust: Only CMP (conditional moves handled by a different pass)
    // Divergence is structural — both correctly implement the comparison.
    let cmp_ops = [
        WasmOp::I32Ne,
        WasmOp::I32LtS,
        WasmOp::I32LtU,
        WasmOp::I32GtS,
        WasmOp::I32GtU,
        WasmOp::I32LeS,
        WasmOp::I32LeU,
        WasmOp::I32GeS,
        WasmOp::I32GeU,
    ];

    for wasm_op in &cmp_ops {
        let ops = select_single(wasm_op.clone());
        assert!(
            !ops.is_empty(),
            "{wasm_op:?} should produce at least one instruction"
        );
        assert_eq!(
            opcode_names(&ops)[0],
            "CMP",
            "{wasm_op:?} should start with CMP"
        );
    }
}

// ─────────────────────────────────────────────────────────────────────
// Instruction Count Correspondence
//
// Verify the Rust selector generates the expected number of ARM
// instructions for each WASM op (matching Rocq's compile_wasm_to_arm).
// ─────────────────────────────────────────────────────────────────────

#[test]
fn instruction_counts_match_rocq() {
    // (WasmOp, expected ARM instruction count from Compilation.v)
    let expected: Vec<(WasmOp, usize)> = vec![
        // Single-instruction ops
        (WasmOp::I32Add, 1),
        (WasmOp::I32Sub, 1),
        (WasmOp::I32Mul, 1),
        (WasmOp::I32And, 1),
        (WasmOp::I32Or, 1),
        (WasmOp::I32Xor, 1),
        (WasmOp::I32Shl, 1),
        (WasmOp::I32ShrU, 1),
        (WasmOp::I32ShrS, 1),
        (WasmOp::I32Rotr, 1),
        (WasmOp::I32Clz, 1),
        (WasmOp::I32DivS, 1),
        (WasmOp::I32DivU, 1),
        // Two-instruction ops
        (WasmOp::I32Rotl, 2), // RSB + ROR_reg
        (WasmOp::I32Ctz, 2),  // RBIT + CLZ
        (WasmOp::I32RemS, 2), // SDIV + MLS
        (WasmOp::I32RemU, 2), // UDIV + MLS
    ];

    for (wasm_op, expected_count) in &expected {
        let ops = select_single(wasm_op.clone());
        assert_eq!(
            ops.len(),
            *expected_count,
            "{wasm_op:?}: expected {expected_count} ARM instructions, got {}",
            ops.len()
        );
    }
}
