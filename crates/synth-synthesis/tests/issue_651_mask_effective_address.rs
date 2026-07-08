//! #651: `--safety-bounds mask` must bound the EFFECTIVE address.
//!
//! WASM defines the effective address of a memory access as
//! `operand + offset` (u33). The broken lowering was
//! `(operand & R10) + offset` — the mask applied to the operand only, so any
//! non-zero static offset escaped the bound after the AND (by up to ~4 GiB
//! for `offset=0xffff0000`), and the AND used R10 = memory SIZE rather than
//! `size - 1`. The fixed lowering computes
//!
//! ```text
//! masked = min((operand + offset) & (size - 1), size - access_size)
//! ```
//!
//! These tests are an executable oracle: they run the direct selector with
//! `BoundsCheckConfig::Masking`, interpret the emitted address-computation
//! ops with a mini ARM interpreter (the `semantic_correctness.rs` pattern),
//! and check the wasm-side address the memory op actually accesses:
//!
//! 1. every access — including its FINAL byte (`+ access_size - 1`) — stays
//!    inside `[0, size)` (RED on the pre-fix lowering: the offset escapes);
//! 2. in-bounds accesses are executed at their EXACT wasm address;
//! 3. wasm-trapping accesses land where the documented wrap semantics say
//!    (`ea & (size-1)`, start clamped to `size - access_size`).

use synth_synthesis::{
    ArmInstruction, ArmOp, BoundsCheckConfig, Condition, InstructionSelector, Operand2, Reg,
    RuleDatabase, WasmOp,
};

/// Linear-memory size used throughout: one 64 KiB wasm page (the startup
/// default), power of two per the mask profile's contract.
const MEM_SIZE: u32 = 0x1_0000;

// ---------------------------------------------------------------------------
// Mini ARM interpreter (semantic_correctness.rs pattern): registers + NZCV,
// executed up to the first R11-based memory access, whose wasm-side effective
// address is the value under test.
// ---------------------------------------------------------------------------

fn reg_index(r: &Reg) -> usize {
    match r {
        Reg::R0 => 0,
        Reg::R1 => 1,
        Reg::R2 => 2,
        Reg::R3 => 3,
        Reg::R4 => 4,
        Reg::R5 => 5,
        Reg::R6 => 6,
        Reg::R7 => 7,
        Reg::R8 => 8,
        Reg::R9 => 9,
        Reg::R10 => 10,
        Reg::R11 => 11,
        Reg::R12 => 12,
        Reg::SP => 13,
        Reg::LR => 14,
        Reg::PC => 15,
    }
}

struct ArmState {
    regs: [u32; 16],
    flag_n: bool,
    flag_z: bool,
    flag_c: bool,
    flag_v: bool,
}

impl ArmState {
    fn new() -> Self {
        Self {
            regs: [0u32; 16],
            flag_n: false,
            flag_z: false,
            flag_c: false,
            flag_v: false,
        }
    }

    fn get(&self, r: &Reg) -> u32 {
        self.regs[reg_index(r)]
    }

    fn set(&mut self, r: Reg, val: u32) {
        self.regs[reg_index(&r)] = val;
    }

    fn resolve_operand2(&self, op2: &Operand2) -> u32 {
        match op2 {
            Operand2::Imm(v) => *v as u32,
            Operand2::Reg(r) => self.get(r),
            Operand2::RegShift { rm, .. } => self.get(rm),
        }
    }

    fn condition_met(&self, cond: &Condition) -> bool {
        match cond {
            Condition::EQ => self.flag_z,
            Condition::NE => !self.flag_z,
            Condition::LT => self.flag_n != self.flag_v,
            Condition::LE => self.flag_z || (self.flag_n != self.flag_v),
            Condition::GT => !self.flag_z && (self.flag_n == self.flag_v),
            Condition::GE => self.flag_n == self.flag_v,
            Condition::LO => !self.flag_c,
            Condition::LS => !self.flag_c || self.flag_z,
            Condition::HI => self.flag_c && !self.flag_z,
            Condition::HS => self.flag_c,
        }
    }
}

/// A captured R11-relative memory access: wasm-side effective address (the
/// register+immediate the op accesses relative to the linear-memory base)
/// and the access width in bytes.
struct Access {
    effective: u32,
    size: u32,
}

/// Interpret straight-line ops until the first R11-based load/store.
///
/// Panics on any unhandled COMPUTATIONAL op so an interpreter gap is loud
/// (the #209 Opt-1b lesson) rather than silently mis-modelled; structural
/// ops (labels, moves handled below) are executed or skipped explicitly.
fn run_until_access(instructions: &[ArmInstruction], addr_param: u32) -> Access {
    let mut state = ArmState::new();
    state.set(Reg::R0, addr_param); // param 0 (AAPCS)
    state.set(Reg::R10, MEM_SIZE); // startup contract: R10 = size in bytes

    for instr in instructions {
        // A memory access ends the address computation under test.
        let mem = match &instr.op {
            ArmOp::Ldr { addr, .. } | ArmOp::Str { addr, .. } => Some((addr, 4u32)),
            ArmOp::Ldrb { addr, .. } | ArmOp::Ldrsb { addr, .. } | ArmOp::Strb { addr, .. } => {
                Some((addr, 1))
            }
            ArmOp::Ldrh { addr, .. } | ArmOp::Ldrsh { addr, .. } | ArmOp::Strh { addr, .. } => {
                Some((addr, 2))
            }
            ArmOp::I64Ldr { addr, .. } | ArmOp::I64Str { addr, .. } => Some((addr, 8)),
            _ => None,
        };
        if let Some((addr, size)) = mem {
            assert_eq!(
                addr.base,
                Reg::R11,
                "linear-memory access must be R11-based"
            );
            let reg_part = addr.offset_reg.map(|r| state.get(&r)).unwrap_or(0);
            return Access {
                effective: reg_part.wrapping_add(addr.offset as u32),
                size,
            };
        }

        match &instr.op {
            ArmOp::Movw { rd, imm16 } => state.set(*rd, *imm16 as u32),
            ArmOp::Movt { rd, imm16 } => {
                let low = state.get(rd) & 0xFFFF;
                state.set(*rd, ((*imm16 as u32) << 16) | low);
            }
            ArmOp::Mov { rd, op2 } => {
                let v = state.resolve_operand2(op2);
                state.set(*rd, v);
            }
            ArmOp::Add { rd, rn, op2 } => {
                let v = state.get(rn).wrapping_add(state.resolve_operand2(op2));
                state.set(*rd, v);
            }
            ArmOp::Sub { rd, rn, op2 } => {
                let v = state.get(rn).wrapping_sub(state.resolve_operand2(op2));
                state.set(*rd, v);
            }
            ArmOp::And { rd, rn, op2 } => {
                let v = state.get(rn) & state.resolve_operand2(op2);
                state.set(*rd, v);
            }
            ArmOp::Cmp { rn, op2 } => {
                let a = state.get(rn);
                let b = state.resolve_operand2(op2);
                let result = a.wrapping_sub(b);
                state.flag_n = (result as i32) < 0;
                state.flag_z = result == 0;
                state.flag_c = a >= b;
                let (sa, sb, sr) = (a as i32, b as i32, result as i32);
                state.flag_v = (sa >= 0 && sb < 0 && sr < 0) || (sa < 0 && sb >= 0 && sr >= 0);
            }
            ArmOp::SelectMove { rd, rm, cond } => {
                if state.condition_met(cond) {
                    let v = state.get(rm);
                    state.set(*rd, v);
                }
            }
            // Structural / non-address ops the selector may emit around the
            // access (prologue, labels, epilogue).
            ArmOp::Label { .. } | ArmOp::Push { .. } | ArmOp::Pop { .. } | ArmOp::Bx { .. } => {}
            other => panic!("interpreter gap — unhandled op before the access: {other:?}"),
        }
    }
    panic!("no R11-based memory access found in the selected instructions");
}

/// Select `wasm_ops` (1 i32 param = the address operand) under Masking and
/// return the captured access for `addr_param`.
fn mask_access(wasm_ops: &[WasmOp], addr_param: u32) -> Access {
    let db = RuleDatabase::new();
    let mut selector =
        InstructionSelector::with_bounds_check(db.rules().to_vec(), BoundsCheckConfig::Masking);
    let instrs = selector
        .select_with_stack(wasm_ops, 1)
        .expect("selection under Masking must succeed");
    run_until_access(&instrs, addr_param)
}

/// The documented mask-profile semantics (wrap-not-trap, #651):
/// `min((operand + offset) & (size-1), size - access_size)` — u33-exact.
fn mask_model(operand: u32, offset: u32, access_size: u32) -> u32 {
    let ea = operand as u64 + offset as u64; // u33, no truncation
    let masked = (ea & (MEM_SIZE as u64 - 1)) as u32;
    masked.min(MEM_SIZE - access_size)
}

/// Assert the access obeys the bound (final byte included) and lands exactly
/// where the mask semantics say.
fn check(access: &Access, operand: u32, offset: u32) {
    assert!(
        access.effective as u64 + access.size as u64 - 1 < MEM_SIZE as u64,
        "#651: access [{:#x}, {:#x}] escapes the {:#x}-byte bound",
        access.effective,
        access.effective as u64 + access.size as u64 - 1,
        MEM_SIZE
    );
    let expected = mask_model(operand, offset, access.size);
    assert_eq!(
        access.effective, expected,
        "#651: masked access at {:#x}, mask semantics require {:#x} \
         (operand {operand:#x}, offset {offset:#x}, size {})",
        access.effective, expected, access.size
    );
}

// ---------------------------------------------------------------------------
// RED on the pre-#651 lowering: in-bounds operand, offset escapes the bound.
// ---------------------------------------------------------------------------

/// gale's repro shape: `(i32.load offset=0xffff0000 (local.get 0))`. The old
/// lowering computed `(operand & R10) + 0xffff0000` — ~4 GiB past the bound.
#[test]
fn load_huge_offset_stays_bounded_651() {
    let ops = [
        WasmOp::LocalGet(0),
        WasmOp::I32Load {
            offset: 0xffff_0000,
            align: 4,
        },
    ];
    let access = mask_access(&ops, 0x100);
    check(&access, 0x100, 0xffff_0000);
    // The u33 fold: (0x100 + 0xffff0000) & 0xffff == 0x100.
    assert_eq!(access.effective, 0x100);
}

/// Small offset, in-bounds operand near the top: old lowering read
/// `offset` bytes past the bound.
#[test]
fn load_small_offset_wraps_not_escapes_651() {
    let ops = [
        WasmOp::LocalGet(0),
        WasmOp::I32Load {
            offset: 0x100,
            align: 4,
        },
    ];
    // operand in-bounds (0xFFFC), ea = 0x100FC >= size: wasm traps, mask wraps.
    let access = mask_access(&ops, 0xFFFC);
    check(&access, 0xFFFC, 0x100);
}

/// Store variant of the escape (the write side is the dangerous one).
#[test]
fn store_offset_stays_bounded_651() {
    let ops = [
        WasmOp::LocalGet(0),
        WasmOp::I32Const(0x7EAC0DE),
        WasmOp::I32Store {
            offset: 0xffff_0000,
            align: 4,
        },
    ];
    let access = mask_access(&ops, 0x40);
    check(&access, 0x40, 0xffff_0000);
}

// ---------------------------------------------------------------------------
// In-bounds accesses must be executed at their exact wasm address.
// ---------------------------------------------------------------------------

#[test]
fn in_bounds_access_address_preserved_651() {
    for (operand, offset) in [
        (0u32, 0u32),
        (0x100, 0x10),
        (0x100, 0xFF),  // ADD-imm ceiling
        (0x100, 0x100), // first materialized (MOVW) offset
        (0, MEM_SIZE - 4),
        (MEM_SIZE - 4, 0), // last legal word start
    ] {
        let ops = [WasmOp::LocalGet(0), WasmOp::I32Load { offset, align: 4 }];
        let access = mask_access(&ops, operand);
        check(&access, operand, offset);
        assert_eq!(
            access.effective,
            operand + offset,
            "in-bounds access must be address-preserving"
        );
    }
}

// ---------------------------------------------------------------------------
// Final-byte boundary (`offset + access_size - 1`, the #640-shaped rule).
// ---------------------------------------------------------------------------

/// A 4-byte load starting in the last 3 bytes would overhang the bound by up
/// to 3 bytes if only the start were masked; the clamp caps the start.
#[test]
fn word_load_final_byte_clamped_651() {
    let ops = [
        WasmOp::LocalGet(0),
        WasmOp::I32Load {
            offset: 0,
            align: 4,
        },
    ];
    for operand in [MEM_SIZE - 3, MEM_SIZE - 2, MEM_SIZE - 1] {
        let access = mask_access(&ops, operand);
        check(&access, operand, 0);
        assert_eq!(access.effective, MEM_SIZE - 4, "start clamped to size-4");
    }
}

/// i64 (8-byte) access: widest overhang, clamped to size-8.
#[test]
fn i64_load_final_byte_clamped_651() {
    let ops = [
        WasmOp::LocalGet(0),
        WasmOp::I64Load {
            offset: 0,
            align: 8,
        },
    ];
    let access = mask_access(&ops, MEM_SIZE - 1);
    assert_eq!(access.size, 8);
    check(&access, MEM_SIZE - 1, 0);
    assert_eq!(access.effective, MEM_SIZE - 8);
}

/// Byte access at the very last byte is legal and must NOT be clamped.
#[test]
fn byte_load_last_byte_exact_651() {
    let ops = [
        WasmOp::LocalGet(0),
        WasmOp::I32Load8U {
            offset: 0,
            align: 1,
        },
    ];
    let access = mask_access(&ops, MEM_SIZE - 1);
    assert_eq!(access.size, 1);
    check(&access, MEM_SIZE - 1, 0);
    assert_eq!(access.effective, MEM_SIZE - 1);
}

/// Subword (halfword) store boundary: offset folds + clamp to size-2.
#[test]
fn halfword_store_boundary_651() {
    let ops = [
        WasmOp::LocalGet(0),
        WasmOp::I32Const(0xBEEF),
        WasmOp::I32Store16 {
            offset: 1,
            align: 2,
        },
    ];
    // ea = (size-2) + 1 = size-1: final byte would be at `size` — clamped.
    let access = mask_access(&ops, MEM_SIZE - 2);
    assert_eq!(access.size, 2);
    check(&access, MEM_SIZE - 2, 1);
    assert_eq!(access.effective, MEM_SIZE - 2);
}
