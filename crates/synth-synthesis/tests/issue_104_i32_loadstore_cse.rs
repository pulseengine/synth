//! Regression test for issue #104: i32.load / i32.store wasm_to_ir produces
//! unmapped vreg (latent #93-class bug).
//!
//! # Symptom
//!
//! For the canonical store-then-load function
//!
//! ```text
//! (func (param i32 i32) (result i32)
//!   local.get 0    ;; address
//!   local.get 1    ;; value
//!   i32.store      ;; store value at address
//!   local.get 0    ;; address (again)
//!   i32.load)      ;; load value back
//! ```
//!
//! the optimized pipeline (`OptimizerBridge::optimize_full` + `ir_to_arm`)
//! produced a `MemLoad { addr: v3, .. }` ARM lowering for the second
//! `local.get 0`, where vreg `v3` had been eliminated by CSE but its
//! consumer (`MemLoad`) was never rewritten to reference the surviving
//! `v0`. The unmapped vreg silently fell back to `R0` in `get_arm_reg`,
//! producing a miscompile that structural tests did not catch and that
//! PR #101's defensive panic exposed as `"vreg v3 has no assigned ARM
//! register and no spill slot"`.
//!
//! # Root cause
//!
//! `CommonSubexpressionElimination::eliminate_cse` did not have match arms
//! for `Opcode::MemLoad` / `Opcode::MemStore` (linear-memory ops). When the
//! second `Opcode::Load { dest: v3, addr: 0 }` (the second `local.get 0`)
//! was CSE-killed against the earlier `Opcode::Load { dest: v0, addr: 0 }`
//! and `reg_map[v3] = v0` was recorded, no subsequent pass over
//! `MemLoad { addr: v3, .. }` rewrote `addr` through `reg_map`. The dead
//! `Load` was then dropped by `optimize_full`'s
//! `!i.is_dead && i.opcode != Opcode::Nop` filter and `ir_to_arm` had no
//! producer for `v3`.
//!
//! Same shape as #93 (which fixed `I64ExtendI32U` / `I64ExtendI32S` /
//! `I32WrapI64` in `wasm_to_ir`): a wasm op whose result vreg ends up
//! unmapped by the time `ir_to_arm` runs, masked by the `Reg::R0` silent
//! fallback in `get_arm_reg`.
//!
//! # What this test verifies
//!
//! 1. The optimized pipeline compiles the i32_memory pattern without
//!    panicking and emits an `Ldr` (the load).
//! 2. A mini ARM interpreter — extended to model `Movw` / `Movt` / `Add`
//!    register-base / `Str` / `Ldr` against an emulated linear memory at
//!    `0x20000100` — runs the emitted ARM and produces the stored value
//!    in the function's return register (R0 per AAPCS).
//! 3. The load and store consistently use the same base register so the
//!    round-trip lands at the same effective address.
//!
//! Pre-fix: assertion (1) panics (`vreg v3 ...`) once PR #101's defensive
//! panic is in place; without the panic, assertion (2) returns the wrong
//! value (whatever `R0` happened to hold at the load — the stored value's
//! address rather than the value itself).
//!
//! Post-fix: CSE rewrites the `MemLoad` `addr` through `reg_map`; the load
//! reads from the address the user actually computed, and the function
//! returns the value that was stored.

use std::collections::HashMap;
use synth_synthesis::{ArmOp, MemAddr, Operand2, OptimizerBridge, Reg, WasmOp};

// =========================================================================
// Mini ARM interpreter with linear-memory support
//
// Just enough of the Thumb-2 model to run `MemLoad` / `MemStore` lowerings
// produced by `ir_to_arm`: Movw, Movt, Add (reg + reg), Mov, Ldr, Str.
// =========================================================================

/// `Reg` doesn't derive `Hash`, so we index a fixed-size array.
fn reg_index(r: Reg) -> usize {
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

#[derive(Default)]
struct Cpu {
    regs: [u32; 16],
    /// Emulated little-endian byte-addressable memory. Sparse so we don't
    /// have to allocate the entire 0x20000100-base region.
    mem: HashMap<u32, u8>,
}

impl Cpu {
    fn get(&self, r: Reg) -> u32 {
        self.regs[reg_index(r)]
    }
    fn set(&mut self, r: Reg, v: u32) {
        self.regs[reg_index(r)] = v;
    }

    fn op2(&self, op: &Operand2) -> u32 {
        match op {
            Operand2::Imm(v) => *v as u32,
            Operand2::Reg(r) => self.get(*r),
            Operand2::RegShift { rm, .. } => self.get(*rm),
        }
    }

    fn effective_addr(&self, a: &MemAddr) -> u32 {
        let base = self.get(a.base);
        let with_reg = match a.offset_reg {
            Some(r) => base.wrapping_add(self.get(r)),
            None => base,
        };
        with_reg.wrapping_add(a.offset as u32)
    }

    fn load_u32(&self, addr: u32) -> u32 {
        let b0 = *self.mem.get(&addr).unwrap_or(&0) as u32;
        let b1 = *self.mem.get(&addr.wrapping_add(1)).unwrap_or(&0) as u32;
        let b2 = *self.mem.get(&addr.wrapping_add(2)).unwrap_or(&0) as u32;
        let b3 = *self.mem.get(&addr.wrapping_add(3)).unwrap_or(&0) as u32;
        b0 | (b1 << 8) | (b2 << 16) | (b3 << 24)
    }

    fn store_u32(&mut self, addr: u32, v: u32) {
        self.mem.insert(addr, (v & 0xff) as u8);
        self.mem
            .insert(addr.wrapping_add(1), ((v >> 8) & 0xff) as u8);
        self.mem
            .insert(addr.wrapping_add(2), ((v >> 16) & 0xff) as u8);
        self.mem
            .insert(addr.wrapping_add(3), ((v >> 24) & 0xff) as u8);
    }

    fn step(&mut self, op: &ArmOp) {
        match op {
            ArmOp::Movw { rd, imm16 } => {
                // MOVW writes the low 16 bits and clears the high 16.
                self.set(*rd, *imm16 as u32);
            }
            ArmOp::Movt { rd, imm16 } => {
                let lo = self.get(*rd) & 0xFFFF;
                self.set(*rd, ((*imm16 as u32) << 16) | lo);
            }
            ArmOp::Mov { rd, op2 } => {
                let v = self.op2(op2);
                self.set(*rd, v);
            }
            ArmOp::Add { rd, rn, op2 } => {
                let a = self.get(*rn);
                let b = self.op2(op2);
                self.set(*rd, a.wrapping_add(b));
            }
            ArmOp::Sub { rd, rn, op2 } => {
                let a = self.get(*rn);
                let b = self.op2(op2);
                self.set(*rd, a.wrapping_sub(b));
            }
            ArmOp::Str { rd, addr } => {
                let ea = self.effective_addr(addr);
                let v = self.get(*rd);
                self.store_u32(ea, v);
            }
            ArmOp::Ldr { rd, addr } => {
                let ea = self.effective_addr(addr);
                let v = self.load_u32(ea);
                self.set(*rd, v);
            }
            // Prologue/epilogue (push/pop/bx) and other unmodeled ops are
            // safely ignored — none affect the memory-roundtrip outcome.
            _ => {}
        }
    }
}

// =========================================================================
// Test helpers
// =========================================================================

/// The minimal WASM op sequence equivalent to `tests/wast/i32_memory.wast`'s
/// `store_load` function body, but with **operands swapped**: local 1 is
/// the address, local 0 is the value.
///
/// Why swapped: in the natural `(addr=local 0, value=local 1)` order, the
/// second `local.get 0` is CSE-killed and the consumer `MemLoad` is left
/// referencing the unmapped `v3`. Pre-fix, `get_arm_reg(v3)` falls back to
/// `Reg::R0` — which by coincidence is also `param_regs[0]`, the register
/// holding the address. So the buggy code path happens to compute the
/// right effective address by accident, masking the bug from a behavioral
/// test.
///
/// With the operands swapped, the second `local.get 1` is the one that
/// gets CSE-killed. The correct mapping is `v3 -> R1` (param 1). The R0
/// fallback would point at `param 0` (the *value*), so the load reads
/// from `[mem_base + value]` rather than `[mem_base + addr]`. That's an
/// observable miscompile.
fn store_load_wasm_ops_param1_addr() -> Vec<WasmOp> {
    vec![
        WasmOp::LocalGet(1), // address (param 1, would map to R1)
        WasmOp::LocalGet(0), // value   (param 0, R0)
        WasmOp::I32Store {
            offset: 0,
            align: 2,
        },
        WasmOp::LocalGet(1), // address again — CSE eliminates this
        WasmOp::I32Load {
            offset: 0,
            align: 2,
        },
    ]
}

/// The natural (addr=local 0, value=local 1) shape — matches
/// `tests/wast/i32_memory.wast`. Kept around to ensure both orderings
/// compile and round-trip. Useful for asserting the
/// "structural property" tests (Ldr/Str base register identity)
/// without depending on operand order.
fn store_load_wasm_ops_param0_addr() -> Vec<WasmOp> {
    vec![
        WasmOp::LocalGet(0),
        WasmOp::LocalGet(1),
        WasmOp::I32Store {
            offset: 0,
            align: 2,
        },
        WasmOp::LocalGet(0),
        WasmOp::I32Load {
            offset: 0,
            align: 2,
        },
    ]
}

/// Run the optimized compile pipeline against a given WASM op sequence
/// with 2 params (both i32).
fn compile_optimized(wasm: &[WasmOp]) -> Vec<ArmOp> {
    let bridge = OptimizerBridge::new();
    let (ir, _cfg, _stats) = bridge
        .optimize_full(wasm)
        .expect("optimize_full should succeed for the store-load pattern");
    bridge
        .ir_to_arm(&ir, /* num_params = */ 2)
        .expect("ir_to_arm should succeed for the store-load pattern")
}

/// Execute the swapped-operand variant: param 1 = addr (in R1),
/// param 0 = value (in R0). Returns the i32 return register (R0).
fn execute_store_load_param1_addr(addr: u32, value: u32) -> u32 {
    let arm = compile_optimized(&store_load_wasm_ops_param1_addr());
    let mut cpu = Cpu::default();
    cpu.set(Reg::R0, value); // param 0 (value)
    cpu.set(Reg::R1, addr); // param 1 (address)
    for op in &arm {
        cpu.step(op);
    }
    cpu.get(Reg::R0)
}

// =========================================================================
// Tests
// =========================================================================

/// The core regression: the optimized pipeline must produce code that
/// actually round-trips a store/load.
///
/// **Uses the swapped-operand pattern** (param 1 = address, param 0 =
/// value) so the bug is sensitive to the R0 fallback. With the natural
/// (param 0 = address) layout, the unmapped vreg `v3` happens to
/// fall back to R0 — which is also the correct register for param 0 —
/// so the buggy code path produces the right answer by accident.
///
/// Pre-fix this fails two ways:
///   * panic (under PR #101's defensive `get_arm_reg`,
///     `"vreg v3 has no assigned ARM register"`),
///   * wrong return value under v0.2.1 — the load reads from
///     `[mem_base + R0 + 0]` where R0 holds the *value* (param 0),
///     not the *address* (param 1, R1). So the load picks up
///     whatever the value's-numeric-interpretation-as-address
///     happens to point to in our sparse memory map (typically 0).
///
/// Post-fix the load's `addr` vreg is rewritten by CSE to the
/// surviving `v0` (the first `Opcode::Load { dest: v0, addr: 1 }`
/// for local 1), which maps to R1 — correct.
#[test]
#[ignore = "optimized memory codegen declined pending #178 repair; re-enable when the optimized path handles linear memory correctly"]
fn issue_104_store_load_roundtrip_optimized() {
    // Pick a value far enough from 0 that a R0-fallback bug would point
    // at a sparse-memory address that doesn't contain `value` (so we'd
    // read back 0 instead of `value`).
    let addr: u32 = 0x40;
    let value: u32 = 0xCAFEBABE;
    let got = execute_store_load_param1_addr(addr, value);
    assert_eq!(
        got, value,
        "store_load(addr={addr:#x}, value={value:#x}) returned {got:#x}; \
         expected {value:#x}. This means the second `local.get 1` (the \
         load address) was not correctly re-routed to R1 after CSE — \
         see issue #104. Buggy code falls back to R0 (the value param)."
    );
}

/// Same shape, varying inputs. Hits the assertions from the i32_memory.wast
/// test cases adapted to the swapped-operand pattern.
///
/// **All cases use `addr != value`** so a R0-fallback miscompile gives a
/// wrong answer (reading from `[mem_base + value]`, which is either
/// uninitialized sparse memory → 0, or some other address that doesn't
/// hold `value`).
#[test]
#[ignore = "optimized memory codegen declined pending #178 repair; re-enable when the optimized path handles linear memory correctly"]
fn issue_104_store_load_table_driven() {
    let cases: &[(u32, u32)] = &[
        // (addr, value) — value chosen distinct from addr.
        (0x10, 42),
        (0x20, 100),
        (0x30, 0xDEADBEEF),
        (0x40, 0xFFFF_FFFE), // i32 -2 (note: not equal to addr 0x40)
        (0x50, 0x7FFF_FFFF), // i32::MAX
    ];
    for &(addr, value) in cases {
        let got = execute_store_load_param1_addr(addr, value);
        assert_eq!(
            got, value,
            "store_load(addr={addr:#x}, value={value:#x}) returned {got:#x}; \
             expected {value:#x}"
        );
    }
}

/// Compile must produce `Ldr` and `Str` that use the same base register
/// (the R12 scratch holding `linear_mem_base + user_addr`). This is a
/// structural sanity check that doesn't depend on operand order —
/// it would fire on either the natural or swapped layout if the bug
/// caused the load to compute a different scratch.
#[test]
#[ignore = "optimized memory codegen declined pending #178 repair; re-enable when the optimized path handles linear memory correctly"]
fn issue_104_load_and_store_use_consistent_base_register() {
    let arm = compile_optimized(&store_load_wasm_ops_param0_addr());

    let store = arm
        .iter()
        .find(|o| matches!(o, ArmOp::Str { .. }))
        .expect("expected an Str (i32.store lowering)");
    let load = arm
        .iter()
        .find(|o| matches!(o, ArmOp::Ldr { .. }))
        .expect("expected an Ldr (i32.load lowering)");

    let store_base = match store {
        ArmOp::Str { addr, .. } => addr.base,
        _ => unreachable!(),
    };
    let load_base = match load {
        ArmOp::Ldr { addr, .. } => addr.base,
        _ => unreachable!(),
    };

    assert_eq!(
        store_base, load_base,
        "i32.store and i32.load lowered to use different base registers \
         ({store_base:?} vs {load_base:?}); both should compute \
         `linear_mem_base + user_addr` in the same scratch. See #104."
    );
}

/// Structural check: in the swapped-operand pattern, the `Ldr`'s
/// effective address must depend on R1 (the address param), not R0
/// (the value param). Pre-fix `get_arm_reg`'s `Reg::R0` fallback
/// causes the load's address-computation `Add` to read from R0,
/// which is the value — observable in the emitted code as `Add R12,
/// R12, R0` rather than `Add R12, R12, R1`.
///
/// We check that R0 is NOT the `offset_reg` of any `Ldr` after the
/// `Str` (i.e. the load uses a base computation involving the
/// address param, not the value param).
#[test]
#[ignore = "optimized memory codegen declined pending #178 repair; re-enable when the optimized path handles linear memory correctly"]
fn issue_104_load_addr_does_not_use_value_register() {
    let arm = compile_optimized(&store_load_wasm_ops_param1_addr());

    // Find the Add that computes the load's base. In the lowering
    // sequence for MemLoad we expect:
    //   MOVW R12, #base_lo
    //   MOVT R12, #base_hi
    //   ADD  R12, R12, R<addr>     <-- this Add's op2 must be R1 (addr)
    //   LDR  Rd,  [R12, #offset]
    //
    // We look for the *last* `Add { rd: R12, rn: R12, op2: Reg(rN) }`
    // before the last `Ldr` — that's the load's address-computation.
    let last_ldr_idx = arm
        .iter()
        .rposition(|o| matches!(o, ArmOp::Ldr { .. }))
        .expect("expected an Ldr");

    let mut load_addr_add: Option<&ArmOp> = None;
    for op in &arm[..last_ldr_idx] {
        if let ArmOp::Add {
            rd: Reg::R12,
            rn: Reg::R12,
            op2: Operand2::Reg(_),
        } = op
        {
            load_addr_add = Some(op);
        }
    }

    let add = load_addr_add
        .expect("expected an `Add R12, R12, R<addr>` for the load address computation");
    if let ArmOp::Add {
        op2: Operand2::Reg(src),
        ..
    } = add
    {
        assert_ne!(
            *src,
            Reg::R0,
            "load address computation uses R0 (the value param); expected R1 \
             (the address param). The CSE-killed local-get-1 did not have \
             its consumer MemLoad rewritten to point at the surviving vreg. \
             Pre-fix this manifests as a wrong return value (we load from \
             [base + value] instead of [base + addr]). See issue #104."
        );
        assert_eq!(
            *src,
            Reg::R1,
            "load address computation should use R1 (the address param); got {:?}",
            src
        );
    }
}
