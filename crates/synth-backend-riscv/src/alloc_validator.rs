//! VCR-RA-003 for RISC-V (#815, epic #242) — the RV32 analogue of the ARM-only
//! `synth_synthesis::liveness::validate_final_allocation` register-allocation
//! validator.
//!
//! # Why a parallel re-implementation, not "also run the ARM one"
//!
//! The ARM validator is deeply ARM-coupled: its signature is
//! `&[ArmInstruction]`, its callee-saved set is `[R4..R8]`, its prologue is an
//! LR-containing `push {…}` reg-list, and its def/use classifier `reg_effect`
//! speaks `ArmOp`. RV32 needs a different instruction enum
//! ([`RiscVOp`]), a different callee-saved set (the RV psABI `s`-registers), a
//! different prologue/epilogue shape (`addi sp,sp,-N` + `sw s_k, off(sp)`), and
//! its own def/use classifier ([`op_dest`], already in `selector.rs`, mirroring
//! `reg_effect`'s "bail on unmodeled" contract). So we
//! port the *invariants*, not the code (#815).
//!
//! # Scope — the two STRAIGHT-LINE invariants (ARM phase 1)
//!
//! This validator checks exactly the two invariants the ARM phase-1 validator
//! checks, the two named in #815:
//!
//! 1. **Callee-saved preservation.** A callee-saved register the function body
//!    *writes* must be saved by the prologue `sw s_k, off(sp)` and restored by
//!    every return epilogue `lw s_k, off(sp)`. Reverting `preserve_callee_saved`
//!    (dropping the prologue spill of a written `s`-register) leaves a body def
//!    of an `s`-register with no matching save ⇒
//!    [`RaFinalViolation::CalleeSavedNotSaved`]. Whole-function structural check,
//!    safe across branches/calls (it is not dataflow).
//!
//! 2. **Spill-slot non-aliasing.** Within one straight-line segment, a frame
//!    slot `off(sp)` overwritten by a second `sw` while the first stored value is
//!    still reloaded downstream corrupts the reload ⇒
//!    [`RaFinalViolation::SpillSlotAliased`]. Same holder-model the ARM validator
//!    and `forward_stack_reloads` use.
//!
//! Everything past straight-line — value flow across a `Call`, availability
//! across a control-flow join — is the ARM *phase-2* frontier, which rests on
//! `cfg_liveness`/`check_join_availability` machinery that does not exist for
//! RV. Rather than half-implement a second-backend soundness checker, those
//! shapes are LOUD-declined: a function containing a `Call` yields
//! [`RaFinalVerdict::NotAttempted`] for the join reasoning (the two straight-line
//! invariants still ran and held). Decline > guess — the checker never claims a
//! coherence it cannot prove.
//!
//! # Callee-saved set — mirror the PASS, not the psABI
//!
//! The set is exactly the registers `preserve_callee_saved` saves: the ones
//! `is_callee_saved_temp` covers — `s1` (x9) and `s2..s10` (x18..x26). This is
//! the ARM validator's core discipline (it uses `[R4..R8]` = the set
//! `body_uses_callee_saved` covers): every function the pass left prologue-less
//! also passes the validator, so there is NO false-positive on real codegen. The
//! runtime-reserved `s0` (x8, frame pointer) and `s11` (x27,
//! `__linear_memory_base`) are DELIBERATELY excluded — the selector never emits a
//! body write to them, and the pass never saves them, so including them could
//! only manufacture a false-positive (a body `s11` read/def with no save the pass
//! was never going to add). Unlike the ARM validator, there is NO "unmodeled op →
//! force prologue" fail-safe: on RV every `op_dest == None` op is control-flow /
//! system / label / call (none write an `s`-register), so the fail-safe is
//! unnecessary AND would disagree with the pass (which has none) → false-positive.

use crate::register::Reg;
use crate::riscv_op::RiscVOp;
use crate::selector::op_dest;
use std::collections::{BTreeMap, BTreeSet};

/// A concrete register-allocation invariant violation on the final RV32 stream.
/// Each variant names a miscompile class the per-compilation checker catches.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RaFinalViolation {
    /// The body writes callee-saved register `reg` (`s1`/`s2..s10`) but no
    /// prologue `sw reg, off(sp)` that saves it precedes the write — a caller's
    /// register is silently clobbered (RV psABI violation). Reverting
    /// `preserve_callee_saved`'s save of a written `s`-register makes this fire.
    CalleeSavedNotSaved { reg: Reg },
    /// Epilogue half: the prologue saved `reg` (there is a `sw reg, off(sp)`) but
    /// a return epilogue does not restore it with a matching `lw reg, off(sp)`
    /// before the `ret` — the value the callee promised to preserve is not put
    /// back.
    CalleeSavedNotRestored { reg: Reg },
    /// Within one straight-line segment, spill slot `off(sp)` is overwritten by a
    /// second `sw` (`overwriting_store`) while the value from the first `sw`
    /// (`first_store`) is still needed by a later `lw` (`stale_reload`) — the
    /// reload reads the wrong value. Indices are into the instruction stream.
    SpillSlotAliased {
        slot: i32,
        first_store: usize,
        overwriting_store: usize,
        stale_reload: usize,
    },
}

/// Three-valued verdict of the RV32 register-allocation validator, mirroring the
/// ARM validator's Consistent / Violation / NotAttempted. A checker that cannot
/// model a construct says so LOUDLY (`NotAttempted`) rather than return a false
/// `Consistent` (decline > guess — the v0.49 L4 vacuity lesson).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RaFinalVerdict {
    /// Every checked invariant holds on this function's emitted stream.
    Consistent,
    /// A checked invariant is violated — the compile must hard-error.
    Violation(RaFinalViolation),
    /// A construct the whole-function reasoning does not model is present (a
    /// `Call` — the ARM phase-2 across-call/across-join frontier, which has no RV
    /// CFG machinery yet). The two STRAIGHT-LINE invariants (callee-saved +
    /// spill-slot) STILL RAN and held (else this would be a `Violation`); only
    /// the past-straight-line reasoning is skipped. NON-FATAL at the call site.
    /// `reason` is a static machine-readable tag.
    NotAttempted { reason: &'static str },
}

/// True for the callee-saved registers `preserve_callee_saved` actually saves:
/// `s1` (x9) and `s2..s10` (x18..x26). MUST mirror `is_callee_saved_temp` in
/// `selector.rs` exactly — see the module doc on why `s0`/`s11` are excluded.
fn is_saved_by_pass(r: Reg) -> bool {
    let n = r as u8;
    n == 9 || (18..=26).contains(&n)
}

/// A `sw`/`lw` whose base is `sp` addresses a frame slot at offset `imm`.
/// Returns the slot offset, or `None` if the memory op is not sp-relative (a
/// linear-memory access through the base register, a param home through another
/// pointer, etc. — not a spill slot).
fn sp_slot_store(op: &RiscVOp) -> Option<(i32, Reg)> {
    match op {
        RiscVOp::Sw { rs1, rs2, imm } if *rs1 == Reg::SP => Some((*imm, *rs2)),
        _ => None,
    }
}
fn sp_slot_load(op: &RiscVOp) -> Option<(i32, Reg)> {
    match op {
        RiscVOp::Lw { rd, rs1, imm } if *rs1 == Reg::SP => Some((*imm, *rd)),
        _ => None,
    }
}

/// The `ret` terminator: `jalr x0, 0(ra)`.
fn is_ret(op: &RiscVOp) -> bool {
    matches!(
        op,
        RiscVOp::Jalr {
            rd: Reg::ZERO,
            rs1: Reg::RA,
            imm: 0
        }
    )
}

/// True for ops that do NOT break a straight-line segment: everything with a
/// modeled register effect ([`op_dest`]/[`op_reads`] are `Some`) plus the
/// `sw`/`lw` memory ops. A `Label`, `Jal`, `Branch`, `Call`, `Jalr` return, or
/// any system op breaks the segment (the spill map resets at a join/barrier).
fn is_straight_line(op: &RiscVOp) -> bool {
    use RiscVOp::*;
    match op {
        // Control flow / labels / calls / system — segment barriers.
        Label { .. }
        | Jal { .. }
        | Jalr { .. }
        | Branch { .. }
        | Call { .. }
        | Ecall
        | Ebreak
        | Mret
        | Wfi
        | Fence => false,
        // Everything else is a data op (arith, load, store, csr) — straight-line.
        _ => true,
    }
}

/// VCR-RA-003 (RV32) UNCONDITIONAL single-stream register-allocation validator
/// (#815, epic #242). Runs on every RV32 function compile in the default
/// `--features riscv` build (NOT behind `--features verify` — a verify-gated
/// check would be dormant in the shipping build, the #757 / VCR-VER-003 lesson)
/// and hard-errors the compile on a [`RaFinalViolation`]. Emits nothing, so the
/// RV32 `.text` is byte-identical (the frozen RV32 oracle is unchanged).
///
/// See the module doc for the invariants, the callee-saved-set discipline, and
/// the phase-2 decline boundary.
pub fn validate_final_allocation_rv32(instrs: &[RiscVOp]) -> RaFinalVerdict {
    // ---- Invariant 1: callee-saved preservation, whole-function ----------
    //
    // Collect the prologue save-set: every `sw s_k, off(sp)` BEFORE the first
    // body op that is not part of the prologue. The pass emits the prologue as a
    // leading `addi sp,sp,-frame` followed by the `sw s_k` saves, so the save-set
    // is exactly the sp-relative stores of callee-saved regs that appear before
    // the first `ret`. We scan the whole stream: any `sw s_k, off(sp)` is a save
    // of `s_k` (the pass only stores an s-register to the frame to preserve it).
    let mut saved: BTreeSet<Reg> = BTreeSet::new();
    for ins in instrs {
        if let Some((_, rs2)) = sp_slot_store(ins)
            && is_saved_by_pass(rs2)
        {
            saved.insert(rs2);
        }
    }
    // Which callee-saved registers does the body WRITE (op_dest)? A written
    // s-register with no matching save is the #490-class clobber.
    let mut defined_cs: BTreeSet<Reg> = BTreeSet::new();
    for ins in instrs {
        if let Some(rd) = op_dest(ins)
            && is_saved_by_pass(rd)
        {
            defined_cs.insert(rd);
        }
    }
    for r in &defined_cs {
        if !saved.contains(r) {
            return RaFinalVerdict::Violation(RaFinalViolation::CalleeSavedNotSaved { reg: *r });
        }
    }
    // Epilogue half: every saved s-register must be restored by a `lw s_k,
    // off(sp)` before each `ret`. We check that between the LAST `lw`/restore
    // region and each `ret`, every saved register was reloaded. Simplest sound
    // form: for each `ret`, scan backward to the previous segment barrier and
    // collect the sp-relative loads of s-registers; every `saved` reg must be
    // among them.
    if !saved.is_empty() {
        for (i, ins) in instrs.iter().enumerate() {
            if !is_ret(ins) {
                continue;
            }
            // Collect s-register reloads in the epilogue preceding this ret:
            // walk backward until a non-epilogue op (anything that is neither a
            // sp-relative `lw` of an s-register nor the `addi sp,sp,frame` frame
            // teardown).
            let mut restored: BTreeSet<Reg> = BTreeSet::new();
            let mut j = i;
            while j > 0 {
                j -= 1;
                match &instrs[j] {
                    RiscVOp::Lw {
                        rd, rs1: Reg::SP, ..
                    } if is_saved_by_pass(*rd) => {
                        restored.insert(*rd);
                    }
                    // Frame teardown `addi sp,sp,N` is part of the epilogue.
                    RiscVOp::Addi {
                        rd: Reg::SP,
                        rs1: Reg::SP,
                        ..
                    } => {}
                    // Anything else ends the epilogue window.
                    _ => break,
                }
            }
            for r in &saved {
                if !restored.contains(r) {
                    return RaFinalVerdict::Violation(RaFinalViolation::CalleeSavedNotRestored {
                        reg: *r,
                    });
                }
            }
        }
    }

    // ---- Invariant 2: spill-slot non-aliasing, per straight-line segment --
    //
    // Same holder model as the ARM validator: per slot, remember the owning
    // store and whether the owner was reloaded (consumed). A second store to a
    // slot whose owner has NOT been reloaded shadows a still-live value; a later
    // reload of that slot proves the shadow was needed ⇒ aliasing bug. The `addi
    // sp,sp,imm` frame adjust rebases every slot offset — it resets the map (the
    // RV analogue of the ARM `ldr sp,[sp,#N]` clear).
    #[derive(Clone)]
    struct SlotState {
        owner_store: usize,
        owner_reloaded: bool,
        shadowed: Option<(usize, usize)>,
    }
    let mut i = 0usize;
    while i < instrs.len() {
        if !is_straight_line(&instrs[i]) {
            i += 1;
            continue;
        }
        let mut slots: BTreeMap<i32, SlotState> = BTreeMap::new();
        while i < instrs.len() && is_straight_line(&instrs[i]) {
            // A frame-pointer / sp adjust invalidates every slot name.
            if let RiscVOp::Addi { rd: Reg::SP, .. } = &instrs[i] {
                slots.clear();
                i += 1;
                continue;
            }
            if let Some((slot, _)) = sp_slot_store(&instrs[i]) {
                let shadowed = match slots.get(&slot) {
                    Some(prev) if !prev.owner_reloaded => Some((prev.owner_store, i)),
                    Some(prev) => prev.shadowed,
                    None => None,
                };
                slots.insert(
                    slot,
                    SlotState {
                        owner_store: i,
                        owner_reloaded: false,
                        shadowed,
                    },
                );
            } else if let Some((slot, rd)) = sp_slot_load(&instrs[i]) {
                if rd == Reg::SP {
                    slots.clear();
                } else if let Some(st) = slots.get_mut(&slot) {
                    if let Some((first_store, overwriting_store)) = st.shadowed {
                        return RaFinalVerdict::Violation(RaFinalViolation::SpillSlotAliased {
                            slot,
                            first_store,
                            overwriting_store,
                            stale_reload: i,
                        });
                    }
                    st.owner_reloaded = true;
                }
            }
            i += 1;
        }
    }

    // ---- Phase-2 boundary: value flow across a Call (loud decline) --------
    //
    // A `Call` is the ARM phase-2 across-call / across-join frontier. RV has no
    // `cfg_liveness`/join-availability machinery, so rather than a false pass we
    // LOUD-decline the past-straight-line reasoning. The two straight-line
    // invariants already ran and held. Decline > guess.
    if instrs.iter().any(|op| matches!(op, RiscVOp::Call { .. })) {
        return RaFinalVerdict::NotAttempted {
            reason: "rv32-call-boundary",
        };
    }

    RaFinalVerdict::Consistent
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::register::Reg;
    use crate::riscv_op::RiscVOp::*;

    // A minimal correct leaf body that saves+restores s2, uses it, and returns.
    fn balanced_callee_saved_body() -> Vec<RiscVOp> {
        vec![
            Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: -16,
            }, // prologue frame
            Sw {
                rs1: Reg::SP,
                rs2: Reg::S2,
                imm: 0,
            }, // save s2
            Addi {
                rd: Reg::S2,
                rs1: Reg::ZERO,
                imm: 7,
            }, // body writes s2
            Add {
                rd: Reg::A0,
                rs1: Reg::S2,
                rs2: Reg::ZERO,
            },
            Lw {
                rd: Reg::S2,
                rs1: Reg::SP,
                imm: 0,
            }, // restore s2
            Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: 16,
            }, // teardown
            Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            }, // ret
        ]
    }

    // ── RED-FIRST: clobber a used s-register with no prologue save ──────────
    #[test]
    fn ra003rv_red_missing_callee_saved_prologue_is_caught() {
        // Body writes s2 but there is NO `sw s2, off(sp)` prologue save.
        let clobbering_body = vec![
            Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: -16,
            },
            Addi {
                rd: Reg::S2,
                rs1: Reg::ZERO,
                imm: 7,
            }, // clobbers s2, unsaved
            Add {
                rd: Reg::A0,
                rs1: Reg::S2,
                rs2: Reg::ZERO,
            },
            Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: 16,
            },
            Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(
            validate_final_allocation_rv32(&clobbering_body),
            RaFinalVerdict::Violation(RaFinalViolation::CalleeSavedNotSaved { reg: Reg::S2 }),
            "a written-but-unsaved callee-saved s-register must be caught"
        );
    }

    #[test]
    fn ra003rv_green_callee_saved_prologue_present_is_consistent() {
        assert_eq!(
            validate_final_allocation_rv32(&balanced_callee_saved_body()),
            RaFinalVerdict::Consistent,
        );
    }

    // ── RED-FIRST: epilogue drops the restore of a saved register ──────────
    #[test]
    fn ra003rv_red_epilogue_drops_saved_register_is_caught() {
        // Prologue saves s2, body writes it, but the epilogue omits the `lw s2`.
        let body = vec![
            Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: -16,
            },
            Sw {
                rs1: Reg::SP,
                rs2: Reg::S2,
                imm: 0,
            },
            Addi {
                rd: Reg::S2,
                rs1: Reg::ZERO,
                imm: 7,
            },
            Add {
                rd: Reg::A0,
                rs1: Reg::S2,
                rs2: Reg::ZERO,
            },
            // <-- missing `lw s2, 0(sp)`
            Addi {
                rd: Reg::SP,
                rs1: Reg::SP,
                imm: 16,
            },
            Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(
            validate_final_allocation_rv32(&body),
            RaFinalVerdict::Violation(RaFinalViolation::CalleeSavedNotRestored { reg: Reg::S2 }),
        );
    }

    #[test]
    fn ra003rv_green_pure_scratch_leaf_needs_no_prologue() {
        // Uses only caller-saved temps (t0/a0) — no prologue required.
        let body = vec![
            Addi {
                rd: Reg::T0,
                rs1: Reg::ZERO,
                imm: 3,
            },
            Add {
                rd: Reg::A0,
                rs1: Reg::T0,
                rs2: Reg::ZERO,
            },
            Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(
            validate_final_allocation_rv32(&body),
            RaFinalVerdict::Consistent
        );
    }

    // ── RED-FIRST: alias two live values on one spill slot ─────────────────
    #[test]
    fn ra003rv_red_spill_slot_aliasing_is_caught() {
        // sw A -> slot 4; sw B -> slot 4 (A not yet reloaded); lw slot 4 -> reads
        // B though A was still needed.
        let body = vec![
            Sw {
                rs1: Reg::SP,
                rs2: Reg::T0,
                imm: 4,
            }, // first_store (A)
            Sw {
                rs1: Reg::SP,
                rs2: Reg::T1,
                imm: 4,
            }, // overwriting_store (B)
            Lw {
                rd: Reg::T2,
                rs1: Reg::SP,
                imm: 4,
            }, // stale_reload
            Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(
            validate_final_allocation_rv32(&body),
            RaFinalVerdict::Violation(RaFinalViolation::SpillSlotAliased {
                slot: 4,
                first_store: 0,
                overwriting_store: 1,
                stale_reload: 2,
            }),
        );
    }

    #[test]
    fn ra003rv_green_sequential_slot_reuse_is_consistent() {
        // sw A; lw A (consumed); sw B (legal reuse); lw B — no aliasing.
        let body = vec![
            Sw {
                rs1: Reg::SP,
                rs2: Reg::T0,
                imm: 4,
            },
            Lw {
                rd: Reg::T0,
                rs1: Reg::SP,
                imm: 4,
            }, // A consumed
            Sw {
                rs1: Reg::SP,
                rs2: Reg::T1,
                imm: 4,
            }, // reuse slot 4
            Lw {
                rd: Reg::T1,
                rs1: Reg::SP,
                imm: 4,
            },
            Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(
            validate_final_allocation_rv32(&body),
            RaFinalVerdict::Consistent
        );
    }

    // ── Phase-2 decline: a Call yields NotAttempted (never a false pass) ────
    #[test]
    fn ra003rv_call_boundary_is_not_attempted() {
        let body = vec![
            Addi {
                rd: Reg::A0,
                rs1: Reg::ZERO,
                imm: 1,
            },
            Call {
                label: "callee".to_string(),
            },
            Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(
            validate_final_allocation_rv32(&body),
            RaFinalVerdict::NotAttempted {
                reason: "rv32-call-boundary"
            },
        );
    }

    // ── A Call does NOT mask a straight-line violation before it ───────────
    #[test]
    fn ra003rv_violation_before_call_still_fires() {
        let body = vec![
            Addi {
                rd: Reg::S2,
                rs1: Reg::ZERO,
                imm: 7,
            }, // unsaved s2 clobber
            Call {
                label: "callee".to_string(),
            },
            Jalr {
                rd: Reg::ZERO,
                rs1: Reg::RA,
                imm: 0,
            },
        ];
        assert_eq!(
            validate_final_allocation_rv32(&body),
            RaFinalVerdict::Violation(RaFinalViolation::CalleeSavedNotSaved { reg: Reg::S2 }),
        );
    }
}
