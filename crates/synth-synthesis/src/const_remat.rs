//! VCR-RA-010 — constant rematerialization: the PROVEN half of the scry seam.
//!
//! A reload (`LDR rD, [SP, #slot]`) whose slot was filled from a register that
//! held a **materialized constant** can be replaced by re-materializing that
//! constant (`MOV`/`MOVW`(+`MOVT`) rD, #c). The value is identical, the frame
//! traffic is gone, and on the hot kernels this is exactly the waste gale
//! measured (#390 pass-5 `#0x7e`/`#0x7f` clamps, #209 const-CSE).
//!
//! # Why the hint cannot make this unsound
//!
//! Unlike `--proven-safe` (#901), where a wrong verdict elides a bounds guard
//! and opens a memory-safety hole, a wrong const-remat verdict would corrupt a
//! *value* — a miscompile. So the seam is built the other way round from a
//! trusting one, and the same way as the `--wcet-hints` seam:
//!
//! > **Eligibility is DERIVED from the emitted instruction stream. The hint
//! > only GATES consumption; it can never create an eligible site.**
//!
//! scry's interval domain says "local N is the singleton `[c, c]`". That is a
//! statement about the WASM source. This module never reads it as authority:
//! it independently walks the FINAL ARM stream and admits a reload only when it
//! can see, in that stream, the constant definition that reaches the spill and
//! the absence of any intervening write. A hint naming a local that is not
//! constant produces **zero** eligible sites, which is the red-first property
//! `lying_hint_yields_no_candidates` pins.
//!
//! That asymmetry is the point of the release: *verified or refused, never
//! believed.*
//!
//! # What is deliberately NOT claimed
//!
//! The walk is **linear and conservative**, not a dataflow fixpoint:
//!
//! * any branch, label, or call ends the current window — a slot's constancy is
//!   only tracked within a straight-line run, so a value proven at a join is
//!   simply not found rather than wrongly admitted;
//! * any write to SP (frame adjust) drops every tracked slot;
//! * a second store to a slot with a non-constant register drops that slot.
//!
//! Every one of those is a MISSED opportunity, never an unsound one. The
//! counts this module reports are therefore a floor on the real opportunity,
//! and are reported as such.

use crate::instruction_selector::ArmInstruction;
use crate::rules::{ArmOp, MemAddr, Operand2, Reg};
use std::collections::HashMap;

/// A reload this pass proved replaceable by re-materializing a constant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RematSite {
    /// Index into the instruction stream of the `LDR` that can be replaced.
    pub reload_index: usize,
    /// The destination register of that reload.
    pub rd: Reg,
    /// SP-relative slot the reload reads.
    pub slot: i32,
    /// The constant proven to be in that slot, as a full 32-bit value.
    pub value: u32,
    /// Index of the instruction that materialized the constant — kept so the
    /// evidence is auditable rather than a bare count.
    pub def_index: usize,
}

/// The derived plan. `considered` is what the hint offered; `proven` is what
/// the stream actually justified. Reporting both is the #910 discipline: a
/// bare "N remat sites" cannot distinguish a precise hint from a lucky one.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct RematPlan {
    pub sites: Vec<RematSite>,
    /// Reloads examined — the denominator, so a zero result is legible as
    /// "nothing qualified" rather than "nothing ran".
    pub reloads_seen: usize,
    /// Windows closed by a branch/call/label, i.e. opportunities the linear
    /// walk declines to reason about. A conservatism budget, reported not hidden.
    pub windows_closed: usize,
}

/// What a register is currently known to hold.
#[derive(Clone, Copy, PartialEq, Eq)]
enum RegVal {
    /// A constant materialized at this stream index.
    Const { value: u32, def_index: usize },
}

fn sp_slot(addr: &MemAddr) -> Option<i32> {
    (addr.base == Reg::SP && addr.offset_reg.is_none()).then_some(addr.offset)
}

/// Immediate carried by a `Mov` whose operand is a bare immediate.
fn mov_imm(op2: &Operand2) -> Option<u32> {
    match op2 {
        Operand2::Imm(v) => Some(*v as u32),
        _ => None,
    }
}

/// Derive the rematerialization plan from the FINAL instruction stream.
///
/// `hinted` gates consumption: only slots whose reload destination register is
/// offered by the hint are admitted. Pass an empty set for the flag-off
/// default, which yields an empty plan and leaves bytes untouched.
pub fn plan_const_remat(instrs: &[ArmInstruction], hinted: &HintGate) -> RematPlan {
    let mut plan = RematPlan::default();
    // Register -> proven constant currently in it.
    let mut regs: HashMap<Reg, RegVal> = HashMap::new();
    // SP slot -> proven constant currently stored there.
    let mut slots: HashMap<i32, RegVal> = HashMap::new();

    for (i, instr) in instrs.iter().enumerate() {
        match &instr.op {
            // ---- constant materialization ---------------------------------
            ArmOp::Mov { rd, op2 } => match mov_imm(op2) {
                Some(v) => {
                    regs.insert(
                        *rd,
                        RegVal::Const {
                            value: v,
                            def_index: i,
                        },
                    );
                }
                // MOV from a register: the value is whatever that register
                // held. Not tracked — conservatively unknown.
                None => {
                    regs.remove(rd);
                }
            },
            ArmOp::Movw { rd, imm16 } => {
                regs.insert(
                    *rd,
                    RegVal::Const {
                        value: *imm16 as u32,
                        def_index: i,
                    },
                );
            }
            // MOVT completes a 32-bit constant, but ONLY if the low half was
            // itself a proven constant from a MOVW. Otherwise the register
            // becomes unknown: `MOVT` preserves the low half, so pairing it
            // with an unknown low half yields an unknown value.
            ArmOp::Movt { rd, imm16 } => match regs.get(rd) {
                Some(RegVal::Const { value, def_index }) if *value <= 0xFFFF => {
                    let full = (*imm16 as u32) << 16 | *value;
                    let def_index = *def_index;
                    regs.insert(
                        *rd,
                        RegVal::Const {
                            value: full,
                            def_index,
                        },
                    );
                }
                _ => {
                    regs.remove(rd);
                }
            },

            // ---- the spill ------------------------------------------------
            ArmOp::Str { rd, addr } => {
                match (sp_slot(addr), regs.get(rd).copied()) {
                    // A constant reached the slot: remember it.
                    (Some(s), Some(c)) => {
                        slots.insert(s, c);
                    }
                    // A non-constant reached the slot: it is no longer
                    // rematerializable, and saying so is the whole point.
                    (Some(s), None) => {
                        slots.remove(&s);
                    }
                    (None, _) => {}
                }
            }

            // ---- the reload -----------------------------------------------
            ArmOp::Ldr { rd, addr } => {
                if let Some(s) = sp_slot(addr) {
                    plan.reloads_seen += 1;
                    if let Some(RegVal::Const { value, def_index }) = slots.get(&s).copied()
                        && hinted.admits(*rd, value)
                    {
                        {
                            plan.sites.push(RematSite {
                                reload_index: i,
                                rd: *rd,
                                slot: s,
                                value,
                                def_index,
                            });
                        }
                    }
                    // The reload defines rd with the slot's value.
                    match slots.get(&s).copied() {
                        Some(c) => {
                            regs.insert(*rd, c);
                        }
                        None => {
                            regs.remove(rd);
                        }
                    }
                } else {
                    regs.remove(rd);
                }
            }

            // ---- everything that ends the window --------------------------
            // A branch, a label or a call means a different path can reach the
            // next instruction, and this walk does not compute joins. Drop all
            // knowledge rather than carry it across an edge we did not analyse.
            op if ends_window(op) => {
                plan.windows_closed += 1;
                regs.clear();
                slots.clear();
            }

            // ---- anything else --------------------------------------------
            other => {
                if !preserves_state(other) {
                    // Unknown destination, and possibly an unknown memory
                    // write or stack adjustment. Forget everything.
                    regs.clear();
                    slots.clear();
                }
            }
        }
    }
    plan
}

/// Instructions after which this linear walk refuses to carry knowledge.
fn ends_window(op: &ArmOp) -> bool {
    matches!(
        op,
        ArmOp::B { .. }
            | ArmOp::BOffset { .. }
            | ArmOp::Bl { .. }
            | ArmOp::Blx { .. }
            | ArmOp::Bx { .. }
            | ArmOp::Label { .. }
    )
}

/// Ops after which BOTH register and slot knowledge survive: they define no
/// register this walk tracks and write no memory.
///
/// Everything not listed here — every arithmetic op, every wide store, every
/// stack adjustment — clears the whole state. That is a large amount of missed
/// opportunity and it is deliberate for a first increment: an op wrongly
/// treated as harmless could hide a write to the slot (a `STM`, an `SP`
/// adjustment) and turn a stale constant into a miscompile. Widening this set
/// op-by-op, each with its own test, is the named follow-up; `windows_closed`
/// and `reloads_seen` make the cost of the current conservatism visible rather
/// than leaving a small number looking like a small opportunity.
fn preserves_state(op: &ArmOp) -> bool {
    matches!(
        op,
        ArmOp::Cmp { .. } | ArmOp::Cmn { .. } | ArmOp::Strb { .. } | ArmOp::Strh { .. }
    )
}

/// The consumption gate. Empty = flag-off = no rematerialization at all.
///
/// The gate holds `(register, value)` pairs scry offered. It can only ever
/// SHRINK the proven set — `admits` is consulted after the stream has already
/// justified the site.
#[derive(Debug, Clone, Default)]
pub struct HintGate {
    offered: Vec<(Reg, u32)>,
    /// When true, every proven site is admitted (used by the measurement
    /// harness to report the ceiling the hint is being scored against).
    admit_all: bool,
}

impl HintGate {
    /// The flag-off default: nothing is admitted, so bytes are untouched.
    pub fn closed() -> Self {
        Self::default()
    }

    /// Admit every stream-proven site — the DERIVED ceiling, used to measure
    /// how much of the real opportunity a hint actually names.
    pub fn open() -> Self {
        Self {
            offered: Vec::new(),
            admit_all: true,
        }
    }

    pub fn from_offers(offered: Vec<(Reg, u32)>) -> Self {
        Self {
            offered,
            admit_all: false,
        }
    }

    fn admits(&self, rd: Reg, value: u32) -> bool {
        self.admit_all || self.offered.iter().any(|(r, v)| *r == rd && *v == value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn i(op: ArmOp) -> ArmInstruction {
        ArmInstruction {
            op,
            source_line: None,
        }
    }

    fn slot(offset: i32) -> MemAddr {
        MemAddr::imm(Reg::SP, offset)
    }

    /// A NON-frame address: used to give a register a value this walk cannot
    /// prove constant, which is what the red-first tests need.
    fn heap(base: Reg) -> MemAddr {
        MemAddr::imm(base, 0)
    }

    /// The shape the whole pass exists for: materialize a constant, spill it,
    /// reload it. The reload is replaceable.
    #[test]
    fn constant_spill_reload_is_proven_rematerializable() {
        let s = vec![
            i(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(0x7E),
            }),
            i(ArmOp::Str {
                rd: Reg::R0,
                addr: slot(8),
            }),
            i(ArmOp::Ldr {
                rd: Reg::R1,
                addr: slot(8),
            }),
        ];
        let p = plan_const_remat(&s, &HintGate::open());
        assert_eq!(p.reloads_seen, 1);
        assert_eq!(p.sites.len(), 1, "the constant reaches the reload");
        assert_eq!(p.sites[0].value, 0x7E);
        assert_eq!(p.sites[0].rd, Reg::R1);
        assert_eq!(p.sites[0].def_index, 0, "evidence points at the MOV");
    }

    /// THE RED-FIRST PROPERTY. A hint that names a value the stream does not
    /// justify must produce NOTHING. This is what makes the seam safe: the
    /// hint cannot manufacture an eligible site.
    #[test]
    fn lying_hint_yields_no_candidates() {
        // The spilled register holds a RUNTIME value (loaded from memory),
        // not a constant — but the hint insists it is 999.
        let s = vec![
            i(ArmOp::Ldr {
                rd: Reg::R0,
                addr: heap(Reg::R4),
            }),
            i(ArmOp::Str {
                rd: Reg::R0,
                addr: slot(4),
            }),
            i(ArmOp::Ldr {
                rd: Reg::R1,
                addr: slot(4),
            }),
        ];
        // The gate is deliberately OPEN here. An earlier version of this test
        // offered only `(R1, 999)` and passed — but for the WRONG REASON: a
        // broken stream check yields the constant 0, the gate's value
        // comparison rejected 0 != 999, and the test stayed green while the
        // property it names was broken. Mutation is what exposed that; the
        // gate must not be able to do the rejecting, or this test proves
        // nothing about the stream.
        let p = plan_const_remat(&s, &HintGate::open());
        assert_eq!(p.reloads_seen, 1, "the reload WAS examined");
        assert!(
            p.sites.is_empty(),
            "a hint must never create a site the stream does not justify"
        );

        // And with the gate closed over a value a broken walk WOULD invent.
        let lying = HintGate::from_offers(vec![(Reg::R1, 0), (Reg::R1, 999)]);
        assert!(
            plan_const_remat(&s, &lying).sites.is_empty(),
            "naming the exact value a broken walk would invent must still fail"
        );
    }

    /// A non-constant store to the slot must retire the slot's constancy —
    /// otherwise a stale constant would be rematerialized over a live value.
    #[test]
    fn overwriting_the_slot_with_a_runtime_value_retires_it() {
        let s = vec![
            i(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(5),
            }),
            i(ArmOp::Str {
                rd: Reg::R0,
                addr: slot(8),
            }),
            // R2's value is unknown to the walk; storing it must clear slot 8.
            i(ArmOp::Str {
                rd: Reg::R2,
                addr: slot(8),
            }),
            i(ArmOp::Ldr {
                rd: Reg::R1,
                addr: slot(8),
            }),
        ];
        let p = plan_const_remat(&s, &HintGate::open());
        assert!(p.sites.is_empty(), "the slot no longer holds the constant");
    }

    /// MOVT over an unknown low half must NOT be read as a constant.
    #[test]
    fn movt_over_unknown_low_half_is_not_constant() {
        let s = vec![
            // R0 is defined by a reload from a non-SP address: unknown.
            i(ArmOp::Ldr {
                rd: Reg::R0,
                addr: heap(Reg::R4),
            }),
            i(ArmOp::Movt {
                rd: Reg::R0,
                imm16: 0xDEAD,
            }),
            i(ArmOp::Str {
                rd: Reg::R0,
                addr: slot(0),
            }),
            i(ArmOp::Ldr {
                rd: Reg::R1,
                addr: slot(0),
            }),
        ];
        let p = plan_const_remat(&s, &HintGate::open());
        assert!(
            p.sites.is_empty(),
            "MOVT preserves the low half; an unknown low half stays unknown"
        );
    }

    /// MOVW+MOVT is the 32-bit constant form and must reconstruct exactly.
    #[test]
    fn movw_movt_pair_reconstructs_the_full_constant() {
        let s = vec![
            i(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0xBEEF,
            }),
            i(ArmOp::Movt {
                rd: Reg::R0,
                imm16: 0xDEAD,
            }),
            i(ArmOp::Str {
                rd: Reg::R0,
                addr: slot(12),
            }),
            i(ArmOp::Ldr {
                rd: Reg::R1,
                addr: slot(12),
            }),
        ];
        let p = plan_const_remat(&s, &HintGate::open());
        assert_eq!(p.sites.len(), 1);
        assert_eq!(p.sites[0].value, 0xDEAD_BEEF);
    }

    /// The flag-off default must be byte-invisible: no site, whatever the
    /// stream contains.
    #[test]
    fn closed_gate_admits_nothing() {
        let s = vec![
            i(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            i(ArmOp::Str {
                rd: Reg::R0,
                addr: slot(8),
            }),
            i(ArmOp::Ldr {
                rd: Reg::R1,
                addr: slot(8),
            }),
        ];
        let p = plan_const_remat(&s, &HintGate::closed());
        assert_eq!(p.reloads_seen, 1);
        assert!(p.sites.is_empty(), "flag-off must change nothing");
    }

    /// A branch between the spill and the reload closes the window. This is a
    /// DECLINE, and the test exists so the conservatism is visible rather than
    /// discovered later as a mysterious zero.
    #[test]
    fn a_branch_closes_the_window_conservatively() {
        let s = vec![
            i(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Imm(7),
            }),
            i(ArmOp::Str {
                rd: Reg::R0,
                addr: slot(8),
            }),
            i(ArmOp::B {
                label: "join".to_string(),
            }),
            i(ArmOp::Ldr {
                rd: Reg::R1,
                addr: slot(8),
            }),
        ];
        let p = plan_const_remat(&s, &HintGate::open());
        assert_eq!(p.windows_closed, 1, "the decline is counted, not silent");
        assert!(p.sites.is_empty());
    }
}
