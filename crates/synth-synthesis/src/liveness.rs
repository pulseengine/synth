//! Register def/use + liveness analysis — foundation for VCR-RA-001.
//!
//! This is the reusable primitive a spill-capable register allocator (and DCE,
//! and peephole-safety checks) is built on: for each ARM instruction, which
//! registers it *reads* (uses) and which it *writes* (defs). The current
//! codegen has no such analysis — `select_with_stack` tracks a virtual stack and
//! hard-fails on exhaustion (instruction_selector.rs:330/356/577/4667) rather
//! than reasoning over live ranges. Per the verified-codegen roadmap
//! (`artifacts/verified-codegen-roadmap.yaml`, VCR-RA-001) we build that
//! reasoning up incrementally; this module is step one.
//!
//! **Soundness discipline.** Instructions whose register effect is not yet
//! modeled precisely — high-level pseudo-ops (`LocalGet`, `Select`, …), the
//! 64-bit register-pair ops, the FP ops, and anything that clobbers a
//! caller-saved set (`Bl`, `Call`, …) — return `None` from [`reg_effect`]. Every
//! analysis here returns `None` for a stream it cannot *fully* model, so a
//! non-`None` result is always trustworthy. Nothing in this module is wired into
//! codegen yet: it is pure analysis, so it cannot change emitted bytes.

use crate::instruction_selector::ArmInstruction;
use crate::rules::{ArmOp, MemAddr, Operand2, Reg};

/// The register read/write effect of a single instruction.
///
/// `defs` are registers fully written (their previous value is dead after this
/// instruction); `uses` are registers read. An instruction that both reads and
/// writes a register (e.g. `Movt`, which preserves the low half) lists it in
/// both.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct RegEffect {
    pub defs: Vec<Reg>,
    pub uses: Vec<Reg>,
}

fn op2_uses(op2: &Operand2) -> Vec<Reg> {
    match op2 {
        Operand2::Reg(r) => vec![*r],
        Operand2::RegShift { rm, .. } => vec![*rm],
        Operand2::Imm(_) => vec![],
    }
}

fn addr_uses(a: &MemAddr) -> Vec<Reg> {
    let mut v = vec![a.base];
    if let Some(r) = a.offset_reg {
        v.push(r);
    }
    v
}

/// The register def/use effect of `op`, or `None` if `op` is not yet modeled
/// precisely (pseudo-ops, i64-pair ops, FP, calls, control flow). Callers that
/// need soundness must treat `None` as "unknown" and bail.
pub fn reg_effect(op: &ArmOp) -> Option<RegEffect> {
    use ArmOp::*;
    let def_use = |defs: Vec<Reg>, uses: Vec<Reg>| Some(RegEffect { defs, uses });

    match op {
        // rd = rn <op> op2
        Add { rd, rn, op2 }
        | Sub { rd, rn, op2 }
        | Adds { rd, rn, op2 }
        | Subs { rd, rn, op2 }
        | Adc { rd, rn, op2 }
        | Sbc { rd, rn, op2 }
        | And { rd, rn, op2 }
        | Orr { rd, rn, op2 }
        | Eor { rd, rn, op2 } => {
            let mut uses = vec![*rn];
            uses.extend(op2_uses(op2));
            def_use(vec![*rd], uses)
        }

        // rd = imm - rn (reverse subtract; second operand is an immediate)
        Rsb { rd, rn, .. } => def_use(vec![*rd], vec![*rn]),

        // rd = <op> op2
        Mov { rd, op2 } | Mvn { rd, op2 } => def_use(vec![*rd], op2_uses(op2)),

        // rd = imm (low half); upper half zeroed — no use
        Movw { rd, .. } | MovwSym { rd, .. } => def_use(vec![*rd], vec![]),
        // rd[31:16] = imm, rd[15:0] preserved — reads and writes rd
        Movt { rd, .. } | MovtSym { rd, .. } => def_use(vec![*rd], vec![*rd]),

        // rd = rn <op> rm
        Mul { rd, rn, rm }
        | Sdiv { rd, rn, rm }
        | Udiv { rd, rn, rm }
        | LslReg { rd, rn, rm }
        | LsrReg { rd, rn, rm }
        | AsrReg { rd, rn, rm }
        | RorReg { rd, rn, rm } => def_use(vec![*rd], vec![*rn, *rm]),

        // {rdhi:rdlo} = rn * rm
        Umull { rdlo, rdhi, rn, rm } => def_use(vec![*rdlo, *rdhi], vec![*rn, *rm]),

        // rd = rn*rm - ra
        Mls { rd, rn, rm, ra } => def_use(vec![*rd], vec![*rn, *rm, *ra]),

        // rd = rn <shift> #imm
        Lsl { rd, rn, .. } | Lsr { rd, rn, .. } | Asr { rd, rn, .. } | Ror { rd, rn, .. } => {
            def_use(vec![*rd], vec![*rn])
        }

        // rd = <unary> rm
        Clz { rd, rm }
        | Rbit { rd, rm }
        | Popcnt { rd, rm }
        | Sxtb { rd, rm }
        | Sxth { rd, rm } => def_use(vec![*rd], vec![*rm]),

        // flag-setting compares: read operands, write no GP register
        Cmp { rn, op2 } | Cmn { rn, op2 } => {
            let mut uses = vec![*rn];
            uses.extend(op2_uses(op2));
            def_use(vec![], uses)
        }

        // rd = cond (materialize a flag) — writes rd, reads flags only
        SetCond { rd, .. } => def_use(vec![*rd], vec![]),

        // loads: rd = mem[addr]
        Ldr { rd, addr }
        | Ldrb { rd, addr }
        | Ldrsb { rd, addr }
        | Ldrh { rd, addr }
        | Ldrsh { rd, addr } => def_use(vec![*rd], addr_uses(addr)),

        // stores: mem[addr] = rd — rd is a SOURCE (use), addr regs are uses
        Str { rd, addr } | Strb { rd, addr } | Strh { rd, addr } => {
            let mut uses = vec![*rd];
            uses.extend(addr_uses(addr));
            def_use(vec![], uses)
        }

        // register lists
        Pop { regs } => def_use(regs.clone(), vec![]),
        Push { regs } => def_use(vec![], regs.clone()),

        // no register effect
        Nop | Udf { .. } => def_use(vec![], vec![]),

        // Everything else is not modeled precisely here: control flow
        // (B/BOffset/BCondOffset/Bhs/Blo/Bcc/Bx), calls and clobbers
        // (Bl/Blx/Call/CallIndirect), memory builtins, the high-level pseudo-ops
        // (Local*/Global*/Select*/BrTable), and the i64-pair + FP families.
        // Returning None keeps every downstream analysis sound.
        _ => None,
    }
}

/// True if `op` is straight-line (no branch / label / call) and therefore safe
/// to include in a local, single-block analysis.
fn is_straight_line(op: &ArmOp) -> bool {
    use ArmOp::*;
    !matches!(
        op,
        Label { .. }
            | B { .. }
            | BOffset { .. }
            | BCondOffset { .. }
            | Bhs { .. }
            | Blo { .. }
            | Bcc { .. }
            | Bl { .. }
            | Bx { .. }
            | Blx { .. }
            | BrTable { .. }
            | Call { .. }
            | CallIndirect { .. }
    )
}

/// Indices of instructions in `instrs` whose destination register is a **dead
/// store**: written here and then *overwritten* later in the same straight-line
/// region before any intervening read. Such an instruction's result is provably
/// unused regardless of what is live on exit, so it is a sound dead-code
/// candidate — the generic form of the hand-rolled dead-divisor-const peephole
/// (#221, `drop_prev_const_materialization`).
///
/// Returns `None` (declines to analyze) if the region is not a single
/// straight-line block of fully-modeled instructions — never a wrong answer.
/// A single-`def`, no-`use` instruction (a pure materialization like `Movw`) is
/// required for a candidate, so we never flag a read-modify-write as dead.
pub fn local_dead_defs(instrs: &[ArmInstruction]) -> Option<Vec<usize>> {
    // Pre-compute effects; bail if anything is unmodeled or not straight-line.
    let mut effects: Vec<RegEffect> = Vec::with_capacity(instrs.len());
    for instr in instrs {
        if !is_straight_line(&instr.op) {
            return None;
        }
        effects.push(reg_effect(&instr.op)?);
    }

    let mut dead = Vec::new();
    for (i, eff) in effects.iter().enumerate() {
        // Only consider a pure single-register materialization (def, no use of
        // that same reg): a read-modify-write (e.g. Movt) is never a dead store.
        if eff.defs.len() != 1 {
            continue;
        }
        let d = eff.defs[0];
        if eff.uses.contains(&d) {
            continue;
        }
        // Scan forward: is `d` read before it is written again?
        let mut overwritten_before_use = false;
        for later in &effects[i + 1..] {
            if later.uses.contains(&d) {
                break; // used → live → not dead
            }
            if later.defs.contains(&d) {
                overwritten_before_use = true; // redefined unused → dead store
                break;
            }
        }
        if overwritten_before_use {
            dead.push(i);
        }
    }
    Some(dead)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instruction_selector::ArmInstruction;
    use crate::rules::{ArmOp, Operand2, Reg};

    fn ins(op: ArmOp) -> ArmInstruction {
        ArmInstruction {
            op,
            source_line: None,
        }
    }

    #[test]
    fn reg_effect_models_three_operand_alu() {
        let e = reg_effect(&ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R1,
            op2: Operand2::Reg(Reg::R2),
        })
        .unwrap();
        assert_eq!(e.defs, vec![Reg::R0]);
        assert_eq!(e.uses, vec![Reg::R1, Reg::R2]);
    }

    #[test]
    fn reg_effect_store_source_is_a_use_not_a_def() {
        // STR R3, [R11, R4] — R3 is read (the value stored), R11+R4 addressing.
        let e = reg_effect(&ArmOp::Str {
            rd: Reg::R3,
            addr: crate::rules::MemAddr::reg(Reg::R11, Reg::R4),
        })
        .unwrap();
        assert!(e.defs.is_empty(), "a store defines no register");
        assert_eq!(e.uses, vec![Reg::R3, Reg::R11, Reg::R4]);
    }

    #[test]
    fn reg_effect_movt_reads_and_writes_rd() {
        let e = reg_effect(&ArmOp::Movt {
            rd: Reg::R5,
            imm16: 0x1234,
        })
        .unwrap();
        assert_eq!(e.defs, vec![Reg::R5]);
        assert_eq!(e.uses, vec![Reg::R5], "Movt preserves the low half");
    }

    #[test]
    fn reg_effect_declines_pseudo_and_call_ops() {
        assert!(
            reg_effect(&ArmOp::LocalGet {
                rd: Reg::R0,
                index: 0
            })
            .is_none()
        );
        assert!(
            reg_effect(&ArmOp::Bl {
                label: String::new()
            })
            .is_none()
        );
    }

    #[test]
    fn dead_def_detects_overwrite_before_use() {
        // Movw R0,#7  ;  Movw R0,#9  ;  Add R1,R0,#0
        // The first Movw is a dead store (R0 overwritten before any read).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 9,
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
        ];
        assert_eq!(local_dead_defs(&seq), Some(vec![0]));
    }

    #[test]
    fn dead_def_respects_intervening_use() {
        // Movw R0,#7  ;  Add R1,R0,#0  ;  Movw R0,#9
        // The first Movw is NOT dead: R0 is read by the Add before being rewritten.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 9,
            }),
        ];
        assert_eq!(local_dead_defs(&seq), Some(vec![]));
    }

    #[test]
    fn dead_def_declines_on_branch_or_unmodeled() {
        // A branch in the region → cannot soundly analyze a single block.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::BOffset { offset: 4 }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 9,
            }),
        ];
        assert_eq!(local_dead_defs(&seq), None);
    }
}
