//! RQ-91-M0I32 (#1301): the ARMv6-M lowering of i32 arithmetic, constants,
//! compares, select and structured control flow.
//!
//! WHERE IT RUNS. On the final allocated `ArmOp` stream of an ARMv6-M
//! (cortex-m0 / cortex-m0plus) function — after `finish_allocated_stream`,
//! before label resolution — and nowhere else. Every other target never
//! reaches this module, so their bytes cannot move.
//!
//! WHAT IT DOES. [`lower`] is a rule table keyed on the op: each op the
//! direct selector emits for the scope above is rewritten into ops whose
//! Thumb encodings are 16-bit ARMv6-M forms (the explicit flag-setting
//! variants `Movs`/`Mvns`/`Ands`/`Orrs`/`Eors`/`Lsls`/`Lsrs`/`Asrs`/`Muls`
//! where the v6-M form sets flags, plain `Mov`/`Add`/`Sub`/`Cmp`/branches
//! otherwise), and EVERY op outside the table is refused, naming it. So a
//! v6-M function is either fully lowered by a listed rule or declines loudly;
//! there is no silent pass-through.
//!
//! - Constants (`Mov #imm`, `Movw`, `Movw`+`Movt`): a MOVS / LSLS
//!   / ADDS #imm8 / MVNS sequence (at most 7 instructions; no literal pool —
//!   the 16-bit pool load is refused by `armv6m::check_bytes` until a reach
//!   check exists for it).
//! - `SetCond` (an IT block on v7-M): a branch diamond,
//!   `b<c> L1; movs rd,#0; b L2; L1: movs rd,#1; L2:`. The cold review's M2
//!   shape: both straight-line rewrites of `ite c; mov rd,#1; mov rd,#0` are
//!   wrong, because the first MOVS destroys the compare's flags.
//! - `SelectMove` (`it c; mov rd, rm`): `b<!c> L; mov rd, rm; L:`.
//! - Direct calls (RQ-92-WDGTHIN, #1741): `bl <symbol>` is ARMv6-M as it is
//!   (the one 32-bit instruction this pass emits), to a function of the
//!   module or to a function import. At most four argument words: a call
//!   with an outgoing stack argument is refused before selection
//!   ([`refuse_stack_argument_call`]). Indirect calls stay refused.
//! - Two-operand forms: v6-M data processing is `rdn = rdn op rm`, so a
//!   three-register op becomes `mov rd, rn; <op>s rd, rm` unless `rd` already
//!   is a source.
//!
//! REGISTERS (the ARMv6-M contract, gale notice 20261118T091556-9870f8).
//! Allocation uses R0-R6 only ([`ALLOC_POOL`]; the selector and the range
//! re-allocator are both handed that pool). R7 is this pass's scratch
//! ([`SCRATCH`]); the selector's own scratch, R12, is renamed to R7 here, so
//! synth writes no R12 and allocates no R8 on this profile. R9-R11 are never
//! touched (memory and globals stay declined). A function whose stream
//! names R7 or R8 before the rename, or any of R9-R11, is refused. When R7 is
//! used, it is added to the prologue's PUSH and to every epilogue POP.
//!
//! FLAGS. Every 16-bit v6-M data-processing form sets flags. The NZCV
//! verifier (`crate::nzcv`, always on for ARMv6-M) checks every flag the
//! emitted BYTES write against the op's contract: the explicit flag-setting
//! variants declare nothing (`Writes(0)`), so each flag they write must be
//! dead; `Add`/`Sub`/`Mov` keep `Preserves` and are held to the same rule
//! (R1). This pass emits no op whose flags are consumed except `Cmp`/`Cmn`,
//! which declare all four. A lowering mistake therefore yields a refusal,
//! never a stream that reads a clobbered flag.
//!
//! WHAT THIS PASS DOES NOT COVER: the stream the selector hands it. Selection
//! under register pressure is the selector's, and its exhaustion-recovery
//! rungs (spill, pool-grow) miscompiled under the R0-R6 pool (cold review 15
//! F1: 100 of 39,627 accepted fuzz functions). `compile_wasm_to_arm` therefore
//! declines, on ARMv6-M, every function the `base` rung cannot select.
//!
//! FAIL-CLOSED BEHIND IT. `armv6m::check_bytes` still checks every encoded
//! instruction (and refuses any write to R8-R12), so a rule that produced a
//! non-v6-M encoding refuses the function rather than emit it.

use synth_synthesis::ArmInstruction;
use synth_synthesis::rules::{ArmOp, Condition, MemAddr, Operand2, Reg};

/// The allocatable pool on ARMv6-M: R0-R6.
pub const ALLOC_POOL: [Reg; 7] = [
    Reg::R0,
    Reg::R1,
    Reg::R2,
    Reg::R3,
    Reg::R4,
    Reg::R5,
    Reg::R6,
];

/// Registers the selector must never allocate on ARMv6-M.
pub const EXCLUDED_ALLOC: &[Reg] = &[Reg::R7, Reg::R8];

/// The lowering's scratch register (callee-saved: pushed when used).
pub const SCRATCH: Reg = Reg::R7;

/// The class prefix of every refusal from this pass.
const WHY: &str = "ARMv6-M lowering, RQ-91-M0I32 (#1301)";

fn refuse<T>(what: String) -> Result<T, String> {
    Err(format!(
        "{WHY}: {what}. The function is refused rather than emitted."
    ))
}

/// The registers an op defines and uses: the liveness model's
/// `reg_effect`, completed for the ops this pass reads or emits that it does
/// not model (`Mvn`, the flag-setting variants, control flow). `None` for an
/// op outside both; every such op is refused by the rule table.
fn effect(op: &ArmOp) -> Option<(Vec<Reg>, Vec<Reg>)> {
    use ArmOp::*;
    let o2 = |o: &Operand2| match o {
        Operand2::Reg(r) | Operand2::RegShift { rm: r, .. } => vec![*r],
        Operand2::Imm(_) => vec![],
    };
    Some(match op {
        Mvn { rd, op2 } | Movs { rd, op2 } | Mvns { rd, op2 } => (vec![*rd], o2(op2)),
        Ands { rd, rn, op2 } | Orrs { rd, rn, op2 } | Eors { rd, rn, op2 } => {
            let mut u = vec![*rn];
            u.extend(o2(op2));
            (vec![*rd], u)
        }
        Lsls { rd, rn, .. } | Lsrs { rd, rn, .. } | Asrs { rd, rn, .. } => (vec![*rd], vec![*rn]),
        Muls { rd, rn, rm } => (vec![*rd], vec![*rn, *rm]),
        Label { .. }
        | B { .. }
        | Bcc { .. }
        | Bhs { .. }
        | Blo { .. }
        | BOffset { .. }
        | BCondOffset { .. } => (vec![], vec![]),
        Bx { rm } => (vec![], vec![*rm]),
        // A direct call, as the AAPCS callee sees the registers this pass
        // works in: it reads the argument registers and may clobber R0-R3 and
        // LR. R12 is renamed to R7 before any rule runs, and a callee
        // preserves R7, so the call neither reads nor writes the scratch;
        // `scratch_never_crosses_control` separately refuses a stream that
        // read the selector's R12 after a call.
        Bl { .. } => (
            vec![Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::LR],
            vec![Reg::R0, Reg::R1, Reg::R2, Reg::R3],
        ),
        op => {
            let e = synth_synthesis::liveness::reg_effect(op)?;
            (e.defs, e.uses)
        }
    })
}

/// Every register an op names (defined or used).
fn regs_of(op: &ArmOp) -> Option<Vec<Reg>> {
    let (mut d, u) = effect(op)?;
    d.extend(u);
    Some(d)
}

fn reads(op: &ArmOp, r: Reg) -> bool {
    effect(op).is_none_or(|(_, u)| u.contains(&r))
}

fn writes(op: &ArmOp, r: Reg) -> bool {
    effect(op).is_some_and(|(d, _)| d.contains(&r))
}

fn is_control(op: &ArmOp) -> bool {
    matches!(
        op,
        ArmOp::Label { .. }
            | ArmOp::B { .. }
            | ArmOp::Bcc { .. }
            | ArmOp::Bhs { .. }
            | ArmOp::Blo { .. }
            | ArmOp::BOffset { .. }
            | ArmOp::BCondOffset { .. }
            | ArmOp::Bx { .. }
            | ArmOp::Pop { .. }
            | ArmOp::Udf { .. }
    )
}

/// Whether the scratch R7 is dead immediately BEFORE `ops[i]` executes,
/// conservatively: no op after `i` reads R7, or the first access at or after
/// `i` in straight-line order is a pure write. Reaching control flow first
/// counts as live.
///
/// SOUND ONLY UNDER [`scratch_never_crosses_control`], which [`lower`]
/// checks before any rule runs: R7 (the selector's renamed R12) is never live
/// across a label or branch. A loop back edge therefore cannot carry an R7
/// value to an earlier read, which the forward scan here does not see.
/// The invariant [`scratch_dead_at`] rests on (cold review 15 F7): every
/// read of R7 is preceded by a write to R7 since the last control-flow op or
/// label, in stream order. `Err` names the first read that is not.
fn scratch_never_crosses_control(ops: &[ArmOp]) -> Result<(), String> {
    let mut written = false;
    for op in ops {
        if matches!(op, ArmOp::Push { .. } | ArmOp::Pop { .. }) {
            // Save lists, rebuilt by `fix_prologue`; not a use of the value.
            written = false;
            continue;
        }
        // A call clobbers the selector's R12 (AAPCS IP): what R7 holds after
        // the rename is not a value the stream may read back.
        if is_control(op) || matches!(op, ArmOp::Bl { .. }) {
            written = false;
        }
        if reads(op, SCRATCH) && effect(op).is_some() && !written {
            return refuse(format!(
                "`{op:?}` reads the scratch R7 (the selector's R12) without a write \
                 since the last label or branch: R12 would be live across control \
                 flow, which the scratch liveness check does not model"
            ));
        }
        if writes(op, SCRATCH) {
            written = true;
        }
    }
    Ok(())
}

fn scratch_dead_at(ops: &[ArmOp], i: usize) -> bool {
    if !ops[i..].iter().any(|op| reads(op, SCRATCH)) {
        return true;
    }
    for op in &ops[i..] {
        if reads(op, SCRATCH) {
            return false;
        }
        if writes(op, SCRATCH) {
            return true;
        }
        if is_control(op) {
            return false;
        }
    }
    true
}

/// Rename `from` to `to` in the ops the rule table lowers. An op outside the
/// table is returned unchanged and refused by the table afterwards.
fn rename_op(op: &ArmOp, from: Reg, to: Reg) -> ArmOp {
    use ArmOp::*;
    let r = |x: Reg| if x == from { to } else { x };
    let rename_op2 = |o: &Operand2| match o {
        Operand2::Reg(x) => Operand2::Reg(r(*x)),
        other => other.clone(),
    };
    match op {
        Add { rd, rn, op2 } => Add {
            rd: r(*rd),
            rn: r(*rn),
            op2: rename_op2(op2),
        },
        Sub { rd, rn, op2 } => Sub {
            rd: r(*rd),
            rn: r(*rn),
            op2: rename_op2(op2),
        },
        And { rd, rn, op2 } => And {
            rd: r(*rd),
            rn: r(*rn),
            op2: rename_op2(op2),
        },
        Orr { rd, rn, op2 } => Orr {
            rd: r(*rd),
            rn: r(*rn),
            op2: rename_op2(op2),
        },
        Eor { rd, rn, op2 } => Eor {
            rd: r(*rd),
            rn: r(*rn),
            op2: rename_op2(op2),
        },
        Mov { rd, op2 } => Mov {
            rd: r(*rd),
            op2: rename_op2(op2),
        },
        Mvn { rd, op2 } => Mvn {
            rd: r(*rd),
            op2: rename_op2(op2),
        },
        Mul { rd, rn, rm } => Mul {
            rd: r(*rd),
            rn: r(*rn),
            rm: r(*rm),
        },
        Lsl { rd, rn, shift } => Lsl {
            rd: r(*rd),
            rn: r(*rn),
            shift: *shift,
        },
        Lsr { rd, rn, shift } => Lsr {
            rd: r(*rd),
            rn: r(*rn),
            shift: *shift,
        },
        Asr { rd, rn, shift } => Asr {
            rd: r(*rd),
            rn: r(*rn),
            shift: *shift,
        },
        Ror { rd, rn, shift } => Ror {
            rd: r(*rd),
            rn: r(*rn),
            shift: *shift,
        },
        LslReg { rd, rn, rm } => LslReg {
            rd: r(*rd),
            rn: r(*rn),
            rm: r(*rm),
        },
        LsrReg { rd, rn, rm } => LsrReg {
            rd: r(*rd),
            rn: r(*rn),
            rm: r(*rm),
        },
        AsrReg { rd, rn, rm } => AsrReg {
            rd: r(*rd),
            rn: r(*rn),
            rm: r(*rm),
        },
        RorReg { rd, rn, rm } => RorReg {
            rd: r(*rd),
            rn: r(*rn),
            rm: r(*rm),
        },
        Rsb { rd, rn, imm } => Rsb {
            rd: r(*rd),
            rn: r(*rn),
            imm: *imm,
        },
        Movw { rd, imm16 } => Movw {
            rd: r(*rd),
            imm16: *imm16,
        },
        Movt { rd, imm16 } => Movt {
            rd: r(*rd),
            imm16: *imm16,
        },
        Cmp { rn, op2 } => Cmp {
            rn: r(*rn),
            op2: rename_op2(op2),
        },
        Cmn { rn, op2 } => Cmn {
            rn: r(*rn),
            op2: rename_op2(op2),
        },
        Sxtb { rd, rm } => Sxtb {
            rd: r(*rd),
            rm: r(*rm),
        },
        Sxth { rd, rm } => Sxth {
            rd: r(*rd),
            rm: r(*rm),
        },
        Uxtb { rd, rm } => Uxtb {
            rd: r(*rd),
            rm: r(*rm),
        },
        Uxth { rd, rm } => Uxth {
            rd: r(*rd),
            rm: r(*rm),
        },
        SetCond { rd, cond } => SetCond {
            rd: r(*rd),
            cond: *cond,
        },
        SelectMove { rd, rm, cond } => SelectMove {
            rd: r(*rd),
            rm: r(*rm),
            cond: *cond,
        },
        Ldr { rd, addr } => Ldr {
            rd: r(*rd),
            addr: addr.clone(),
        },
        Str { rd, addr } => Str {
            rd: r(*rd),
            addr: addr.clone(),
        },
        other => other.clone(),
    }
}

/// The ops that materialize the 32-bit constant `v` into the low register
/// `rd`, shortest of the candidate shapes. Every op is a 16-bit v6-M
/// encoding: `MOVS rd,#imm8`, `LSLS rd,rd,#imm5`, `ADDS rd,#imm8` (an `Add`
/// with `rd == rn`, which the v6-M encoder emits as T2) and `MVNS rd,rd`.
pub fn materialize(rd: Reg, v: u32) -> Vec<ArmOp> {
    let movs = |k: u32| ArmOp::Movs {
        rd,
        op2: Operand2::Imm(k as i32),
    };
    let lsls = |s: u32| ArmOp::Lsls {
        rd,
        rn: rd,
        shift: s,
    };
    let mvns = ArmOp::Mvns {
        rd,
        op2: Operand2::Reg(rd),
    };
    // A non-negative value built from its top byte down: `movs` of the
    // leading 8 bits, then for each further non-zero byte a merged `lsls`
    // and an `adds #imm8`, then a final `lsls` for trailing zero bits.
    let build = |v: u32| -> Vec<ArmOp> {
        if v <= 0xFF {
            return vec![movs(v)];
        }
        // k << s with k <= 255.
        let tz = v.trailing_zeros();
        if (v >> tz) <= 0xFF {
            return vec![movs(v >> tz), lsls(tz)];
        }
        // Leading 8-bit window, then 8-bit chunks.
        let top = 31 - v.leading_zeros(); // index of the highest set bit
        let mut pos = top.saturating_sub(7); // low bit of the leading window
        let mut out = vec![movs(v >> pos)];
        let mut pending_shift = 0u32;
        while pos > 0 {
            let step = pos.min(8);
            pos -= step;
            pending_shift += step;
            let chunk = (v >> pos) & ((1u32 << step) - 1);
            if chunk != 0 {
                out.push(lsls(pending_shift));
                pending_shift = 0;
                out.push(ArmOp::Add {
                    rd,
                    rn: rd,
                    op2: Operand2::Imm(chunk as i32),
                });
            }
        }
        if pending_shift > 0 {
            out.push(lsls(pending_shift));
        }
        out
    };
    let direct = build(v);
    let mut inverted = build(!v);
    inverted.push(mvns);
    if inverted.len() < direct.len() {
        inverted
    } else {
        direct
    }
}

/// One rewritten op with a fresh-label source.
struct Ctx {
    out: Vec<ArmInstruction>,
    labels: usize,
    func_tag: usize,
}

impl Ctx {
    fn push(&mut self, op: ArmOp, line: Option<usize>) {
        self.out.push(ArmInstruction {
            op,
            source_line: line,
        });
    }
    fn label(&mut self) -> String {
        self.labels += 1;
        format!(".Lv6m_{}_{}", self.func_tag, self.labels)
    }
}

fn low(r: Reg) -> bool {
    ALLOC_POOL.contains(&r) || r == SCRATCH
}

/// `rd = rn <op> rm` for a commutative v6-M two-operand op `mk(rdn, rm)`.
fn commutative(
    cx: &mut Ctx,
    mk: &dyn Fn(Reg, Reg) -> ArmOp,
    rd: Reg,
    rn: Reg,
    rm: Reg,
    line: Option<usize>,
) {
    if rd == rn {
        cx.push(mk(rd, rm), line);
    } else if rd == rm {
        cx.push(mk(rd, rn), line);
    } else {
        cx.push(
            ArmOp::Mov {
                rd,
                op2: Operand2::Reg(rn),
            },
            line,
        );
        cx.push(mk(rd, rm), line);
    }
}

/// Lower one ARMv6-M function. `func_tag` makes the diamond labels unique
/// within the object (they are local to the function either way).
pub fn lower(instrs: Vec<ArmInstruction>, func_tag: usize) -> Result<Vec<ArmInstruction>, String> {
    // 1. Register contract, on the stream as selected. R9-R11 refuse.
    for ins in &instrs {
        if matches!(ins.op, ArmOp::Push { .. } | ArmOp::Pop { .. }) {
            continue; // save lists are rebuilt by `fix_prologue`
        }
        if let Some(r) = regs_of(&ins.op)
            .unwrap_or_default()
            .into_iter()
            .find(|r| matches!(r, Reg::R9 | Reg::R10 | Reg::R11))
        {
            return refuse(format!(
                "`{:?}` names {r:?} (globals / linear memory), which has no \
                 ARMv6-M lowering yet",
                ins.op
            ));
        }
    }
    let mut ops: Vec<ArmOp> = instrs.iter().map(|i| i.op.clone()).collect();
    let lines: Vec<Option<usize>> = instrs.iter().map(|i| i.source_line).collect();
    // The selector and the range re-allocator never pick R7/R8 here, but
    // later passes (spill re-homing, const-CSE) choose from the v7-M pool. A
    // value they put in R7 or R8 is moved, by a whole-function rename, to a
    // register the function never names — semantics-preserving because
    // nothing else reads or writes the target. Only possible when every op's
    // registers are modeled; otherwise refused.
    for hi in [Reg::R7, Reg::R8] {
        fn body(ops: &[ArmOp]) -> impl Iterator<Item = &ArmOp> {
            ops.iter()
                .filter(|o| !matches!(o, ArmOp::Push { .. } | ArmOp::Pop { .. }))
        }
        if !body(&ops).any(|o| regs_of(o).unwrap_or_default().contains(&hi)) {
            continue;
        }
        let mut named = std::collections::BTreeSet::new();
        for o in body(&ops) {
            match regs_of(o) {
                Some(rs) => named.extend(rs),
                None => {
                    return refuse(format!(
                        "{hi:?} holds a value (not allocatable on ARMv6-M) and `{o:?}` \
                         has no register model, so it cannot be renamed"
                    ));
                }
            }
        }
        let Some(&to) = [Reg::R3, Reg::R2, Reg::R4, Reg::R5, Reg::R6]
            .iter()
            .find(|r| !named.contains(r))
        else {
            return refuse(format!(
                "{hi:?} holds a value and every low register is in use \
                 (R7 is the lowering scratch; R8 has no 16-bit load, store or push)"
            ));
        };
        ops = ops.iter().map(|o| rename_op(o, hi, to)).collect();
        if body(&ops).any(|o| regs_of(o).unwrap_or_default().contains(&hi)) {
            return refuse(format!("{hi:?} is named by an op this pass cannot rename"));
        }
    }
    // The frame the prologue allocates (`push; sub sp, #frame`): an SP-relative
    // access at or above it reads an incoming STACK argument. Those are not
    // lowered in this lane: no execution oracle sets up stack arguments yet.
    let frame_bytes = match ops.get(1) {
        Some(ArmOp::Sub {
            rd: Reg::SP,
            rn: Reg::SP,
            op2: Operand2::Imm(k),
        }) if matches!(ops.first(), Some(ArmOp::Push { .. })) => *k,
        _ => 0,
    };
    // 2. The selector's scratch R12 becomes R7.
    let ops: Vec<ArmOp> = ops
        .iter()
        .map(|o| rename_op(o, Reg::R12, SCRATCH))
        .collect();
    scratch_never_crosses_control(&ops)?;

    let mut cx = Ctx {
        out: Vec::with_capacity(ops.len() * 2),
        labels: 0,
        func_tag,
    };
    let need_scratch = |i: usize, what: &ArmOp| -> Result<(), String> {
        if reads(what, SCRATCH) || !scratch_dead_at(&ops, i) {
            refuse(format!(
                "`{what:?}` needs the scratch R7 for a constant, but R7 is live there"
            ))
        } else {
            Ok(())
        }
    };

    let mut i = 0;
    while i < ops.len() {
        let op = &ops[i];
        let line = lines[i];
        use ArmOp::*;
        match op {
            // Control flow and traps: 16-bit as they are. Long label branches
            // are widened by the v6-M encoder or refused by the byte check.
            Label { .. } | B { .. } | Bcc { .. } | Bhs { .. } | Blo { .. } | Udf { .. } | Nop => {
                cx.push(op.clone(), line);
            }
            Bx { rm: Reg::LR } => cx.push(op.clone(), line),
            // A pre-resolved numeric branch counts halfwords over ops whose
            // sizes this pass may change. Only the size-invariant guard shape
            // `b<c> +0; udf` (skip exactly one UDF) is kept.
            BCondOffset { offset: 0, .. } if matches!(ops.get(i + 1), Some(Udf { .. })) => {
                cx.push(op.clone(), line);
            }
            Push { .. } | Pop { .. } => cx.push(op.clone(), line),
            // RQ-92-WDGTHIN (#1741): a direct call, `bl <symbol>` — the one
            // 32-bit instruction of ARMv6-M this pass emits. To a function of
            // the module or to a function import (an undefined symbol the
            // embedder's linker binds); the encoding and the relocation are
            // the v7-M ones. Arguments arrive in R0-R3 from the selector's
            // marshalling moves, which the `Mov` rules lower; a call with an
            // outgoing STACK argument is refused in `compile_wasm_to_arm`
            // before selection. LR must already be saved: `fix_prologue`
            // refuses a call in a function with no `push {.., lr}`.
            Bl { .. } => cx.push(op.clone(), line),

            Mov {
                rd,
                op2: Operand2::Reg(rm),
            } if low(*rd) && low(*rm) => cx.push(op.clone(), line),
            Mov {
                rd,
                op2: Operand2::Imm(v),
            } if low(*rd) => {
                for o in materialize(*rd, *v as u32) {
                    cx.push(o, line);
                }
            }
            Movw { rd, imm16 } if low(*rd) => {
                let mut v = u32::from(*imm16);
                if let Some(Movt { rd: rt, imm16: hi }) = ops.get(i + 1)
                    && rt == rd
                {
                    v |= u32::from(*hi) << 16;
                    i += 1;
                }
                for o in materialize(*rd, v) {
                    cx.push(o, line);
                }
            }
            Mvn {
                rd,
                op2: Operand2::Reg(rm),
            } if low(*rd) && low(*rm) => cx.push(
                Mvns {
                    rd: *rd,
                    op2: Operand2::Reg(*rm),
                },
                line,
            ),

            // Frame: `sub sp,#k` / `add sp,#k` (16-bit up to 508).
            Add {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(k),
            }
            | Sub {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(k),
            } if (0..=508).contains(k) && k % 4 == 0 => cx.push(op.clone(), line),

            Add {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            }
            | Sub {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            } if low(*rd) && low(*rn) && low(*rm) => cx.push(op.clone(), line),
            Add {
                rd,
                rn,
                op2: Operand2::Imm(k),
            }
            | Sub {
                rd,
                rn,
                op2: Operand2::Imm(k),
            } if low(*rd) && low(*rn) => {
                let is_add = matches!(op, Add { .. });
                // Normalize to rd = rn + a or rd = rn - a with a >= 0.
                let (add, a) = match (is_add, *k >= 0) {
                    (true, true) => (true, *k as u32),
                    (true, false) => (false, k.unsigned_abs()),
                    (false, true) => (false, *k as u32),
                    (false, false) => (true, k.unsigned_abs()),
                };
                let mk = |rd: Reg, rn: Reg, o: Operand2| {
                    if add {
                        Add { rd, rn, op2: o }
                    } else {
                        Sub { rd, rn, op2: o }
                    }
                };
                if a == 0 {
                    if rd != rn {
                        cx.push(
                            Mov {
                                rd: *rd,
                                op2: Operand2::Reg(*rn),
                            },
                            line,
                        );
                    }
                } else if a <= 7 || (rd == rn && a <= 0xFF) {
                    cx.push(mk(*rd, *rn, Operand2::Imm(a as i32)), line);
                } else if rd != rn {
                    // rd = constant, then rd = rn +/- rd (operands read first).
                    for o in materialize(*rd, a) {
                        cx.push(o, line);
                    }
                    cx.push(mk(*rd, *rn, Operand2::Reg(*rd)), line);
                } else {
                    need_scratch(i, op)?;
                    for o in materialize(SCRATCH, a) {
                        cx.push(o, line);
                    }
                    cx.push(mk(*rd, *rn, Operand2::Reg(SCRATCH)), line);
                }
            }
            Rsb { rd, rn, imm } if low(*rd) && low(*rn) => {
                // rd = imm - rn.
                if rd != rn {
                    for o in materialize(*rd, *imm) {
                        cx.push(o, line);
                    }
                    cx.push(
                        Sub {
                            rd: *rd,
                            rn: *rd,
                            op2: Operand2::Reg(*rn),
                        },
                        line,
                    );
                } else {
                    need_scratch(i, op)?;
                    for o in materialize(SCRATCH, *imm) {
                        cx.push(o, line);
                    }
                    cx.push(
                        Sub {
                            rd: *rd,
                            rn: SCRATCH,
                            op2: Operand2::Reg(*rn),
                        },
                        line,
                    );
                }
            }
            Mul { rd, rn, rm } if low(*rd) && low(*rn) && low(*rm) => {
                let mk = |d: Reg, m: Reg| Muls {
                    rd: d,
                    rn: d,
                    rm: m,
                };
                commutative(&mut cx, &mk, *rd, *rn, *rm, line);
            }
            And { rd, rn, op2 } | Orr { rd, rn, op2 } | Eor { rd, rn, op2 }
                if low(*rd) && low(*rn) =>
            {
                let kind = match op {
                    And { .. } => 0,
                    Orr { .. } => 1,
                    _ => 2,
                };
                let mk = move |d: Reg, m: Reg| {
                    let o = Operand2::Reg(m);
                    match kind {
                        0 => Ands {
                            rd: d,
                            rn: d,
                            op2: o,
                        },
                        1 => Orrs {
                            rd: d,
                            rn: d,
                            op2: o,
                        },
                        _ => Eors {
                            rd: d,
                            rn: d,
                            op2: o,
                        },
                    }
                };
                match op2 {
                    Operand2::Reg(rm) if low(*rm) => {
                        commutative(&mut cx, &mk, *rd, *rn, *rm, line);
                    }
                    Operand2::Imm(0xFF) if kind == 0 => cx.push(Uxtb { rd: *rd, rm: *rn }, line),
                    Operand2::Imm(0xFFFF) if kind == 0 => cx.push(Uxth { rd: *rd, rm: *rn }, line),
                    Operand2::Imm(v) => {
                        let v = *v as u32;
                        if rd != rn {
                            for o in materialize(*rd, v) {
                                cx.push(o, line);
                            }
                            cx.push(mk(*rd, *rn), line);
                        } else {
                            need_scratch(i, op)?;
                            for o in materialize(SCRATCH, v) {
                                cx.push(o, line);
                            }
                            cx.push(mk(*rd, SCRATCH), line);
                        }
                    }
                    _ => return refuse(format!("no rule for `{op:?}`")),
                }
            }
            Lsl { rd, rn, shift } if low(*rd) && low(*rn) && *shift <= 31 => cx.push(
                Lsls {
                    rd: *rd,
                    rn: *rn,
                    shift: *shift,
                },
                line,
            ),
            Lsr { rd, rn, shift } | Asr { rd, rn, shift }
                if low(*rd) && low(*rn) && *shift <= 32 =>
            {
                if *shift == 0 {
                    if rd != rn {
                        cx.push(
                            Mov {
                                rd: *rd,
                                op2: Operand2::Reg(*rn),
                            },
                            line,
                        );
                    }
                } else if matches!(op, Lsr { .. }) {
                    cx.push(
                        Lsrs {
                            rd: *rd,
                            rn: *rn,
                            shift: *shift,
                        },
                        line,
                    );
                } else {
                    cx.push(
                        Asrs {
                            rd: *rd,
                            rn: *rn,
                            shift: *shift,
                        },
                        line,
                    );
                }
            }
            // Shift / rotate by register: v6-M has only `<op>S rdn, rm` (the
            // v6-M encoder emits it for `rd == rn`).
            LslReg { rd, rn, rm }
            | LsrReg { rd, rn, rm }
            | AsrReg { rd, rn, rm }
            | RorReg { rd, rn, rm }
                if low(*rd) && low(*rn) && low(*rm) =>
            {
                let mk = |d: Reg, m: Reg| match op {
                    LslReg { .. } => LslReg {
                        rd: d,
                        rn: d,
                        rm: m,
                    },
                    LsrReg { .. } => LsrReg {
                        rd: d,
                        rn: d,
                        rm: m,
                    },
                    AsrReg { .. } => AsrReg {
                        rd: d,
                        rn: d,
                        rm: m,
                    },
                    _ => RorReg {
                        rd: d,
                        rn: d,
                        rm: m,
                    },
                };
                if rd == rn {
                    cx.push(mk(*rd, *rm), line);
                } else if rd != rm {
                    cx.push(
                        Mov {
                            rd: *rd,
                            op2: Operand2::Reg(*rn),
                        },
                        line,
                    );
                    cx.push(mk(*rd, *rm), line);
                } else {
                    // rd == rm != rn: keep the amount in the scratch first.
                    need_scratch(i, op)?;
                    cx.push(
                        Mov {
                            rd: SCRATCH,
                            op2: Operand2::Reg(*rm),
                        },
                        line,
                    );
                    cx.push(
                        Mov {
                            rd: *rd,
                            op2: Operand2::Reg(*rn),
                        },
                        line,
                    );
                    cx.push(mk(*rd, SCRATCH), line);
                }
            }
            // No rule for `Ror #imm` or `Mvn #imm`: the direct selector, the
            // only path that reaches ARMv6-M, never emits either (constant
            // rotates arrive as `RorReg`, `~imm` as `Movw` + `Mvn reg`;
            // `fold_immediate_shifts` folds only LSL/LSR/ASR). Cold review 15
            // F3 found both rules unreached by 49,600 fuzz functions; they
            // were deleted rather than kept untested. Either op refuses.
            Sxtb { rd, rm } | Sxth { rd, rm } | Uxtb { rd, rm } | Uxth { rd, rm }
                if low(*rd) && low(*rm) =>
            {
                cx.push(op.clone(), line)
            }

            Cmp {
                rn,
                op2: Operand2::Reg(rm),
            }
            | Cmn {
                rn,
                op2: Operand2::Reg(rm),
            } if low(*rn) && low(*rm) => cx.push(op.clone(), line),
            Cmp {
                rn,
                op2: Operand2::Imm(v),
            } if low(*rn) && (0..=0xFF).contains(v) => cx.push(op.clone(), line),
            Cmp {
                rn,
                op2: Operand2::Imm(v),
            }
            | Cmn {
                rn,
                op2: Operand2::Imm(v),
            } if low(*rn) => {
                need_scratch(i, op)?;
                for o in materialize(SCRATCH, *v as u32) {
                    cx.push(o, line);
                }
                let o = Operand2::Reg(SCRATCH);
                cx.push(
                    if matches!(op, Cmp { .. }) {
                        Cmp { rn: *rn, op2: o }
                    } else {
                        Cmn { rn: *rn, op2: o }
                    },
                    line,
                );
            }

            // IT blocks become branch diamonds.
            SetCond { rd, cond } if low(*rd) => {
                let (l1, l2) = (cx.label(), cx.label());
                cx.push(
                    Bcc {
                        cond: *cond,
                        label: l1.clone(),
                    },
                    line,
                );
                cx.push(
                    Movs {
                        rd: *rd,
                        op2: Operand2::Imm(0),
                    },
                    line,
                );
                cx.push(B { label: l2.clone() }, line);
                cx.push(Label { name: l1 }, line);
                cx.push(
                    Movs {
                        rd: *rd,
                        op2: Operand2::Imm(1),
                    },
                    line,
                );
                cx.push(Label { name: l2 }, line);
            }
            SelectMove { rd, rm, cond } if low(*rd) && low(*rm) => {
                let skip = cx.label();
                cx.push(
                    Bcc {
                        cond: invert(*cond),
                        label: skip.clone(),
                    },
                    line,
                );
                cx.push(
                    Mov {
                        rd: *rd,
                        op2: Operand2::Reg(*rm),
                    },
                    line,
                );
                cx.push(Label { name: skip }, line);
            }

            Ldr {
                addr:
                    MemAddr {
                        base: Reg::SP,
                        offset,
                        ..
                    },
                ..
            }
            | Str {
                addr:
                    MemAddr {
                        base: Reg::SP,
                        offset,
                        ..
                    },
                ..
            } if *offset >= frame_bytes => {
                return refuse(format!(
                    "`{op:?}` reads an incoming stack argument (above the {frame_bytes}-byte \
                     frame); stack-passed parameters are not lowered for ARMv6-M yet"
                ));
            }
            // Frame slots: `ldr/str rt, [sp, #imm8*4]`.
            Ldr {
                rd,
                addr:
                    MemAddr {
                        base: Reg::SP,
                        offset,
                        offset_reg: None,
                    },
            }
            | Str {
                rd,
                addr:
                    MemAddr {
                        base: Reg::SP,
                        offset,
                        offset_reg: None,
                    },
            } if low(*rd) && (0..=1020).contains(offset) && offset % 4 == 0 => {
                cx.push(op.clone(), line)
            }

            other => {
                return refuse(format!(
                    "no ARMv6-M rule for `{other:?}` (i32 arithmetic, constants, \
                     compares, select, structured control flow and direct calls \
                     are lowered; memory, globals, indirect calls, i64 arithmetic, \
                     floats, division and bit counts are not yet)"
                ));
            }
        }
        i += 1;
    }

    fix_prologue(cx.out)
}

/// RQ-92-WDGTHIN (#1741): refuse a function that makes a direct call with more
/// than four argument words. The selector passes the fifth and later words in
/// the outgoing stack area, and no ARMv6-M execution oracle sets up or checks
/// stack arguments at a call boundary (the hosted harness refuses them), so
/// the shape is declined, by name, rather than emitted unexecuted. A callee
/// whose arity the compile was not given is refused for the same reason.
/// 64-bit arguments are already refused on every ARM target (#929), so an
/// argument count is a word count here.
pub fn refuse_stack_argument_call(
    wasm_ops: &[synth_core::WasmOp],
    func_arg_counts: &[u32],
) -> Result<(), String> {
    for op in wasm_ops {
        if let synth_core::WasmOp::Call(f) = op {
            match func_arg_counts.get(*f as usize) {
                Some(n) if *n <= 4 => {}
                Some(n) => {
                    return refuse(format!(
                        "the call to function {f} passes {n} arguments, so it needs an \
                         outgoing stack argument; calls with more than four argument \
                         words are not lowered for ARMv6-M yet"
                    ));
                }
                None => {
                    return refuse(format!(
                        "the call to function {f} has no known argument count, so it \
                         cannot be shown to need no outgoing stack argument"
                    ));
                }
            }
        }
    }
    Ok(())
}

fn invert(c: Condition) -> Condition {
    c.invert()
}

/// Whether any op other than PUSH/POP addresses or moves SP.
fn touches_sp(out: &[ArmInstruction]) -> bool {
    out.iter().any(|i| match &i.op {
        ArmOp::Push { .. } | ArmOp::Pop { .. } => false,
        ArmOp::Ldr { addr, .. } | ArmOp::Str { addr, .. } => addr.base == Reg::SP,
        op => regs_of(op).is_some_and(|r| r.contains(&Reg::SP)),
    })
}

/// The prologue / epilogue on ARMv6-M: `push {..., lr}` / `pop {..., pc}`
/// with low registers only, saving exactly the callee-saved registers the
/// lowered body names (R4-R6, and R7 when the scratch is used). R8 never
/// appears (it holds no value here). In a function that addresses SP the
/// list is padded back to the selector's size, so every SP-relative offset
/// and the 8-byte SP alignment are unchanged; elsewhere it is the smallest
/// even-length list. Pads come from R3, R2, then unused R4-R6: R2/R3 are
/// caller-saved and never result registers, so restoring them in the
/// epilogue is harmless.
fn fix_prologue(mut out: Vec<ArmInstruction>) -> Result<Vec<ArmInstruction>, String> {
    let uses_scratch = out.iter().any(|i| match &i.op {
        ArmOp::Push { .. } | ArmOp::Pop { .. } => false,
        op => regs_of(op).is_none_or(|r| r.contains(&SCRATCH)),
    });
    let pushes: Vec<usize> = (0..out.len())
        .filter(|&k| matches!(out[k].op, ArmOp::Push { .. }))
        .collect();
    let pops: Vec<usize> = (0..out.len())
        .filter(|&k| matches!(out[k].op, ArmOp::Pop { .. }))
        .collect();
    let Some(&first) = pushes.first() else {
        if out.iter().any(|i| matches!(i.op, ArmOp::Bl { .. })) {
            return refuse("a call in a function with no prologue: LR is not saved".into());
        }
        let callee_saved = out.iter().any(|i| {
            regs_of(&i.op)
                .is_none_or(|r| r.iter().any(|r| matches!(r, Reg::R4 | Reg::R5 | Reg::R6)))
        });
        if callee_saved {
            return refuse("a callee-saved register is used in a function with no prologue".into());
        }
        if uses_scratch {
            return refuse("the scratch R7 is used in a function with no prologue".into());
        }
        if !pops.is_empty() {
            return refuse("an epilogue POP without a prologue PUSH".into());
        }
        return Ok(out);
    };
    let ArmOp::Push { regs: orig } = out[first].op.clone() else {
        unreachable!()
    };
    if pushes.len() != 1 || first != 0 || !orig.contains(&Reg::LR) {
        return refuse(format!(
            "only a single entry `push {{.., lr}}` is lowered (found {} PUSH, first `{:?}`)",
            pushes.len(),
            out[first].op
        ));
    }
    let core: Vec<Reg> = orig.iter().filter(|r| **r != Reg::LR).copied().collect();
    if let Some(bad) = core
        .iter()
        .find(|r| !matches!(r, Reg::R4 | Reg::R5 | Reg::R6 | Reg::R7 | Reg::R8))
    {
        return refuse(format!("prologue saves {bad:?}, which is not lowered"));
    }
    let want_epilogue: Vec<Reg> = orig
        .iter()
        .map(|r| if *r == Reg::LR { Reg::PC } else { *r })
        .collect();
    for &k in &pops {
        if !matches!(&out[k].op, ArmOp::Pop { regs } if *regs == want_epilogue) {
            return refuse(format!(
                "epilogue `{:?}` restores a different list than the prologue `{:?}` saves",
                out[k].op, out[first].op
            ));
        }
    }
    // The callee-saved registers the lowered body names.
    let mut saves: Vec<Reg> = Vec::new();
    for i in &out {
        if matches!(i.op, ArmOp::Push { .. } | ArmOp::Pop { .. }) {
            continue;
        }
        for r in regs_of(&i.op).unwrap_or_default() {
            if matches!(r, Reg::R4 | Reg::R5 | Reg::R6 | Reg::R7) && !saves.contains(&r) {
                saves.push(r);
            }
        }
    }
    let pad = |saves: &[Reg]| -> Reg {
        *[Reg::R3, Reg::R2, Reg::R4, Reg::R5, Reg::R6]
            .iter()
            .find(|r| !saves.contains(r))
            .expect("a pad register is always free: at most 5 are saved")
    };
    if touches_sp(&out) {
        // SP-relative offsets (incoming stack arguments sit above the push)
        // are measured against the selector's push: keep its size.
        if saves.len() > core.len() {
            return refuse(format!(
                "saving R7 would grow the prologue by {} bytes in a function that \
                 addresses SP",
                4 * (saves.len() - core.len())
            ));
        }
        while saves.len() < core.len() {
            saves.push(pad(&saves));
        }
    } else if (saves.len() + 1) % 2 == 1 {
        // No SP-relative access: the smallest list, with the push+LR count
        // even (8-byte SP alignment).
        saves.push(pad(&saves));
    }
    saves.sort();
    saves.dedup();
    let mut push = saves.clone();
    push.push(Reg::LR);
    let mut pop = saves;
    pop.push(Reg::PC);
    out[first].op = ArmOp::Push { regs: push };
    for &k in &pops {
        out[k].op = ArmOp::Pop { regs: pop.clone() };
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The constant sequences compute the constant, for a spread of shapes.
    #[test]
    fn materialize_computes_the_value() {
        fn eval(ops: &[ArmOp]) -> u32 {
            let mut r = 0u32;
            for op in ops {
                r = match op {
                    ArmOp::Movs {
                        op2: Operand2::Imm(k),
                        ..
                    } => *k as u32,
                    ArmOp::Lsls { shift, .. } => r << shift,
                    ArmOp::Add {
                        op2: Operand2::Imm(k),
                        ..
                    } => {
                        assert!((0..=0xFF).contains(k), "{k}");
                        r.wrapping_add(*k as u32)
                    }
                    ArmOp::Mvns { .. } => !r,
                    o => panic!("unexpected {o:?}"),
                };
            }
            r
        }
        let mut vals = vec![
            0u32,
            1,
            7,
            8,
            255,
            256,
            0x7FFF,
            0xFFFF,
            0x1_0000,
            0x12345678,
            0x8000_0000,
            0xC000_0000,
            0x4000_0000,
            0xBFFF_FFFF,
            0xFFFF_FFFF,
            0xFFFF_FF00,
            0x8000_7FFF,
            0xC000_7FFF,
            0xDEAD_BEEF,
            0x0000_CCCC,
            0x00FF_00FF,
            0x7FFF_FFFF,
        ];
        let mut x: u32 = 0x9E37_79B9;
        for _ in 0..20_000 {
            x ^= x << 13;
            x ^= x >> 17;
            x ^= x << 5;
            vals.push(x);
            vals.push(x >> (x & 31));
        }
        for v in vals {
            let ops = materialize(Reg::R3, v);
            assert!(ops.len() <= 7, "{v:#x}: {} ops", ops.len());
            assert_eq!(eval(&ops), v, "{v:#x}: {ops:?}");
        }
        assert_eq!(materialize(Reg::R0, 42).len(), 1);
        assert_eq!(materialize(Reg::R0, 0xFFFF_FFFF).len(), 2);
        assert_eq!(materialize(Reg::R0, 0x8000_0000).len(), 2);
    }

    /// The SetCond diamond is the M2 shape: the condition branch comes
    /// before EITHER flag-setting MOVS.
    #[test]
    fn setcond_is_a_diamond() {
        let s = vec![
            ArmInstruction {
                op: ArmOp::Cmp {
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                },
                source_line: None,
            },
            ArmInstruction {
                op: ArmOp::SetCond {
                    rd: Reg::R2,
                    cond: Condition::LT,
                },
                source_line: None,
            },
        ];
        let out: Vec<ArmOp> = lower(s, 0).unwrap().into_iter().map(|i| i.op).collect();
        assert!(matches!(
            out[1],
            ArmOp::Bcc {
                cond: Condition::LT,
                ..
            }
        ));
        assert!(matches!(out[2], ArmOp::Movs { .. }));
        assert!(matches!(out[3], ArmOp::B { .. }));
        assert!(matches!(out[5], ArmOp::Movs { .. }));
    }

    /// RQ-92-WDGTHIN (#1741): a direct call is passed through as `bl`, LR stays
    /// in the save list, and a value the stream keeps in R8 across the call
    /// is renamed to a CALLEE-saved low register (never R2/R3, which the
    /// callee may clobber).
    #[test]
    fn direct_call_is_lowered_and_keeps_values_in_callee_saved_registers() {
        let ins = |op| ArmInstruction {
            op,
            source_line: None,
        };
        let mov = |rd, rm| {
            ins(ArmOp::Mov {
                rd,
                op2: Operand2::Reg(rm),
            })
        };
        let bl = || {
            ins(ArmOp::Bl {
                label: "func_7".into(),
            })
        };
        let save = vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8];
        let push = {
            let mut regs = save.clone();
            regs.push(Reg::LR);
            ins(ArmOp::Push { regs })
        };
        let pop = {
            let mut regs = save;
            regs.push(Reg::PC);
            ins(ArmOp::Pop { regs })
        };
        let out: Vec<ArmOp> = lower(
            vec![
                push.clone(),
                mov(Reg::R8, Reg::R1),
                bl(),
                mov(Reg::R0, Reg::R8),
                pop.clone(),
            ],
            0,
        )
        .unwrap()
        .into_iter()
        .map(|i| i.op)
        .collect();
        assert!(matches!(&out[2], ArmOp::Bl { label } if label == "func_7"));
        let ArmOp::Mov { rd: kept, .. } = &out[1] else {
            panic!("{:?}", out[1])
        };
        assert!(
            matches!(kept, Reg::R4 | Reg::R5 | Reg::R6),
            "the value live across the call was put in {kept:?}"
        );
        assert_eq!(
            out[3],
            ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(*kept)
            }
        );
        let ArmOp::Push { regs } = &out[0] else {
            panic!("{:?}", out[0])
        };
        assert!(regs.contains(&Reg::LR) && regs.contains(kept), "{regs:?}");
        assert!(!regs.contains(&Reg::R8), "{regs:?}");
        assert_eq!(regs.len() % 2, 0, "8-byte SP alignment at the call");

        // No prologue: LR is not saved, so the call is refused.
        let e = lower(vec![bl(), ins(ArmOp::Bx { rm: Reg::LR })], 0).unwrap_err();
        assert!(e.contains("LR is not saved"), "{e}");

        // The selector's R12 is clobbered by a call (AAPCS IP): a read of it
        // after the call with no write in between is refused, a write first
        // is accepted.
        let read_ip = ins(ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R12),
        });
        let e = lower(
            vec![
                push.clone(),
                mov(Reg::R12, Reg::R1),
                bl(),
                read_ip.clone(),
                pop.clone(),
            ],
            0,
        )
        .unwrap_err();
        assert!(e.contains("reads the scratch R7"), "{e}");
        lower(vec![push, bl(), mov(Reg::R12, Reg::R1), read_ip, pop], 0).unwrap();
    }

    /// RQ-92-WDGTHIN (#1741): only a call with at most four argument words is
    /// lowered; an unknown callee arity is refused, not assumed small.
    #[test]
    fn stack_argument_calls_are_refused() {
        use synth_core::WasmOp;
        let ops = [WasmOp::LocalGet(0), WasmOp::Call(1), WasmOp::End];
        assert!(refuse_stack_argument_call(&ops, &[9, 4]).is_ok());
        assert!(refuse_stack_argument_call(&ops, &[9, 0]).is_ok());
        let e = refuse_stack_argument_call(&ops, &[0, 5]).unwrap_err();
        assert!(
            e.contains("passes 5 arguments") && e.contains("outgoing stack argument"),
            "{e}"
        );
        let e = refuse_stack_argument_call(&ops, &[3]).unwrap_err();
        assert!(e.contains("no known argument count"), "{e}");
        assert!(refuse_stack_argument_call(&[WasmOp::LocalGet(0), WasmOp::End], &[]).is_ok());
    }

    /// F7: an R12 value live across a label is refused (the invariant the
    /// forward scratch-liveness scan rests on); a write after the label is
    /// accepted.
    #[test]
    fn scratch_live_across_a_label_is_refused() {
        let ins = |op| ArmInstruction {
            op,
            source_line: None,
        };
        let and_ip = ins(ArmOp::And {
            rd: Reg::R12,
            rn: Reg::R1,
            op2: Operand2::Imm(31),
        });
        let label = ins(ArmOp::Label { name: ".Lx".into() });
        let shift = ins(ArmOp::LslReg {
            rd: Reg::R2,
            rn: Reg::R2,
            rm: Reg::R12,
        });
        let push = ins(ArmOp::Push {
            regs: vec![Reg::R4, Reg::LR],
        });
        let pop = ins(ArmOp::Pop {
            regs: vec![Reg::R4, Reg::PC],
        });
        let bad = vec![
            push.clone(),
            and_ip.clone(),
            label.clone(),
            shift.clone(),
            pop.clone(),
        ];
        let e = lower(bad, 0).unwrap_err();
        assert!(e.contains("live across control"), "{e}");
        let good = vec![push, label, and_ip, shift, pop];
        assert!(lower(good, 0).is_ok());
    }

    /// R7 / R8 named by the selected stream, and any unlisted op, refuse.
    #[test]
    fn refusals() {
        let one = |op| {
            lower(
                vec![ArmInstruction {
                    op,
                    source_line: None,
                }],
                0,
            )
        };
        for r in [Reg::R9, Reg::R10, Reg::R11] {
            assert!(
                one(ArmOp::Mov {
                    rd: r,
                    op2: Operand2::Reg(Reg::R0)
                })
                .is_err(),
                "{r:?}"
            );
        }
        // A value in R7 or R8 moves, by a whole-function rename, to a
        // register the function never names (R3 first).
        for r in [Reg::R7, Reg::R8] {
            let out = one(ArmOp::Mov {
                rd: r,
                op2: Operand2::Reg(Reg::R0),
            })
            .unwrap();
            assert_eq!(
                out[0].op,
                ArmOp::Mov {
                    rd: Reg::R3,
                    op2: Operand2::Reg(Reg::R0)
                }
            );
        }
        assert!(
            one(ArmOp::Udiv {
                rd: Reg::R0,
                rn: Reg::R0,
                rm: Reg::R1
            })
            .is_err()
        );
        // R12 is renamed to the scratch, which then must be pushed.
        let s = vec![
            ArmInstruction {
                op: ArmOp::Push {
                    regs: vec![Reg::R4, Reg::LR],
                },
                source_line: None,
            },
            ArmInstruction {
                op: ArmOp::And {
                    rd: Reg::R12,
                    rn: Reg::R1,
                    op2: Operand2::Imm(31),
                },
                source_line: None,
            },
            ArmInstruction {
                op: ArmOp::LslReg {
                    rd: Reg::R2,
                    rn: Reg::R0,
                    rm: Reg::R12,
                },
                source_line: None,
            },
            ArmInstruction {
                op: ArmOp::Pop {
                    regs: vec![Reg::R4, Reg::PC],
                },
                source_line: None,
            },
        ];
        let out: Vec<ArmOp> = lower(s, 0).unwrap().into_iter().map(|i| i.op).collect();
        assert!(
            out.iter()
                .all(|o| regs_of(o).is_none_or(|r| !r.contains(&Reg::R12)))
        );
        assert!(
            matches!(&out[0], ArmOp::Push { regs } if regs.contains(&Reg::R7) && regs.len() % 2 == 0)
        );
        assert!(matches!(out.last(), Some(ArmOp::Pop { regs }) if regs.contains(&Reg::R7)));
    }
}
