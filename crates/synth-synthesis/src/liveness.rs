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
use crate::rules::{ArmOp, Condition, MemAddr, Operand2, Reg};
use std::collections::{BTreeMap, BTreeSet};

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
        // #345: rd = full symbol address loaded from the literal pool — pure def
        // of rd (NOT an RMW like Movt), no register use.
        LdrSym { rd, .. } => def_use(vec![*rd], vec![]),
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

        // rd = ra -/+ rn*rm
        Mls { rd, rn, rm, ra } | Mla { rd, rn, rm, ra } => def_use(vec![*rd], vec![*rn, *rm, *ra]),

        // rd = rn <shift> #imm
        Lsl { rd, rn, .. } | Lsr { rd, rn, .. } | Asr { rd, rn, .. } | Ror { rd, rn, .. } => {
            def_use(vec![*rd], vec![*rn])
        }

        // rd = <unary> rm
        Clz { rd, rm }
        | Rbit { rd, rm }
        | Popcnt { rd, rm }
        | Sxtb { rd, rm }
        | Sxth { rd, rm }
        | Uxtb { rd, rm }
        | Uxth { rd, rm } => def_use(vec![*rd], vec![*rm]),

        // flag-setting compares: read operands, write no GP register
        Cmp { rn, op2 } | Cmn { rn, op2 } => {
            let mut uses = vec![*rn];
            uses.extend(op2_uses(op2));
            def_use(vec![], uses)
        }

        // rd = cond (materialize a flag) — writes rd, reads flags only
        SetCond { rd, .. } => def_use(vec![*rd], vec![]),

        // conditional move (IT-block clamp form): rd = rm if cond, else rd
        // unchanged → rd is both read (preserved branch) and written; rm read.
        // Modeling this keeps the int8-clamp sequences (the #209 const-CSE
        // target) inside one analyzable segment instead of breaking at each
        // predicated move, so the allocator analysis can see the resident
        // clamp-bound constants across the whole clamp chain.
        SelectMove { rd, rm, .. } => def_use(vec![*rd], vec![*rd, *rm]),

        // rd = rcond != 0 ? rval1 : rval2 — writes rd, reads all three inputs.
        Select {
            rd,
            rval1,
            rval2,
            rcond,
        } => def_use(vec![*rd], vec![*rval1, *rval2, *rcond]),

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

/// Conservative NZCV-clobber predicate: `true` if `op` *might* write the
/// condition flags. Used by [`fuse_cmp_select`] to prove the flags set by a
/// comparison survive to the predicated moves once the intervening `SetCond` +
/// `cmp rd,#0` are deleted.
///
/// `reg_effect` deliberately does NOT model the flag side-effect (it tracks only
/// GP registers), so this is a separate, intentionally tight allowlist: only the
/// instructions we are *certain* leave NZCV untouched return `false`. Everything
/// else — flag-setting compares (`Cmp`/`Cmn`/`Tst`), the S-form arithmetic, every
/// unmodeled / pseudo / control-flow op — is treated as a clobber. The only ops
/// that legitimately appear between a `SetCond` and its select's `cmp` are
/// register-resident-operand reloads (loads/stores), which this admits.
fn clobbers_flags(op: &ArmOp) -> bool {
    use ArmOp::*;
    // Allowlist of definitely-flag-preserving ops. NOT included: `Mov` (a low-reg
    // `MOV #imm` is `MOVS` and sets flags), `SelectMove` (only ever appears AFTER
    // the select's cmp, never inside the window), arithmetic of any kind.
    !matches!(
        op,
        Ldr { .. }
            | Ldrb { .. }
            | Ldrsb { .. }
            | Ldrh { .. }
            | Ldrsh { .. }
            | Str { .. }
            | Strb { .. }
            | Strh { .. }
            | Push { .. }
            | Pop { .. }
            | Nop
    )
}

/// VCR-SEL-004 — cmp→select → IT-block predication fusion.
///
/// The selector lowers `(select v1 v2 (i32.lt_s a b))` to a *materialize then
/// re-test* sequence: the comparison emits `cmp a,b; SetCond D,LT` (D ← 0/1), and
/// the select then emits `cmp D,#0; movne dst,v1; moveq dst,v2`. The `SetCond`
/// and the select's `cmp D,#0` are pure overhead — the original comparison
/// already set NZCV, and each `SelectMove` is an independent flag-preserving
/// `IT;MOV` (arm_encoder.rs:4231). This pass collapses the pair: it deletes the
/// `SetCond D,c` and the `cmp D,#0`, and retargets the predicated moves onto the
/// comparison's own flags — `movne→mov{c}` (fires iff `c` held → v1) and
/// `moveq→mov{invert(c)}` (fires iff `c` did not → v2). Net: −2 instructions and
/// the redundant flag round-trip removed, per select.
///
/// Returns the rewritten stream and the number of fusions applied (0 ⇒
/// bit-identical to the input). Removal-only + rename-only, so it is run LATE,
/// after register re-allocation (final register identities) and before encode.
///
/// **Soundness** — a fusion fires only when all hold (else that site is skipped):
/// 1. `[i-1]` is a flag-setting `Cmp`/`Cmn` (the comparison whose flags we reuse;
///    `SetCond` is always emitted immediately after its compare, so this is the
///    comparison that produced `c`).
/// 2. No flag-clobbering op (per [`clobbers_flags`]) and no read/write of `D` sits
///    between the `SetCond` and the select's `cmp D,#0` — so the reused flags and
///    the value of `D` both survive the window (only operand reloads may appear).
/// 3. `D` is provably **dead** after the select: scanning forward, it is
///    *redefined* (written without being read) before any use, any unmodeled op,
///    or any branch/end-of-block. This refuses to delete a `SetCond` whose 0/1
///    boolean is consumed elsewhere (e.g. stored to a local, or returned in R0).
/// 4. `dst != D`, keeping the dead-check unambiguous.
pub fn fuse_cmp_select(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    let (out, total, _two_move) = fuse_cmp_select_with_stats(instrs);
    (out, total)
}

/// Like [`fuse_cmp_select`] but additionally returns the number of *two-move*
/// fusions — the predicated-pair form (`mov{c} dst,v1; mov{invert(c)} dst,v2`)
/// whose `mov{invert(c)}` arm only became reachable through the real selector
/// once `reg_dead_by_redef` learned the return terminator (#7). `in_place =
/// total - two_move` is the single-move form (`mov{c} dst,v1`, dst already
/// holds v2). Diagnostic only: the production path calls the 2-tuple
/// [`fuse_cmp_select`] wrapper; this split feeds `SYNTH_FUSE_STATS` and the
/// fusion census (the blast-radius datum for the default-on flip decision).
/// The rewritten instruction stream is identical to [`fuse_cmp_select`]'s.
pub fn fuse_cmp_select_with_stats(
    instrs: &[ArmInstruction],
) -> (Vec<ArmInstruction>, usize, usize) {
    let n = instrs.len();
    let mut out: Vec<ArmInstruction> = instrs.to_vec();
    let mut delete = vec![false; n];
    let mut fusions = 0usize;
    let mut two_move = 0usize;

    for i in 0..n {
        // [i] must be `SetCond { rd: D, cond: c }`.
        let (d, c) = match instrs[i].op {
            ArmOp::SetCond { rd, cond } => (rd, cond),
            _ => continue,
        };
        // (1) the immediately-preceding op set the flags we will reuse.
        if i == 0 || !matches!(instrs[i - 1].op, ArmOp::Cmp { .. } | ArmOp::Cmn { .. }) {
            continue;
        }
        // (2) walk to the select's `cmp D,#0`, allowing only flag-safe ops that
        // neither read nor write D in between.
        let mut j = i + 1;
        let mut window_ok = true;
        let cmp_idx = loop {
            if j >= n {
                window_ok = false;
                break j;
            }
            if matches!(&instrs[j].op,
                ArmOp::Cmp { rn, op2: Operand2::Imm(0) } if *rn == d)
            {
                break j;
            }
            if clobbers_flags(&instrs[j].op) {
                window_ok = false;
                break j;
            }
            match reg_effect(&instrs[j].op) {
                Some(eff) if !eff.uses.contains(&d) && !eff.defs.contains(&d) => {}
                _ => {
                    window_ok = false;
                    break j;
                }
            }
            j += 1;
        };
        if !window_ok {
            continue;
        }
        // (next) `movne dst,v1`.
        let ne_idx = cmp_idx + 1;
        let (dst, v1) = match instrs.get(ne_idx).map(|x| &x.op) {
            Some(ArmOp::SelectMove {
                rd,
                rm,
                cond: Condition::NE,
            }) => (*rd, *rm),
            _ => continue,
        };
        if dst == d {
            continue;
        }
        // optional `moveq dst,v2` (the in-place select omits it).
        let eq_idx = match instrs.get(ne_idx + 1).map(|x| &x.op) {
            Some(ArmOp::SelectMove {
                rd,
                cond: Condition::EQ,
                ..
            }) if *rd == dst => Some(ne_idx + 1),
            _ => None,
        };
        // (3) D must be dead after the select block: a redefinition (def, no use)
        // strictly before any use / unmodeled op / branch / end.
        let after = eq_idx.unwrap_or(ne_idx) + 1;
        if !reg_dead_by_redef(d, &instrs[after..]) {
            continue;
        }

        // Commit: delete SetCond and the select's cmp; retarget the moves.
        delete[i] = true;
        delete[cmp_idx] = true;
        out[ne_idx].op = ArmOp::SelectMove {
            rd: dst,
            rm: v1,
            cond: c,
        };
        if let Some(eq) = eq_idx
            && let ArmOp::SelectMove { rd, rm, .. } = out[eq].op
        {
            out[eq].op = ArmOp::SelectMove {
                rd,
                rm,
                cond: c.invert(),
            };
            // The optional `moveq` arm is present ⇒ this is the two-move form.
            two_move += 1;
        }
        fusions += 1;
    }

    if fusions == 0 {
        return (out, 0, 0);
    }
    let result: Vec<ArmInstruction> = out
        .into_iter()
        .enumerate()
        .filter(|(k, _)| !delete[*k])
        .map(|(_, x)| x)
        .collect();
    (result, fusions, two_move)
}

/// Redundant stack-reload elimination — perf lever 1 toward native parity (#390,
/// #209, epic #242). synth lowers every wasm local to a frame slot, so a
/// `local.set` then `local.get` of the same local emits `str rX,[sp,#N]; … ;
/// ldr rY,[sp,#N]` — a memory store-then-reload of one slot (≈18 % of the hot
/// fixture's instructions are sp traffic; an M4 stack load is ~2 cycles). When the
/// stored register `rX` still holds the value at the `ldr` — nothing rewrites `rX`,
/// nothing rewrites slot `N`, `sp` does not move, and there is no call / branch /
/// label between (the forward scan bails via `reg_effect → None` on any of those,
/// the same soundness lynchpin as [`fuse_cmp_select`]) — the `ldr` is replaced by
/// `mov rY, rX` (~1 cycle). The `str` is KEPT: the slot may still be read past a
/// boundary the scan bailed at. Removal-of-a-load + rename only ⇒ NO new instruction
/// form (no validator change) and labels/branch offsets are untouched. Returns the
/// rewritten stream and the number of reloads forwarded (0 ⇒ input unchanged).
pub fn forward_stack_reloads(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    let n = instrs.len();
    let mut out = instrs.to_vec();
    let mut rewrites = 0usize;

    for i in 0..n {
        // [i] must be `str rX, [sp, #N]` (immediate slot, no register offset).
        let (rx, slot) = match &instrs[i].op {
            ArmOp::Str { rd, addr } if addr.base == Reg::SP && addr.offset_reg.is_none() => {
                (*rd, addr.offset)
            }
            _ => continue,
        };
        // Forward `rX` into same-slot loads until it (or the slot, or sp) changes
        // or the scan reaches an op it cannot reason past.
        for j in (i + 1)..n {
            // A reload of the same slot ⇒ rewrite to `mov rY, rX`. `rX` is still
            // the live source, so keep scanning — a later same-slot load forwards too.
            if let ArmOp::Ldr { rd: ry, addr } = &out[j].op
                && addr.base == Reg::SP
                && addr.offset_reg.is_none()
                && addr.offset == slot
            {
                let ry = *ry;
                out[j].op = ArmOp::Mov {
                    rd: ry,
                    op2: Operand2::Reg(rx),
                };
                rewrites += 1;
                continue;
            }
            // A store that could land in slot N (same immediate, or any register
            // offset we cannot resolve) ⇒ the slot's value may change; stop.
            if let ArmOp::Str { addr, .. } = &instrs[j].op
                && addr.base == Reg::SP
                && (addr.offset_reg.is_some() || addr.offset == slot)
            {
                break;
            }
            match reg_effect(&instrs[j].op) {
                // `rX` clobbered or the frame pointer moved ⇒ value no longer valid.
                Some(eff) if eff.defs.contains(&rx) || eff.defs.contains(&Reg::SP) => break,
                Some(_) => {}
                // call / branch / label / unmodeled op ⇒ cannot reason past it.
                None => break,
            }
        }
    }

    (out, rewrites)
}

/// VCR-RA frame-slot dead-store elimination (#242, epic #242): remove a
/// `str rX, [sp, #N]` whose spill slot `N` is provably never read again before
/// it is overwritten or the function ends. This is the natural completion of
/// [`forward_stack_reloads`]: once the reloads of a slot have been forwarded to
/// register moves, the store that fed them writes a value nobody loads — pure
/// dead weight. `eliminate_dead_stores` cannot catch it (a store defines no
/// register, so its register-def liveness is vacuous); slot liveness is what's
/// needed.
///
/// SOUNDNESS — a store at `i` to `[sp, #N]` (immediate slot, no register offset)
/// is removed only if a forward scan from `i+1` reaches either the next store to
/// the SAME immediate slot `N`, or the end of the function, WITHOUT encountering
/// anything that could read slot `N` or that we cannot reason past. The scan
/// conservatively KEEPS the store (proves nothing) at the first of:
///  - a `ldr` from `[sp, #N]` (the slot is read — live),
///  - ANY `[sp, reg-offset]` load or store (slot unresolvable — could touch `N`),
///  - a `Push`/`Pop` (touches the stack region — could overlap `N`),
///  - a call (`Bl`/`Blx`/`Call`/`CallIndirect`: a callee may read an outgoing
///    stack-argument slot),
///  - any op that defines `SP` (frame geometry changed — `#N` no longer names
///    the same location),
///  - any op `reg_effect` does not model (branch / label / unmodeled): control
///    could reach a reader, so we cannot prove deadness on a straight line.
///
/// Only the immediate-offset `Str`/`Ldr` forms participate; everything else is a
/// blocker. This makes the pass effective on straight-line leaf regions (the
/// frame-resident hot kernels) and a conservative no-op elsewhere — it never
/// removes a store whose slot any reachable instruction might load.
///
/// LOAD-BEARING ASSUMPTION: spill slots are word-aligned and non-overlapping, so
/// a `str [sp,#N]` is the ONLY writer of those 4 bytes and a different immediate
/// `#M` provably does not alias `#N`. The sub-word-access blocker above is what
/// enforces "no partial writers/readers"; do not widen the participating set
/// without re-checking this.
///
/// **Branch-offset safety:** like [`forward_stack_reloads`] and
/// [`eliminate_dead_stores`], intended to run on the `select_with_stack` output
/// BEFORE `resolve_label_branches`; removing a non-branch interior instruction is
/// offset-neutral. The frame `sub sp,#K` is untouched (the slot just goes unused),
/// so SP balance is preserved — frame SHRINKING is [`elide_dead_frame`]'s job.
/// Pure function; callers opt in.
pub fn eliminate_dead_frame_stores(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    let n = instrs.len();
    let mut dead: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();

    for i in 0..n {
        // [i] must be `str rX, [sp, #N]` (immediate slot, no register offset).
        let slot = match &instrs[i].op {
            ArmOp::Str { addr, .. } if addr.base == Reg::SP && addr.offset_reg.is_none() => {
                addr.offset
            }
            _ => continue,
        };
        // Scan forward for an OVERWRITE of slot N with no intervening read or
        // aliasing op. A store is proven dead ONLY by a later store to the same
        // immediate slot (classic dead-store-before-overwrite) — reaching the end
        // of the function does NOT count (that "abandoned at frame teardown" case
        // needs epilogue reasoning we deliberately do not do here, so the default
        // is to KEEP). This makes the pass unconditionally sound: it never removes
        // a store whose slot any reachable instruction might load.
        let mut overwritten = false;
        for scan in &instrs[i + 1..] {
            match &scan.op {
                // A reload of the SAME immediate slot ⇒ the value is used ⇒ live.
                ArmOp::Ldr { addr, .. }
                    if addr.base == Reg::SP && addr.offset_reg.is_none() && addr.offset == slot =>
                {
                    break;
                }
                // Overwrite of the SAME immediate slot with no intervening read ⇒
                // THIS store is dead (its value never escaped the slot).
                ArmOp::Str { addr, .. }
                    if addr.base == Reg::SP && addr.offset_reg.is_none() && addr.offset == slot =>
                {
                    overwritten = true;
                    break;
                }
                // Any sp-relative access we cannot pin to a single slot
                // (register offset) could touch slot N ⇒ stop. Distinct immediate
                // slots do not alias, so a different #M is fine and falls through
                // to the reg_effect handling below.
                ArmOp::Ldr { addr, .. } | ArmOp::Str { addr, .. }
                    if addr.base == Reg::SP && addr.offset_reg.is_some() =>
                {
                    break;
                }
                // Sub-word sp-relative access: a `ldrb`/`ldrh`/… reads (or a
                // `strb`/`strh` partially writes) bytes that may fall inside slot
                // N. The overwrite rule below assumes the only writer/reader of
                // slot N's word is a full-word `Str`/`Ldr [sp,#N]`; any narrower
                // sp access breaks that, so stop. (Today's spill slots are
                // word-aligned and accessed only full-word — linear-memory
                // sub-word traffic goes through R11 — but this guard is what keeps
                // the pass sound if that ever changes.)
                ArmOp::Ldrb { addr, .. }
                | ArmOp::Ldrsb { addr, .. }
                | ArmOp::Ldrh { addr, .. }
                | ArmOp::Ldrsh { addr, .. }
                | ArmOp::Strb { addr, .. }
                | ArmOp::Strh { addr, .. }
                    if addr.base == Reg::SP =>
                {
                    break;
                }
                // Stack-region register lists could overlap slot N.
                ArmOp::Push { .. } | ArmOp::Pop { .. } => break,
                // A callee may read an outgoing stack-argument slot.
                ArmOp::Bl { .. }
                | ArmOp::Blx { .. }
                | ArmOp::Call { .. }
                | ArmOp::CallIndirect { .. } => break,
                _ => {}
            }
            // SP redefinition or an unmodeled op (branch/label/...) ⇒ cannot prove
            // the slot stays dead past here.
            match reg_effect(&scan.op) {
                Some(eff) if eff.defs.contains(&Reg::SP) => break,
                Some(_) => {}
                None => break,
            }
        }
        if overwritten {
            dead.insert(i);
        }
    }

    if dead.is_empty() {
        return (instrs.to_vec(), 0);
    }
    let kept: Vec<ArmInstruction> = instrs
        .iter()
        .enumerate()
        .filter(|(i, _)| !dead.contains(i))
        .map(|(_, ins)| ins.clone())
        .collect();
    (kept, dead.len())
}

/// VCR-RA whole-function frame-slot liveness (#242, VCR-RA-001): remove a
/// `str rX, [sp, #N]` whose slot is provably never READ anywhere the store can
/// reach — including the reach-end case [`eliminate_dead_frame_stores`]
/// deliberately keeps. That pass proves deadness only via a later same-slot
/// overwrite on a straight line ("reach-end ≠ dead" — the #515 stance, because
/// segment-local reasoning cannot see past its scope). This pass supplies the
/// missing whole-function view: it walks every path the store can reach
/// (fall-through + label/branch edges, loops included) and drops the store only
/// when NO reachable instruction can observe the slot's bytes. flat_flight's
/// two surviving spill stores (#576) are exactly this shape — their slots are
/// never loaded again anywhere in the function.
///
/// ADMISSION (whole function declines — returns the input unchanged — on the
/// first violation; per-slot precision is never traded for soundness):
///  - any sp-relative access with a REGISTER offset (`[sp, rM]`): the touched
///    slot is unresolvable, so every slot would have to be assumed live;
///  - SP used as a general operand (`add rD, sp, #x`, `mov rD, sp`,
///    `[rN, sp]`, …): the frame address ESCAPES into a register, and a later
///    plain `ldr [rD]` could read any slot invisibly;
///  - SP redefined by anything other than the tracked shapes (`add/sub
///    sp, sp, #imm`, `Push`, `Pop`): the frame geometry becomes untrackable;
///  - a call (`Bl`/`Blx`/`Call`/`CallIndirect`): a callee may read an outgoing
///    stack-argument slot through its own view of SP;
///  - a branch whose target cannot be resolved (numeric `BOffset`/
///    `BCondOffset` — this pass runs BEFORE `resolve_label_branches` — a
///    `BrTable`, a missing/duplicate label, or an indirect `Bx` that is not the
///    `bx lr` return);
///  - any op [`reg_effect`] does not model (i64-pair pseudo-ops, FP, memory
///    builtins, …): its memory behavior is unknown.
///
/// THE WALK — per candidate store, a may-reach traversal over states
/// `(index, sp_delta)` where `sp_delta` is SP's displacement from its value at
/// the store (so slot `N` occupies bytes `[N, N+4)` in store-time coordinates,
/// and an access `[sp, #M]` under displacement `d` touches `[d+M, d+M+w)`):
///  - a load (`ldr`/`ldrb`/`ldrsb`/`ldrh`/`ldrsh [sp, #M]`) whose byte
///    interval OVERLAPS the slot ⇒ the store is LIVE (sub-word reads thus count
///    as reads of their containing word — the #483-class lesson);
///  - a whole-word `str [sp, #M]` with `d+M == N` COVERS the slot ⇒ the path
///    dies (classic overwrite-kill); any partial overlap is neither a read nor
///    a kill and the walk continues;
///  - `add/sub sp, sp, #imm` adjusts `d` and is NOT a read (frame teardown);
///  - `Push {regs}` writes strictly below SP (no read), `d -= 4·|regs|`;
///  - `Pop {regs}` READS `[d, d+4·|regs|)` — if that overlaps the slot the
///    store is LIVE (a mis-paired epilogue is caught, not assumed away);
///    otherwise it is teardown, `d += 4·|regs|`, and a `pop {…, pc}` ends the
///    path (return);
///  - `bx lr` ends the path; conditional branches fork; unconditional `b`
///    follows its label; falling off the end of the function ends the path
///    (reach-end without a read — the case this pass exists to catch);
///  - a state budget (`16·len + 64` visited states) bounds loops whose SP
///    displacement diverges; exceeding it conservatively keeps the store.
///
/// Removal-only ⇒ the output never grows (asserted) and, run before
/// `resolve_label_branches` like every pass here, is branch-offset neutral.
/// The frame `sub sp, #K` is untouched (the slot goes unused; frame SHRINKING
/// is [`elide_dead_frame`]'s job). Pure function; DEFAULT-ON via the
/// `arm_backend.rs` wiring (`SYNTH_SPILL_REALLOC=0` is the opt-out), same
/// lever as the spill re-choice it completes.
pub fn eliminate_unread_frame_stores(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    use ArmOp::*;

    // ---- Admission: label map + whole-function soundness scan. ----
    let mut labels: BTreeMap<&str, usize> = BTreeMap::new();
    for (i, ins) in instrs.iter().enumerate() {
        if let Label { name } = &ins.op
            && labels.insert(name.as_str(), i).is_some()
        {
            return (instrs.to_vec(), 0); // duplicate label: ambiguous CFG
        }
    }
    for ins in instrs {
        let admissible = match &ins.op {
            Label { .. } => true,
            B { label } | Bhs { label } | Blo { label } | Bcc { label, .. } => {
                labels.contains_key(label.as_str())
            }
            // Only the `bx lr` return form: any other indirect jump could land
            // anywhere, so "no successors" would be a wrong CFG.
            Bx { rm } => *rm == Reg::LR,
            Push { .. } | Pop { .. } => true,
            // Tracked frame adjust: add/sub sp, sp, #imm.
            Add {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(_),
            }
            | Sub {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(_),
            } => true,
            // sp-relative memory access: must be a pinnable immediate slot.
            Ldr { addr, .. }
            | Ldrb { addr, .. }
            | Ldrsb { addr, .. }
            | Ldrh { addr, .. }
            | Ldrsh { addr, .. }
            | Str { addr, .. }
            | Strb { addr, .. }
            | Strh { addr, .. }
                if addr.base == Reg::SP =>
            {
                addr.offset_reg.is_none()
            }
            // Everything else: must be fully modeled AND not touch SP at all
            // (an SP use here is an address-of-frame ESCAPE; an SP def is an
            // untracked frame move). Calls, BrTable, numeric branch offsets and
            // unmodeled pseudo-ops all land in the `None` arm.
            op => match reg_effect(op) {
                Some(eff) => !eff.uses.contains(&Reg::SP) && !eff.defs.contains(&Reg::SP),
                None => false,
            },
        };
        if !admissible {
            return (instrs.to_vec(), 0);
        }
    }

    // ---- Per-store may-reach walk. ----
    let dead: std::collections::BTreeSet<usize> = instrs
        .iter()
        .enumerate()
        .filter(|(i, ins)| match &ins.op {
            Str { addr, .. } => {
                sp_slot(addr).is_some_and(|slot| frame_slot_unread_from(instrs, &labels, *i, slot))
            }
            _ => false,
        })
        .map(|(i, _)| i)
        .collect();

    if dead.is_empty() {
        return (instrs.to_vec(), 0);
    }
    let kept: Vec<ArmInstruction> = instrs
        .iter()
        .enumerate()
        .filter(|(i, _)| !dead.contains(i))
        .map(|(_, ins)| ins.clone())
        .collect();
    // Guard: removal-only — the function can only shrink.
    assert!(
        kept.len() + dead.len() == instrs.len(),
        "eliminate_unread_frame_stores must be removal-only"
    );
    (kept, dead.len())
}

/// The may-reach walk of [`eliminate_unread_frame_stores`]: `true` iff no
/// instruction reachable from the store at `start` can read slot
/// `[slot, slot+4)` (byte interval in store-time SP coordinates). The stream
/// has already passed the admission scan, so every op encountered is one of
/// the tracked shapes.
fn frame_slot_unread_from(
    instrs: &[ArmInstruction],
    labels: &BTreeMap<&str, usize>,
    start: usize,
    slot: i32,
) -> bool {
    use ArmOp::*;
    let n = instrs.len();
    let max_states = 16 * n + 64;
    let slot = i64::from(slot);
    // An access at [sp, #M] of width w under displacement d overlaps the slot?
    let reads_slot = |d: i64, m: i32, w: i64| {
        let lo = d + i64::from(m);
        lo < slot + 4 && slot < lo + w
    };

    let mut visited: std::collections::BTreeSet<(usize, i64)> = std::collections::BTreeSet::new();
    // Work list of (index, sp_delta) states still to examine.
    let mut work: Vec<(usize, i64)> = vec![(start + 1, 0)];
    while let Some((i, d)) = work.pop() {
        if i >= n || !visited.insert((i, d)) {
            continue; // fell off the end (reach-end ≠ read) or already seen
        }
        if visited.len() > max_states {
            return false; // budget exceeded: conservatively live
        }
        match &instrs[i].op {
            // sp-relative loads: any byte overlap with the slot is a read.
            Ldr { addr, .. } if addr.base == Reg::SP => {
                if reads_slot(d, addr.offset, 4) {
                    return false;
                }
                work.push((i + 1, d));
            }
            Ldrb { addr, .. } | Ldrsb { addr, .. } if addr.base == Reg::SP => {
                if reads_slot(d, addr.offset, 1) {
                    return false;
                }
                work.push((i + 1, d));
            }
            Ldrh { addr, .. } | Ldrsh { addr, .. } if addr.base == Reg::SP => {
                if reads_slot(d, addr.offset, 2) {
                    return false;
                }
                work.push((i + 1, d));
            }
            // Whole-word store covering the slot exactly: overwrite-kill — the
            // path dies. Anything else (partial overlap, other slot, sub-word
            // store) is neither a read nor a kill.
            Str { addr, .. } if addr.base == Reg::SP => {
                if d + i64::from(addr.offset) != slot {
                    work.push((i + 1, d));
                }
            }
            // Tracked frame adjusts — teardown, not a read.
            Add {
                rd: Reg::SP,
                op2: Operand2::Imm(k),
                ..
            } => work.push((i + 1, d + i64::from(*k))),
            Sub {
                rd: Reg::SP,
                op2: Operand2::Imm(k),
                ..
            } => work.push((i + 1, d - i64::from(*k))),
            // Push writes strictly below SP: no read; SP drops.
            Push { regs } => work.push((i + 1, d - 4 * regs.len() as i64)),
            // Pop READS [d, d+4·|regs|): a mis-paired epilogue that would read
            // the slot keeps the store; the normal `add sp,#K; pop` epilogue
            // has d ≥ K > slot and is teardown. `pop {…, pc}` returns.
            Pop { regs } => {
                if slot >= d && slot < d + 4 * regs.len() as i64 {
                    return false;
                }
                if !regs.contains(&Reg::PC) {
                    work.push((i + 1, d + 4 * regs.len() as i64));
                }
            }
            // Control flow (targets exist — admission checked).
            B { label } => work.push((labels[label.as_str()], d)),
            Bhs { label } | Blo { label } | Bcc { label, .. } => {
                work.push((i + 1, d));
                work.push((labels[label.as_str()], d));
            }
            Bx { .. } => {} // `bx lr` return: path ends
            // Every other admitted op neither touches the frame nor moves SP.
            _ => work.push((i + 1, d)),
        }
    }
    true
}

/// VCR-RA immediate-shift folding (#390, epic #242): fold a register-materialized
/// constant shift amount into an immediate shift, dropping the `movw`.
///
/// The stack selector lowers `i32.shl`/`shr_s`/`shr_u` to the REGISTER shift forms
/// (`LslReg`/`AsrReg`/`LsrReg`), so a constant shift amount on the operand stack is
/// first materialized into a scratch register (`movw rM, #C`) and then consumed
/// (`lsl rD, rN, rM`). This rewrites the pair to the IMMEDIATE form
/// (`lsl rD, rN, #C`) and removes the now-dead `movw` — −1 instruction and −1 live
/// register. Real on the hot path: flight_seam `movw r7,#24; lsl r8,r6,r7` and
/// flight_seam_flat `movw r2,#24; lsl r3,r1,r2`.
///
/// SOUNDNESS:
/// - **Shift range `C ∈ [1,31]`.** Only there do the register- and immediate-shift
///   forms provably agree: the register shift uses `rM mod 256` capped (≥32 ⇒ 0 for
///   LSL/LSR), which the 5-bit immediate cannot encode; and immediate `lsr/asr #0`
///   means shift-by-32 (≠ register shift by 0). `C ∈ [1,31]` sidesteps both — and
///   `movw` materializes the exact value, so the register really held `C`.
/// - **`rM` is the shift AMOUNT, not the value** (`rm == M`, `rn != M`): if `rn==M`
///   the shift also reads `M` as its input, so the `movw` can't be dropped.
/// - **`M` untouched between** the `movw` and the shift (not read — else its value
///   is used elsewhere; not redefined — else it isn't `C` at the shift), and the
///   scan bails on any unmodeled op (`reg_effect → None`: call/branch/label).
/// - **`M` dead after the shift** ([`reg_dead_by_redef`]: redefined-before-read, or
///   a return terminator where `M` is not an ABI result reg). Then the `movw` is a
///   dead store and is removed.
///
/// **Branch-offset safety:** like [`eliminate_dead_stores`], intended to run on the
/// `select_with_stack` output BEFORE `resolve_label_branches`, where branches are
/// symbolic labels — removing a non-branch interior instruction is offset-neutral.
/// Pure function; callers opt in (flag-gated wiring is a separate, oracle-gated step).
pub fn fold_immediate_shifts(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    let n = instrs.len();
    let mut out = instrs.to_vec();
    let mut drop_movw: Vec<bool> = vec![false; n];
    let mut folds = 0usize;

    for i in 0..n {
        // [i] must be `movw rM, #C` with C a foldable shift amount.
        let (m, c) = match &instrs[i].op {
            ArmOp::Movw { rd, imm16 } if (1..=31).contains(imm16) => (*rd, *imm16 as u32),
            _ => continue,
        };
        // Find the first op that touches M; it must be the consuming Reg-shift.
        for j in (i + 1)..n {
            // The shift consuming M as its amount.
            let shifted = match &out[j].op {
                ArmOp::LslReg { rd, rn, rm } if *rm == m && *rn != m => Some(ArmOp::Lsl {
                    rd: *rd,
                    rn: *rn,
                    shift: c,
                }),
                ArmOp::LsrReg { rd, rn, rm } if *rm == m && *rn != m => Some(ArmOp::Lsr {
                    rd: *rd,
                    rn: *rn,
                    shift: c,
                }),
                ArmOp::AsrReg { rd, rn, rm } if *rm == m && *rn != m => Some(ArmOp::Asr {
                    rd: *rd,
                    rn: *rn,
                    shift: c,
                }),
                _ => None,
            };
            if let Some(imm_shift) = shifted {
                // M must be dead after the shift for the movw to be a dead store.
                if reg_dead_by_redef(m, &instrs[j + 1..]) {
                    out[j].op = imm_shift;
                    drop_movw[i] = true;
                    folds += 1;
                }
                break; // M consumed (folded or declined) — done with this movw.
            }
            // Any other read/redef of M, or an unmodeled op, ends this movw's window.
            match reg_effect(&instrs[j].op) {
                Some(eff) if eff.uses.contains(&m) || eff.defs.contains(&m) => break,
                Some(_) => {}
                None => break,
            }
        }
    }

    if folds == 0 {
        return (out, 0);
    }
    let folded: Vec<ArmInstruction> = out
        .into_iter()
        .enumerate()
        .filter(|(i, _)| !drop_movw[*i])
        .map(|(_, ins)| ins)
        .collect();
    (folded, folds)
}

/// VCR-RA peephole (#428, #242): fold a 16/8-bit mask materialized into a scratch
/// register and consumed by `AND` into the dedicated zero-extend instruction.
///
/// ```text
/// movw rM, #0xffff ; and rD, rN, rM   ->   uxth rD, rN   (rD = rN & 0xffff)
/// movw rM, #0x00ff ; and rD, rN, rM   ->   uxtb rD, rN   (rD = rN & 0x00ff)
/// ```
///
/// `0xffff`/`0xff` are not Thumb-2 modified immediates, so the selector must
/// materialize the mask into a register (`movw`) and use the register form of AND;
/// `uxth`/`uxtb` express the same masking in one instruction, freeing the scratch
/// register. Sound unconditionally: `r & 0xffff` and `r & 0xff` are exactly what
/// UXTH/UXTB compute (rotation 0). AND is commutative, so the masked source is
/// whichever operand is not the materialized mask register.
///
/// Same soundness scaffolding as [`fold_immediate_shifts`]: the mask register `M`
/// must be untouched between the `movw` and the `and`, and **dead after** the `and`
/// (`reg_dead_by_redef`) for the `movw` to be a removable dead store. Removal-only
/// and rewrite-in-place, so offset-neutral (no labels/branches move). Pure
/// function; callers opt in (flag-gated wiring is a separate, oracle-gated step).
pub fn fold_uxth(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    use crate::rules::Operand2;
    let n = instrs.len();
    let mut out = instrs.to_vec();
    let mut drop_movw: Vec<bool> = vec![false; n];
    let mut folds = 0usize;

    for i in 0..n {
        // [i] must be `movw rM, #0xffff` (→ uxth) or `#0xff` (→ uxtb).
        let (m, wide) = match &instrs[i].op {
            ArmOp::Movw { rd, imm16: 0xffff } => (*rd, true),
            ArmOp::Movw { rd, imm16: 0x00ff } => (*rd, false),
            _ => continue,
        };
        for j in (i + 1)..n {
            // The AND consuming M as one operand; the source is the OTHER operand.
            let extended = match &out[j].op {
                ArmOp::And {
                    rd,
                    rn,
                    op2: Operand2::Reg(rm),
                } if *rm == m && *rn != m => Some((*rd, *rn)),
                ArmOp::And {
                    rd,
                    rn,
                    op2: Operand2::Reg(rm),
                } if *rn == m && *rm != m => Some((*rd, *rm)),
                _ => None,
            };
            if let Some((rd, src)) = extended {
                // The movw must be a dead store once the AND (its only consumer of
                // M in this window) becomes a `uxth/uxtb` that doesn't read M. That
                // holds if either the fold's destination IS M — `and M,src,M`
                // ⇒ `uxth M,src` redefines M, killing the movw — or M is otherwise
                // dead after the AND.
                if rd == m || reg_dead_by_redef(m, &instrs[j + 1..]) {
                    out[j].op = if wide {
                        ArmOp::Uxth { rd, rm: src }
                    } else {
                        ArmOp::Uxtb { rd, rm: src }
                    };
                    drop_movw[i] = true;
                    folds += 1;
                }
                break; // M consumed (folded or declined) — done with this movw.
            }
            // Any other read/redef of M, or an unmodeled op, ends this movw's window.
            match reg_effect(&instrs[j].op) {
                Some(eff) if eff.uses.contains(&m) || eff.defs.contains(&m) => break,
                Some(_) => {}
                None => break,
            }
        }
    }

    if folds == 0 {
        return (out, 0);
    }
    let folded: Vec<ArmInstruction> = out
        .into_iter()
        .enumerate()
        .filter(|(i, _)| !drop_movw[*i])
        .map(|(_, ins)| ins)
        .collect();
    (folded, folds)
}

/// True if `op` returns from the function: `Bx LR`, or a `Pop`/`Ldmia` that loads
/// `PC` (the `pop {…, pc}` epilogue). At such a point the only registers live out
/// of the function are the ABI result registers — see [`RETURN_VALUE_REGS`].
///
/// SOUNDNESS ASSUMPTION: `Bx`/`Pop` are *unconditional* — neither struct carries a
/// condition field, so the scan reaching one means the return is taken on every
/// path. A future *predicated* return (`bxne lr`) would break this: the fall-through
/// edge could still read `d`, yet we'd conclude dead. If such an op is ever added,
/// it must NOT be treated as a return terminator here.
fn is_return_terminator(op: &ArmOp) -> bool {
    match op {
        ArmOp::Bx { rm } => *rm == Reg::LR,
        ArmOp::Pop { regs } => regs.contains(&Reg::PC),
        _ => false,
    }
}

/// The registers that may carry a wasm function's result, hence be live at the
/// return: `R0` (an `i32`/`f32`-in-core result) and `R1` (the high half of an
/// `i64`/`f64`-in-core result — selector convention "result in (R0,R1)",
/// instruction_selector.rs). `R2`/`R3` are i64 *operand* inputs, never results,
/// so a boolean parked in `R2`..`R8` is never live out of a return.
const RETURN_VALUE_REGS: [Reg; 2] = [Reg::R0, Reg::R1];

/// True if `d` is provably dead at the start of `rest`. Scanning forward through
/// fully-modeled, straight-line instructions:
///   - a **read** of `d` ⇒ live (`false`);
///   - a **redefinition** of `d` (written, not first read) ⇒ dead (`true`);
///   - a **return terminator** (`Bx LR` / `pop {…,pc}`) reached with `d` not yet
///     read ⇒ dead iff `d` is not a result register (`d ∉ RETURN_VALUE_REGS`),
///     because the only live-out at a return is the result reg(s);
///   - any **unmodeled** op — a call, a *non-return* branch, a `Label` (join
///     point), an i64/FP op — ⇒ `false` ("can't prove"). This bail is the
///     soundness lynchpin: the scan never walks past control flow it cannot
///     reason about, so a value live on some other edge is never mistaken dead.
///
/// This is the deadness oracle for [`fuse_cmp_select`]: the original cmp→select
/// lowering leaves the materialized boolean **abandoned** after the select (used
/// once, not redefined, not live-out), which the redef-only rule declined — the
/// return-terminator case recovers exactly that, soundly.
fn reg_dead_by_redef(d: Reg, rest: &[ArmInstruction]) -> bool {
    let is_result_reg = RETURN_VALUE_REGS.contains(&d);
    for instr in rest {
        // Recognize the return BEFORE reg_effect: `pop {…,pc}` is modeled (would
        // pass through as a plain Pop) and `Bx LR` is unmodeled (would bail) —
        // either way the function exits here and live-out ⊆ result regs.
        if is_return_terminator(&instr.op) {
            return !is_result_reg;
        }
        match reg_effect(&instr.op) {
            Some(eff) => {
                if eff.uses.contains(&d) {
                    return false; // read before redef ⇒ live
                }
                if eff.defs.contains(&d) {
                    return true; // redefined unused ⇒ dead from here back
                }
            }
            None => return false, // unmodeled (call / non-return branch / label) ⇒ can't prove
        }
    }
    // Ran off the end without seeing a return terminator — a malformed/partial
    // stream; stay conservative.
    false
}

/// A constant materialization whose value is **already available** in a live
/// register at that point — a redundant re-derivation (const-CSE opportunity).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RedundantConst {
    /// Index of the redundant materialization in the instruction stream.
    pub index: usize,
    /// The constant value being (re-)materialized.
    pub value: i32,
    /// A register that already holds `value` at this point.
    pub available_in: Reg,
}

/// If `op` is a single-instruction constant materialization, the `(rd, value)`
/// it produces. Only the 16-bit `Movw` / immediate `Mov` forms are recognized —
/// these are the ones the hot paths re-materialize (saturation clamps `#0x7e` /
/// `#0x7f`, shift amounts, `#0`). A `Movt` builds the high half of a 32-bit
/// constant; it is deliberately *not* recognized here and instead invalidates
/// the tracked value (handled by the caller via `reg_effect`), so a
/// `Movw;Movt` pair is never mistaken for a pure 16-bit constant.
fn const_materialization(op: &ArmOp) -> Option<(Reg, i32)> {
    match op {
        ArmOp::Movw { rd, imm16 } => Some((*rd, *imm16 as i32)),
        ArmOp::Mov {
            rd,
            op2: Operand2::Imm(v),
        } => Some((*rd, *v)),
        _ => None,
    }
}

/// Redundant constant materializations within a straight-line block: each
/// instruction that re-derives a constant **already resident** in a register
/// (not clobbered since). This is the analysis behind const-CSE /
/// rematerialization-avoidance — the dominant hot-path waste gale measured on
/// `flat_flight` (the int8 clamps `#0x7e` / `#0x7f` materialized 6× each,
/// 61% of all constant loads redundant, #209). It is the *forward* dual of
/// [`local_dead_defs`]: that finds a write with no later read; this finds a
/// write whose value was already computed.
///
/// Pure detection — it reports the opportunity; the eventual fix (keep the
/// constant resident across its uses) is the register allocator's job
/// (VCR-RA-001). Returns `None` if the region is not a single straight-line
/// block of fully-modeled instructions, so a result is never a wrong answer.
pub fn redundant_const_defs(instrs: &[ArmInstruction]) -> Option<Vec<RedundantConst>> {
    let mut held: Vec<(Reg, i32)> = Vec::new(); // registers with a known constant
    let mut out = Vec::new();

    for (i, instr) in instrs.iter().enumerate() {
        if !is_straight_line(&instr.op) {
            return None;
        }
        let eff = reg_effect(&instr.op)?;

        if let Some((rd, v)) = const_materialization(&instr.op) {
            // Already available in some register? → redundant re-derivation.
            if let Some(&(r, _)) = held.iter().find(|&&(_, val)| val == v) {
                out.push(RedundantConst {
                    index: i,
                    value: v,
                    available_in: r,
                });
            }
            // `rd` now holds `v` (drop any prior fact about rd first).
            held.retain(|&(r, _)| r != rd);
            held.push((rd, v));
        } else {
            // Any register this instruction writes loses its known constant.
            for d in &eff.defs {
                held.retain(|&(r, _)| r != *d);
            }
        }
    }
    Some(out)
}

/// Aggregate analysis of a whole (possibly branchy) function.
///
/// The per-block detectors ([`local_dead_defs`], [`redundant_const_defs`]) only
/// reason over a single straight-line block and decline (`None`) on any branch.
/// Real functions (e.g. `flat_flight`, with its `br_table` clamps) are a
/// sequence of such blocks separated by control flow. This splits the stream
/// into **maximal straight-line, fully-modeled segments** — a non-straight-line
/// op (branch/call) or an op with no precise [`reg_effect`] ends the current
/// segment — runs both detectors per segment, and reports global indices.
///
/// This is **sound by construction**: a constant resident at the end of one
/// segment is *not* assumed resident in the next (state is reset at every
/// boundary), so cross-block redundancy is under-reported rather than
/// over-reported, and an instruction that can't be modeled never lands inside a
/// segment. It never returns `None` — it analyzes whatever is analyzable and
/// counts the rest as skipped.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FunctionAnalysis {
    /// Global indices of dead stores (overwritten before use within a segment).
    pub dead_defs: Vec<usize>,
    /// Redundant constant materializations (value already resident), global idx.
    pub redundant_consts: Vec<RedundantConst>,
    /// Number of maximal straight-line analyzable segments found.
    pub segments: usize,
    /// Instructions that ended a segment (branch/call/unmodeled) — not analyzed.
    pub skipped: usize,
}

pub fn analyze_function(instrs: &[ArmInstruction]) -> FunctionAnalysis {
    let mut report = FunctionAnalysis::default();
    let mut seg_start = 0usize;

    // Flush [seg_start, end) as one segment, offsetting indices to global.
    let flush = |report: &mut FunctionAnalysis, start: usize, end: usize| {
        if end <= start {
            return;
        }
        let seg = &instrs[start..end];
        report.segments += 1;
        if let Some(d) = local_dead_defs(seg) {
            report.dead_defs.extend(d.into_iter().map(|i| i + start));
        }
        if let Some(rc) = redundant_const_defs(seg) {
            report.redundant_consts.extend(rc.into_iter().map(|mut c| {
                c.index += start;
                c
            }));
        }
    };

    for (i, instr) in instrs.iter().enumerate() {
        let analyzable = is_straight_line(&instr.op) && reg_effect(&instr.op).is_some();
        if !analyzable {
            flush(&mut report, seg_start, i);
            report.skipped += 1;
            seg_start = i + 1;
        }
    }
    flush(&mut report, seg_start, instrs.len());
    report
}

/// Remove provably-dead stores from an instruction stream, returning the
/// rewritten stream and the count removed.
///
/// "Dead" here is exactly [`analyze_function`]'s `dead_defs`: a register write
/// that is *overwritten before any use within its straight-line segment*. Such
/// a write is dead regardless of cross-block liveness (the in-segment redefine
/// proves it), so deleting it preserves observable behavior. This is the
/// generic, function-wide form of the hand-rolled #221 peephole
/// (`drop_prev_const_materialization`), and the first **transform** on the
/// allocator track — the migration of the merged analyses into a codegen pass.
///
/// **Branch-offset safety:** this is intended to run on the `select_with_stack`
/// output *before* `resolve_label_branches` (arm_backend), where branches are
/// still symbolic labels — removing a non-branch instruction cannot perturb a
/// label-relative target, which is resolved to bytes afterward. The dead
/// instructions are always interior to a straight-line segment and are never
/// branch targets, so the rewrite is offset-neutral by construction.
///
/// Pure function: callers opt in. Not wired into codegen by this change — the
/// wiring is a separate, fully oracle-gated step (every differential fixture
/// must stay result-identical + a measured size/cycle delta + fuzz).
pub fn eliminate_dead_stores(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    let dead: std::collections::BTreeSet<usize> =
        analyze_function(instrs).dead_defs.into_iter().collect();
    if dead.is_empty() {
        return (instrs.to_vec(), 0);
    }
    let kept: Vec<ArmInstruction> = instrs
        .iter()
        .enumerate()
        .filter(|(i, _)| !dead.contains(i))
        .map(|(_, ins)| ins.clone())
        .collect();
    (kept, dead.len())
}

/// Fuse `mul` + `add` into `mla` (#257): for an `Add rD, x, Reg(y)` where one
/// operand is the destination of an earlier `Mul rM, rn, rm`, the result is
/// `mla rD, rn, rm, other`, and the now-redundant `Mul` is removed. Returns the
/// rewritten stream and the number of fusions.
///
/// Soundness conditions (all checked via [`reg_effect`]; any unmodeled
/// instruction conservatively blocks a fusion across it):
///  - the mul result `rM`'s value is **consumed only by the add** — dead after
///    the add until `rM` is next redefined. This is a precise *live-range*
///    check, NOT "rM is read nowhere in the function": the single-pass allocator
///    reuses `rM` for unrelated later values, and reads of those reincarnations
///    must not block the fusion (#257: the whole-function scan fired zero times
///    on the real `flat_flight`, where `r8` is recycled across axes),
///  - between the mul and the add, `rM` and the mul inputs `rn`/`rm` are
///    **neither redefined nor** (for `rM`) **read** — so the `mla` reading
///    `rn`/`rm` at the add's position sees the same values,
///  - `rM` and the other add operand are distinct, and the mul inputs are not
///    `rM` itself.
///
/// Pure function: callers opt in.
pub fn fuse_mul_add(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    let n = instrs.len();
    let mut removed = vec![false; n];
    let mut rewritten: Vec<Option<ArmOp>> = vec![None; n];

    for j in 0..n {
        let (rd, x, y) = match &instrs[j].op {
            ArmOp::Add {
                rd,
                rn,
                op2: Operand2::Reg(rm),
            } => (*rd, *rn, *rm),
            _ => continue,
        };
        for (rmul, rother) in [(x, y), (y, x)] {
            if rmul == rother {
                continue;
            }
            // Most recent live `Mul rmul, mn, mm` before j.
            let Some(i) = (0..j).rev().find(|&k| {
                !removed[k] && matches!(&instrs[k].op, ArmOp::Mul { rd, .. } if *rd == rmul)
            }) else {
                continue;
            };
            let ArmOp::Mul { rn: mn, rm: mm, .. } = instrs[i].op else {
                continue;
            };
            if mn == rmul || mm == rmul {
                continue;
            }
            // Between i and j: no redef of rmul/mn/mm, no read of rmul.
            let between_ok = ((i + 1)..j).all(|k| {
                removed[k]
                    || reg_effect(&instrs[k].op).is_some_and(|e| {
                        !e.defs.contains(&rmul)
                            && !e.defs.contains(&mn)
                            && !e.defs.contains(&mm)
                            && !e.uses.contains(&rmul)
                    })
            });
            if !between_ok {
                continue;
            }
            // The mul result must be consumed ONLY by this add: dead after `j`
            // until `rmul` is next redefined. `between_ok` already proved no read
            // in (i, j). A whole-function "is rmul read anywhere" scan is WRONG —
            // the single-pass allocator REUSES `rmul` for unrelated later values,
            // whose reads would falsely block the fusion (#257: this is exactly
            // why fusion fired zero times on the real flat_flight, where r8 is
            // recycled). Scan forward from j+1: a read of `rmul` before any redef
            // means our value is still live → unsafe; a redef ends its live range
            // → safe; an op we cannot see through (branch/call/pseudo) is treated
            // conservatively as a possible later read → unsafe. When `rmul == rd`
            // the add overwrites it with the (correct) result, so later reads are
            // of the result, not the dangling product — always safe.
            if rmul != rd {
                let mut consumed_only_here = true;
                for k in (j + 1)..n {
                    if removed[k] {
                        continue;
                    }
                    match reg_effect(&instrs[k].op) {
                        Some(e) if e.uses.contains(&rmul) => {
                            consumed_only_here = false; // still live → unsafe
                            break;
                        }
                        Some(e) if e.defs.contains(&rmul) => break, // redef → dead → safe
                        Some(_) => {}                               // unrelated → keep scanning
                        None => {
                            // Unmodeled (branch/call/pseudo): cannot prove the
                            // value is dead past it → bail to stay sound.
                            consumed_only_here = false;
                            break;
                        }
                    }
                }
                if !consumed_only_here {
                    continue;
                }
            }
            rewritten[j] = Some(ArmOp::Mla {
                rd,
                rn: mn,
                rm: mm,
                ra: rother,
            });
            removed[i] = true;
            break;
        }
    }

    let mut fused = 0;
    let mut out = Vec::with_capacity(n);
    for k in 0..n {
        if removed[k] {
            continue;
        }
        match &rewritten[k] {
            Some(op) => {
                fused += 1;
                out.push(ArmInstruction {
                    op: op.clone(),
                    source_line: instrs[k].source_line,
                });
            }
            None => out.push(instrs[k].clone()),
        }
    }
    (out, fused)
}

// ============================================================================
// CFG-aware liveness (VCR-RA-001 substrate)
//
// The per-segment detectors above reset all state at every control-flow
// boundary — sound, but they cannot reason *across* blocks. A spill-capable
// register allocator needs the real thing: for each basic block, the set of
// registers live on entry (`live_in`) and exit (`live_out`), computed by the
// classic backward dataflow fixpoint
//
//     live_in[B]  = use[B] ∪ (live_out[B] − def[B])
//     live_out[B] = ⋃ { live_in[S] : S ∈ succ(B) }
//
// The interference graph an allocator colours is read directly off these sets
// (two registers interfere iff both are live at some common point). This is
// pure analysis — nothing here is wired into codegen, so it cannot change a
// single emitted byte; the fixtures stay bit-identical by construction.
// ============================================================================

/// A basic block of the label-form CFG: the maximal instruction run
/// `[start, end)` with a single entry (its first instruction) and the block
/// indices it can transfer control to (`succ`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BasicBlock {
    /// Global index of the first instruction (inclusive).
    pub start: usize,
    /// Global index one past the last instruction (exclusive).
    pub end: usize,
    /// Successor block indices.
    pub succ: Vec<usize>,
}

/// A function's CFG plus per-block liveness.
///
/// **Scope / soundness.** Built only for functions whose every branch is in the
/// resolvable *label form* (`B`/`Bhs`/`Blo`/`Bcc` targeting a `Label`) and whose
/// every other instruction has a precise [`reg_effect`]. Any numeric-offset
/// branch (`BOffset`/`BCondOffset`), computed/return branch (`Bx`/`Blx`), call
/// (`Bl`/`Call`/`CallIndirect`), `BrTable`, or unmodeled-effect op makes
/// [`cfg_liveness`] return `None` — it never produces a partial or guessed CFG.
/// This is the leaf-function, label-form stage that `select_with_stack` emits
/// before `resolve_label_branches`.
///
/// **Exit liveness caveat (read before driving allocation).** A block with no
/// successors gets `live_out = ∅`. The ABI return-value registers (`R0`, and
/// `R1` for an `i64` result) are therefore *not* counted live at the function
/// exit — that liveness is an external fact the caller must union in before this
/// graph drives spilling, or a return value could be wrongly treated as dead.
/// As pure analysis this is correct w.r.t. the stream's own reads; the ABI
/// augmentation is a deliberately separate, later step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CfgLiveness {
    pub blocks: Vec<BasicBlock>,
    /// `live_in[b]` — registers live entering block `b`.
    pub live_in: Vec<BTreeSet<Reg>>,
    /// `live_out[b]` — registers live leaving block `b`.
    pub live_out: Vec<BTreeSet<Reg>>,
}

/// How a block's final instruction transfers control.
enum Term<'a> {
    /// Unconditional branch to a label — single successor, no fallthrough.
    Uncond(&'a str),
    /// Conditional branch to a label — target plus fallthrough.
    Cond(&'a str),
    /// Straight-line / label-only — falls through to the next block (if any).
    Fall,
    /// Cannot be modeled (numeric-offset branch, computed/return branch, call,
    /// `BrTable`) — the whole analysis declines.
    Unsupported,
}

fn classify(op: &ArmOp) -> Term<'_> {
    use ArmOp::*;
    match op {
        B { label } => Term::Uncond(label),
        Bhs { label } | Blo { label } | Bcc { label, .. } => Term::Cond(label),
        BOffset { .. }
        | BCondOffset { .. }
        | Bx { .. }
        | Blx { .. }
        | Bl { .. }
        | BrTable { .. }
        | Call { .. }
        | CallIndirect { .. } => Term::Unsupported,
        _ => Term::Fall,
    }
}

/// `use`/`def` of one block: registers read before any write in the block
/// (`use`), and registers written anywhere in it (`def`). Branch and `Label`
/// instructions contribute an empty GP-register effect (a conditional branch
/// reads the flags, not a general register).
fn block_use_def(instrs: &[ArmInstruction], b: &BasicBlock) -> (BTreeSet<Reg>, BTreeSet<Reg>) {
    let mut used = BTreeSet::new();
    let mut defined = BTreeSet::new();
    for ins in &instrs[b.start..b.end] {
        let eff = reg_effect(&ins.op).unwrap_or_default();
        for u in &eff.uses {
            if !defined.contains(u) {
                used.insert(*u);
            }
        }
        for d in &eff.defs {
            defined.insert(*d);
        }
    }
    (used, defined)
}

/// Build the label-form CFG of `instrs` and solve per-block liveness, or `None`
/// if the stream contains a construct outside the modeled scope (see
/// [`CfgLiveness`]). Sound by construction: a non-`None` result is a complete,
/// trustworthy CFG + fixpoint, never a partial guess.
pub fn cfg_liveness(instrs: &[ArmInstruction]) -> Option<CfgLiveness> {
    let n = instrs.len();
    if n == 0 {
        return Some(CfgLiveness {
            blocks: vec![],
            live_in: vec![],
            live_out: vec![],
        });
    }

    // 1. Validate every instruction is within the modeled scope.
    for ins in instrs {
        match classify(&ins.op) {
            Term::Unsupported => return None,
            Term::Uncond(_) | Term::Cond(_) => {}
            Term::Fall => {
                if !matches!(ins.op, ArmOp::Label { .. }) && reg_effect(&ins.op).is_none() {
                    return None;
                }
            }
        }
    }

    // 2. Leaders: instruction 0, every `Label`, and every instruction that
    //    follows a branch. (Branch targets are `Label`s, already leaders.)
    let mut is_leader = vec![false; n];
    is_leader[0] = true;
    for i in 0..n {
        if matches!(instrs[i].op, ArmOp::Label { .. }) {
            is_leader[i] = true;
        }
        if matches!(classify(&instrs[i].op), Term::Uncond(_) | Term::Cond(_)) && i + 1 < n {
            is_leader[i + 1] = true;
        }
    }
    let leaders: Vec<usize> = (0..n).filter(|&i| is_leader[i]).collect();

    // 3. Blocks span `[leader, next_leader)`.
    let mut blocks: Vec<BasicBlock> = leaders
        .iter()
        .enumerate()
        .map(|(bi, &start)| BasicBlock {
            start,
            end: leaders.get(bi + 1).copied().unwrap_or(n),
            succ: vec![],
        })
        .collect();

    let block_of_start: BTreeMap<usize, usize> = blocks
        .iter()
        .enumerate()
        .map(|(bi, b)| (b.start, bi))
        .collect();
    let mut block_of_label: BTreeMap<&str, usize> = BTreeMap::new();
    for (bi, b) in blocks.iter().enumerate() {
        if let ArmOp::Label { name } = &instrs[b.start].op {
            block_of_label.insert(name.as_str(), bi);
        }
    }

    // 4. Successors from each block's final instruction. Compute into a side
    //    vector first (immutable borrow of `blocks` for the label lookups),
    //    then write them back.
    let mut succs: Vec<Vec<usize>> = Vec::with_capacity(blocks.len());
    for b in &blocks {
        let last = b.end - 1;
        let fallthrough = block_of_start.get(&b.end).copied();
        let succ = match classify(&instrs[last].op) {
            Term::Uncond(label) => vec![*block_of_label.get(label)?],
            Term::Cond(label) => {
                let t = *block_of_label.get(label)?;
                let mut s = vec![t];
                if let Some(f) = fallthrough
                    && f != t
                {
                    s.push(f);
                }
                s
            }
            Term::Fall => fallthrough.into_iter().collect(),
            Term::Unsupported => return None, // validated above; defensive
        };
        succs.push(succ);
    }
    for (b, succ) in blocks.iter_mut().zip(succs) {
        b.succ = succ;
    }

    // 5. Backward dataflow fixpoint. Sets only grow and are bounded by the
    //    finite register set, so the loop terminates.
    let nb = blocks.len();
    let (use_b, def_b): (Vec<_>, Vec<_>) = blocks.iter().map(|b| block_use_def(instrs, b)).unzip();
    let mut live_in = vec![BTreeSet::<Reg>::new(); nb];
    let mut live_out = vec![BTreeSet::<Reg>::new(); nb];
    let mut changed = true;
    while changed {
        changed = false;
        for bi in (0..nb).rev() {
            let mut out = BTreeSet::new();
            for &s in &blocks[bi].succ {
                out.extend(live_in[s].iter().copied());
            }
            let mut in_ = use_b[bi].clone();
            in_.extend(out.difference(&def_b[bi]).copied());
            if out != live_out[bi] {
                live_out[bi] = out;
                changed = true;
            }
            if in_ != live_in[bi] {
                live_in[bi] = in_;
                changed = true;
            }
        }
    }

    Some(CfgLiveness {
        blocks,
        live_in,
        live_out,
    })
}

// ============================================================================
// Interference graph (VCR-RA-001 — the colouring input)
//
// A graph-colouring register allocator asks: which registers are *simultaneously
// live*, and therefore cannot share one physical register? That relation is the
// interference graph, read directly off the per-instruction liveness derived
// from [`cfg_liveness`]. Walking each block backward from its `live_out`, a
// register *defined* at an instruction interferes with everything live
// immediately *after* that instruction (they coexist), and co-defined registers
// (e.g. `Umull`'s `rdlo`/`rdhi`) interfere with each other. The precision payoff:
// in `add r3, r1, r2` the inputs die at the add, so `r3` does NOT interfere with
// `r1`/`r2` and may reuse one of their registers — a naive "all operands
// interfere" graph would forbid that.
//
// Pure analysis, no codegen callers: it informs a future allocator, it does not
// (yet) drive one, so emitted bytes are unchanged.
// ============================================================================

/// Undirected register interference graph: `a` and `b` are adjacent iff they are
/// ever simultaneously live (so a colouring must give them different physical
/// registers).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct InterferenceGraph {
    adj: BTreeMap<Reg, BTreeSet<Reg>>,
}

impl InterferenceGraph {
    fn node(&mut self, r: Reg) {
        self.adj.entry(r).or_default();
    }

    fn add_edge(&mut self, a: Reg, b: Reg) {
        if a == b {
            return;
        }
        self.adj.entry(a).or_default().insert(b);
        self.adj.entry(b).or_default().insert(a);
    }

    /// Do `a` and `b` interfere (cannot share a physical register)?
    pub fn interferes(&self, a: Reg, b: Reg) -> bool {
        self.adj.get(&a).is_some_and(|s| s.contains(&b))
    }

    /// Registers that interfere with `r`.
    pub fn neighbors(&self, r: Reg) -> impl Iterator<Item = Reg> + '_ {
        self.adj.get(&r).into_iter().flat_map(|s| s.iter().copied())
    }

    /// Interference degree of `r` — the lower bound on distinct registers its
    /// neighbourhood needs; `degree(r) < k` guarantees `r` is `k`-colourable
    /// (the Chaitin/Briggs simplify criterion).
    pub fn degree(&self, r: Reg) -> usize {
        self.adj.get(&r).map_or(0, |s| s.len())
    }

    /// All registers mentioned in the graph (interfering or not).
    pub fn nodes(&self) -> impl Iterator<Item = Reg> + '_ {
        self.adj.keys().copied()
    }

    /// Total number of (undirected) interference edges.
    pub fn edge_count(&self) -> usize {
        self.adj.values().map(|s| s.len()).sum::<usize>() / 2
    }
}

/// Build the interference graph of `instrs`, or `None` if [`cfg_liveness`]
/// declines (a construct outside the modeled leaf-only, label-form scope). Sound
/// by construction: a non-`None` graph is complete for the whole function.
pub fn interference_graph(instrs: &[ArmInstruction]) -> Option<InterferenceGraph> {
    let cfg = cfg_liveness(instrs)?;
    let mut g = InterferenceGraph::default();

    for (bi, b) in cfg.blocks.iter().enumerate() {
        // `live` = registers live immediately AFTER the instruction being
        // processed; seeded with the block's live-out and walked backward.
        let mut live = cfg.live_out[bi].clone();
        for idx in (b.start..b.end).rev() {
            let eff = reg_effect(&instrs[idx].op).unwrap_or_default();
            // Each def interferes with everything live after this instruction
            // and with its co-defs; record defs/uses as nodes regardless.
            for (i, d) in eff.defs.iter().enumerate() {
                g.node(*d);
                for r in &live {
                    g.add_edge(*d, *r);
                }
                for d2 in &eff.defs[i + 1..] {
                    g.add_edge(*d, *d2);
                }
            }
            // live_before = (live − defs) ∪ uses
            for d in &eff.defs {
                live.remove(d);
            }
            for u in &eff.uses {
                g.node(*u);
                live.insert(*u);
            }
        }
    }
    Some(g)
}

// ============================================================================
// Graph colouring (VCR-RA-001 — the allocation decision)
//
// Colouring the interference graph with `k` colours IS register allocation:
// assign every node (value) a colour (physical register) so interfering values
// differ. Chaitin/Briggs:
//   1. SIMPLIFY — repeatedly remove a node of degree < k onto a stack (it can
//      always be coloured after its neighbours, which use ≤ k−1 colours).
//   2. SPILL    — if every remaining node has degree ≥ k, optimistically push
//      one anyway (Briggs: it is often still colourable in practice).
//   3. SELECT   — pop in reverse, giving each node the lowest colour not used by
//      an already-coloured neighbour. A node that finds NO free colour is an
//      actual spill.
//
// This is exactly the decision synth's single-pass allocator cannot make — it
// hard-fails on exhaustion instead of spilling. Pure algorithm over the graph;
// nothing here is wired into codegen.
// ============================================================================

/// Outcome of a `k`-colouring attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ColorResult {
    /// A valid assignment: every node → a colour in `0..k`, adjacent nodes
    /// differ. (Colours map to physical registers at the wiring step.)
    Colored(BTreeMap<Reg, usize>),
    /// Not `k`-colourable by the heuristic; these nodes are the spill set a real
    /// allocator would rewrite to stack slots and then re-attempt.
    Spilled(BTreeSet<Reg>),
}

/// Chaitin/Briggs `k`-colouring of an interference graph with optimistic spill.
/// Returns [`ColorResult::Colored`] with a full assignment, or
/// [`ColorResult::Spilled`] with the nodes that could not be coloured.
///
/// `k == 0` with a non-empty graph is trivially uncolourable (every node
/// spills). Pure function: it computes a decision, it does not mutate codegen.
pub fn color_graph(g: &InterferenceGraph, k: usize) -> ColorResult {
    color_graph_precolored(g, k, &BTreeMap::new())
}

/// `k`-colouring with **precoloured** nodes pinned to fixed colours — the
/// mechanism for honouring synth's reserved registers and ABI pins. Each entry
/// `(reg → colour)` in `precolored` keeps that colour and is never simplified or
/// spilled; it only *constrains* its neighbours (occupying a colour they cannot
/// reuse). Free nodes are coloured/​spilled by the same Chaitin/Briggs pass.
///
/// To reserve physical registers (e.g. keep `R11` = memory base), pin the
/// corresponding node to its colour and treat that colour as taken for the pool;
/// to force args, pin `R0..=R3`. Precoloured colours should be in `0..k`
/// (out-of-range pins are ignored for conflict purposes rather than panicking).
/// Pure function: a decision, not a codegen mutation.
pub fn color_graph_precolored(
    g: &InterferenceGraph,
    k: usize,
    precolored: &BTreeMap<Reg, usize>,
) -> ColorResult {
    // No cost information: every node defaults to cost 1, so minimising
    // cost/degree degenerates to maximising degree — exactly the historic
    // degree-only heuristic (same candidate, same tie-break).
    color_graph_precolored_costed(g, k, precolored, &BTreeMap::new())
}

/// `k`-colouring with precoloured pins **and spill-cost ranking** — VCR-RA-001
/// wiring step 2 (`docs/design/vcr-ra-allocator-wiring.md`).
///
/// When no node can be simplified (every degree ≥ `k`), the optimistic spill
/// candidate is chosen by **Chaitin's metric**: minimise `cost / degree`, where
/// `cost` is the node's def+use occurrence count (each spill inserts a store
/// per def and a reload per use, so cost scales with occurrences) and high
/// degree is *good* to spill (removing the node relieves more interference).
/// Compared cross-multiplied in integers (`cost_a·deg_b < cost_b·deg_a`) to
/// avoid floats; ties break to the smallest register for determinism. A node
/// missing from `costs` defaults to cost 1, so an empty map reproduces the
/// degree-only heuristic exactly. Pure function: a decision, not a mutation.
pub fn color_graph_precolored_costed(
    g: &InterferenceGraph,
    k: usize,
    precolored: &BTreeMap<Reg, usize>,
    costs: &BTreeMap<Reg, usize>,
) -> ColorResult {
    let full: BTreeMap<Reg, BTreeSet<Reg>> =
        g.nodes().map(|n| (n, g.neighbors(n).collect())).collect();
    let (colour, spilled) = chaitin_core(&full, k, precolored, costs);
    if spilled.is_empty() {
        ColorResult::Colored(colour)
    } else {
        ColorResult::Spilled(spilled)
    }
}

/// The Chaitin/Briggs simplify→select core, generic over the node identity —
/// `Reg` for the physical-register graph, `usize` vreg ids for value-range
/// graphs (VCR-RA-001 step 3a). `full` is the complete adjacency: every node
/// (including precoloured ones) with its full neighbour set. Returns
/// `(colouring, spilled)`; an empty spill set means a complete colouring.
/// Pure function — identical algorithm and tie-breaks as the historic
/// `Reg`-typed implementation (a type-parameter refactor, not a behavior
/// change).
fn chaitin_core<N: Ord + Copy>(
    full: &BTreeMap<N, BTreeSet<N>>,
    k: usize,
    precolored: &BTreeMap<N, usize>,
    costs: &BTreeMap<N, usize>,
) -> (BTreeMap<N, usize>, BTreeSet<N>) {
    let cost_of = |r: &N| costs.get(r).copied().unwrap_or(1);
    // Working adjacency over the FREE (non-precoloured) nodes only; precoloured
    // nodes are fixed, so they never enter the simplify worklist — but they
    // remain in every free node's neighbourhood (via `full`) so they still
    // constrain colouring.
    let mut adj: BTreeMap<N, BTreeSet<N>> = full
        .iter()
        .filter(|(n, _)| !precolored.contains_key(n))
        .map(|(n, nbrs)| (*n, nbrs.clone()))
        .collect();
    let mut stack: Vec<N> = Vec::with_capacity(adj.len());

    // SIMPLIFY / SPILL: push every free node, preferring low-degree (< k) nodes;
    // when none qualify, optimistically push the cheapest-to-spill node.
    while !adj.is_empty() {
        let pick = adj
            .iter()
            .find(|(_, nbrs)| nbrs.len() < k)
            .map(|(r, _)| *r)
            .unwrap_or_else(|| {
                // No simplifiable node → optimistic spill candidate: minimise
                // cost/degree (Chaitin), ties to the smallest node id. The
                // comparator never returns Equal for distinct nodes, so the
                // pick is deterministic regardless of iteration order.
                adj.iter()
                    .min_by(|a, b| {
                        (cost_of(a.0) * b.1.len())
                            .cmp(&(cost_of(b.0) * a.1.len()))
                            .then(a.0.cmp(b.0))
                    })
                    .map(|(r, _)| *r)
                    .unwrap()
            });
        // Remove `pick` from the working graph.
        let nbrs = adj.remove(&pick).unwrap_or_default();
        for n in &nbrs {
            if let Some(s) = adj.get_mut(n) {
                s.remove(&pick);
            }
        }
        stack.push(pick);
    }

    // SELECT: pop in reverse, assign the lowest free colour using the ORIGINAL
    // neighbourhood. Seeded with the precoloured pins, so a free node avoids
    // both its precoloured and its already-selected neighbours. A node with no
    // free colour in 0..k is an actual spill.
    let mut colour: BTreeMap<N, usize> = precolored.clone();
    let mut spilled: BTreeSet<N> = BTreeSet::new();
    while let Some(n) = stack.pop() {
        let mut used = vec![false; k];
        if let Some(nbrs) = full.get(&n) {
            for nb in nbrs {
                if let Some(&c) = colour.get(nb)
                    && c < k
                {
                    used[c] = true;
                }
            }
        }
        match (0..k).find(|&c| !used[c]) {
            Some(c) => {
                colour.insert(n, c);
            }
            None => {
                spilled.insert(n);
            }
        }
    }

    (colour, spilled)
}

// ============================================================================
// Allocation verifier (VCR-RA-001 wiring step 1 — the self-check oracle)
//
// `color_graph` PRODUCES an assignment; `verify_allocation` CHECKS one. The two
// are independent code paths, so running the checker on the producer's output
// (or on any externally-supplied assignment — the current physical-register
// layout, or a future allocator's result) is genuine defense-in-depth. Per the
// wiring plan (`docs/design/vcr-ra-allocator-wiring.md`) the wired allocator
// runs this on its own output and refuses to emit on a conflict, so a bad
// allocation can never be silently lowered. Building the oracle FIRST means
// every later wiring sub-step lands already gated. Pure check, no codegen.
// ============================================================================

/// Why an assignment is not a valid colouring of an interference graph.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AllocationConflict {
    /// Two interfering registers were assigned the same colour — they would
    /// clobber each other if both lived in that physical register.
    SameColor { a: Reg, b: Reg, color: usize },
    /// A graph node has no colour in the assignment.
    Unassigned(Reg),
}

/// Verify that `assignment` is a valid colouring of `g`: every node is assigned,
/// and no two interfering nodes share a colour. `Ok(())` means the assignment is
/// safe to lower; `Err` pinpoints the first violation (deterministic in register
/// order). The checker an allocator runs on its own output before emitting.
pub fn verify_allocation(
    g: &InterferenceGraph,
    assignment: &BTreeMap<Reg, usize>,
) -> Result<(), AllocationConflict> {
    // Every node must have a colour.
    for n in g.nodes() {
        if !assignment.contains_key(&n) {
            return Err(AllocationConflict::Unassigned(n));
        }
    }
    // No interfering pair may share a colour.
    for n in g.nodes() {
        let cn = assignment[&n];
        for m in g.neighbors(n) {
            if let Some(&cm) = assignment.get(&m)
                && cn == cm
            {
                return Err(AllocationConflict::SameColor {
                    a: n,
                    b: m,
                    color: cn,
                });
            }
        }
    }
    Ok(())
}

// ============================================================================
// Allocator driver (VCR-RA-001 — the entry point the codegen wiring calls)
//
// Assembles the layer into one call: interference graph → k-colouring (reserved
// registers precoloured) → self-check, plus the rematerialization-avoidance
// opportunity count (the #209 const-CSE headroom). This is the function the
// virtual-register selector output will hand a function to; today it runs on the
// existing physical-register stream as a *shadow* allocation — it computes the
// decision without yet mutating codegen, so it can be measured on the real
// gale benches before anything is wired.
// ============================================================================

/// What the allocator decided for a function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AllocationOutcome {
    /// A valid physical-register assignment (colour = allocatable-pool index).
    Allocated {
        coloring: BTreeMap<Reg, usize>,
        /// Redundant constant materializations the allocator would avoid by
        /// keeping one copy resident — the #209 const-CSE / rematerialization
        /// headroom, measured on this function.
        remat_opportunities: usize,
    },
    /// `k`-colouring failed under the pool budget; these values must spill.
    NeedsSpill(BTreeSet<Reg>),
    /// The function contains a construct the analysis cannot model precisely
    /// (calls, numeric-offset/computed branches, i64-pair / FP ops). The
    /// allocator declines and codegen keeps the existing single-pass path.
    Declined,
}

/// One virtual register: a single def-to-last-use value range that the greedy
/// selector packed into physical register `reg`. `def`/`last_use` are indices
/// into the straight-line segment (a `def == 0` with no instruction-0 def marks
/// a segment input). This is the explicit form of the value the allocator
/// colours — the renaming a re-allocation pass assigns physical registers to.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ValueRange {
    pub vreg: usize,
    pub reg: Reg,
    pub def: usize,
    pub last_use: usize,
}

/// Split each physical register's def-use chains in a straight-line segment into
/// distinct **virtual registers** (value ranges). Returns `None` if the segment
/// is not straight-line / fully modeled. Sound for straight-line code (the
/// reaching definition of every use is unambiguous — the most recent def);
/// cross-block web merging is a separate step. The number of ranges a physical
/// register splits into is exactly the overloading that inflates the physical
/// interference graph (e.g. `R1` → a dozen ranges, one spurious spill); colouring
/// *these* ranges instead is what removes the spurious spill. This is the
/// renaming the eventual virtual-register output / re-allocation consumes.
pub fn straight_line_value_ranges(instrs: &[ArmInstruction]) -> Option<Vec<ValueRange>> {
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new(); // reg → open vreg index
    let mut ranges: Vec<ValueRange> = Vec::new();
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) {
            return None;
        }
        let eff = reg_effect(&ins.op)?;
        for u in &eff.uses {
            let idx = *current.entry(*u).or_insert_with(|| {
                ranges.push(ValueRange {
                    vreg: ranges.len(),
                    reg: *u,
                    def: 0, // input: live from the segment start
                    last_use: i,
                });
                ranges.len() - 1
            });
            ranges[idx].last_use = i;
        }
        for d in &eff.defs {
            let vreg = ranges.len();
            ranges.push(ValueRange {
                vreg,
                reg: *d,
                def: i,
                last_use: i, // dead-on-arrival until a later use extends it
            });
            current.insert(*d, vreg);
        }
    }
    Some(ranges)
}

/// Interference over **value ranges** (vreg ids) — VCR-RA-001 step 3a. Two
/// ranges interfere iff they are simultaneously live:
///
/// ```text
/// a.def < b.last_use && b.def < a.last_use   (strict on both sides)
///   || a.def == b.def                        (co-defined / both inputs)
/// ```
///
/// The strict comparison makes the dies-at-birth boundary deliberately
/// NON-interfering: a value whose last use is the instruction defining `b`
/// is consumed as `b` is born, so `b` may reuse its register — the same
/// convention as the physical `interference_graph` ("defs interfere with
/// everything live *after*") and the in-place-select pattern. Co-defined
/// ranges (`Umull` rdlo/rdhi) and segment inputs (both `def == 0`, live from
/// the segment start) always interfere. An input consumed by instruction 0 is
/// conservatively kept interfering with instruction-0 defs (both have
/// `def == 0`, indistinguishable in this encoding) — sound, at worst one
/// wasted register on that corner. Returns the complete adjacency (isolated
/// ranges present with empty neighbour sets), ready for [`color_ranges`].
pub fn range_interference(ranges: &[ValueRange]) -> BTreeMap<usize, BTreeSet<usize>> {
    let mut adj: BTreeMap<usize, BTreeSet<usize>> =
        ranges.iter().map(|r| (r.vreg, BTreeSet::new())).collect();
    for (i, a) in ranges.iter().enumerate() {
        for b in &ranges[i + 1..] {
            let overlap = (a.def < b.last_use && b.def < a.last_use) || a.def == b.def;
            if overlap {
                adj.get_mut(&a.vreg).unwrap().insert(b.vreg);
                adj.get_mut(&b.vreg).unwrap().insert(a.vreg);
            }
        }
    }
    adj
}

/// `k`-colour a value-range interference graph (from [`range_interference`])
/// with precoloured pins and Chaitin spill-cost ranking — the value-range
/// counterpart of [`color_graph_precolored_costed`], sharing the same core.
/// Returns `(colouring, spilled)`: vreg id → colour (an allocatable-pool
/// index), and the ranges that could not be coloured (the spill candidates a
/// spill-code-insertion pass materialises). Empty spill set = complete
/// colouring. Pins are for ABI/architectural constraints: segment inputs stay
/// in their incoming register, live-outs in their outgoing one. Pure function.
pub fn color_ranges(
    adj: &BTreeMap<usize, BTreeSet<usize>>,
    k: usize,
    precolored: &BTreeMap<usize, usize>,
    costs: &BTreeMap<usize, usize>,
) -> (BTreeMap<usize, usize>, BTreeSet<usize>) {
    chaitin_core(adj, k, precolored, costs)
}

fn map_reg(m: &BTreeMap<Reg, Reg>, r: Reg) -> Reg {
    m.get(&r).copied().unwrap_or(r)
}

fn op2_map(op2: &Operand2, m: &BTreeMap<Reg, Reg>) -> Operand2 {
    match op2 {
        Operand2::Reg(r) => Operand2::Reg(map_reg(m, *r)),
        Operand2::RegShift { rm, shift, amount } => Operand2::RegShift {
            rm: map_reg(m, *rm),
            shift: *shift,
            amount: *amount,
        },
        Operand2::Imm(i) => Operand2::Imm(*i),
    }
}

fn addr_map(a: &MemAddr, m: &BTreeMap<Reg, Reg>) -> MemAddr {
    MemAddr {
        base: map_reg(m, a.base),
        offset: a.offset,
        offset_reg: a.offset_reg.map(|r| map_reg(m, r)),
    }
}

/// Simultaneously rewrite `op`'s registers: definitions through `def_map`,
/// uses through `use_map` (a register absent from a map is unchanged). The
/// positional mirror of [`reg_effect`] — every op it models is rewritten here,
/// covering the same field-by-field def/use classification. Simultaneous
/// substitution is essential: the per-pair `rename_use` applied sequentially
/// mis-rewrites register swaps (`{r0→r1, r1→r0}`).
///
/// Returns `None` for unmodeled ops, and for **read-modify-write** fields
/// (`Movt`/`MovtSym`/`SelectMove` `rd`, which is both def and use of one
/// physical field) when the two maps disagree — the old and new value ranges
/// of an RMW must be assigned the same register (a coalescing constraint the
/// colouring layer does not yet express), so a disagreement is a decline, not
/// a guess.
fn rewrite_op(
    op: &ArmOp,
    use_map: &BTreeMap<Reg, Reg>,
    def_map: &BTreeMap<Reg, Reg>,
) -> Option<ArmOp> {
    use ArmOp::*;
    let u = |r: &Reg| map_reg(use_map, *r);
    let d = |r: &Reg| map_reg(def_map, *r);
    Some(match op {
        Add { rd, rn, op2 } => Add {
            rd: d(rd),
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        Sub { rd, rn, op2 } => Sub {
            rd: d(rd),
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        Adds { rd, rn, op2 } => Adds {
            rd: d(rd),
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        Subs { rd, rn, op2 } => Subs {
            rd: d(rd),
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        Adc { rd, rn, op2 } => Adc {
            rd: d(rd),
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        Sbc { rd, rn, op2 } => Sbc {
            rd: d(rd),
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        And { rd, rn, op2 } => And {
            rd: d(rd),
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        Orr { rd, rn, op2 } => Orr {
            rd: d(rd),
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        Eor { rd, rn, op2 } => Eor {
            rd: d(rd),
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        Rsb { rd, rn, imm } => Rsb {
            rd: d(rd),
            rn: u(rn),
            imm: *imm,
        },
        Mov { rd, op2 } => Mov {
            rd: d(rd),
            op2: op2_map(op2, use_map),
        },
        Mvn { rd, op2 } => Mvn {
            rd: d(rd),
            op2: op2_map(op2, use_map),
        },
        Movw { rd, imm16 } => Movw {
            rd: d(rd),
            imm16: *imm16,
        },
        MovwSym { rd, symbol, addend } => MovwSym {
            rd: d(rd),
            symbol: symbol.clone(),
            addend: *addend,
        },
        // #345: pure def of rd (literal-pool load) — like Movw, not an RMW.
        LdrSym { rd, symbol, addend } => LdrSym {
            rd: d(rd),
            symbol: symbol.clone(),
            addend: *addend,
        },
        // RMW: rd is def AND use of the same field — maps must agree.
        Movt { rd, imm16 } => {
            if d(rd) != u(rd) {
                return None;
            }
            Movt {
                rd: d(rd),
                imm16: *imm16,
            }
        }
        MovtSym { rd, symbol, addend } => {
            if d(rd) != u(rd) {
                return None;
            }
            MovtSym {
                rd: d(rd),
                symbol: symbol.clone(),
                addend: *addend,
            }
        }
        Mul { rd, rn, rm } => Mul {
            rd: d(rd),
            rn: u(rn),
            rm: u(rm),
        },
        Sdiv { rd, rn, rm } => Sdiv {
            rd: d(rd),
            rn: u(rn),
            rm: u(rm),
        },
        Udiv { rd, rn, rm } => Udiv {
            rd: d(rd),
            rn: u(rn),
            rm: u(rm),
        },
        LslReg { rd, rn, rm } => LslReg {
            rd: d(rd),
            rn: u(rn),
            rm: u(rm),
        },
        LsrReg { rd, rn, rm } => LsrReg {
            rd: d(rd),
            rn: u(rn),
            rm: u(rm),
        },
        AsrReg { rd, rn, rm } => AsrReg {
            rd: d(rd),
            rn: u(rn),
            rm: u(rm),
        },
        RorReg { rd, rn, rm } => RorReg {
            rd: d(rd),
            rn: u(rn),
            rm: u(rm),
        },
        Umull { rdlo, rdhi, rn, rm } => Umull {
            rdlo: d(rdlo),
            rdhi: d(rdhi),
            rn: u(rn),
            rm: u(rm),
        },
        Mls { rd, rn, rm, ra } => Mls {
            rd: d(rd),
            rn: u(rn),
            rm: u(rm),
            ra: u(ra),
        },
        Mla { rd, rn, rm, ra } => Mla {
            rd: d(rd),
            rn: u(rn),
            rm: u(rm),
            ra: u(ra),
        },
        Lsl { rd, rn, shift } => Lsl {
            rd: d(rd),
            rn: u(rn),
            shift: *shift,
        },
        Lsr { rd, rn, shift } => Lsr {
            rd: d(rd),
            rn: u(rn),
            shift: *shift,
        },
        Asr { rd, rn, shift } => Asr {
            rd: d(rd),
            rn: u(rn),
            shift: *shift,
        },
        Ror { rd, rn, shift } => Ror {
            rd: d(rd),
            rn: u(rn),
            shift: *shift,
        },
        Clz { rd, rm } => Clz {
            rd: d(rd),
            rm: u(rm),
        },
        Rbit { rd, rm } => Rbit {
            rd: d(rd),
            rm: u(rm),
        },
        Popcnt { rd, rm } => Popcnt {
            rd: d(rd),
            rm: u(rm),
        },
        Sxtb { rd, rm } => Sxtb {
            rd: d(rd),
            rm: u(rm),
        },
        Sxth { rd, rm } => Sxth {
            rd: d(rd),
            rm: u(rm),
        },
        Uxtb { rd, rm } => Uxtb {
            rd: d(rd),
            rm: u(rm),
        },
        Uxth { rd, rm } => Uxth {
            rd: d(rd),
            rm: u(rm),
        },
        Cmp { rn, op2 } => Cmp {
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        Cmn { rn, op2 } => Cmn {
            rn: u(rn),
            op2: op2_map(op2, use_map),
        },
        SetCond { rd, cond } => SetCond {
            rd: d(rd),
            cond: *cond,
        },
        // RMW: rd preserved on the false branch — def and use of one field.
        SelectMove { rd, rm, cond } => {
            if d(rd) != u(rd) {
                return None;
            }
            SelectMove {
                rd: d(rd),
                rm: u(rm),
                cond: *cond,
            }
        }
        Select {
            rd,
            rval1,
            rval2,
            rcond,
        } => Select {
            rd: d(rd),
            rval1: u(rval1),
            rval2: u(rval2),
            rcond: u(rcond),
        },
        Ldr { rd, addr } => Ldr {
            rd: d(rd),
            addr: addr_map(addr, use_map),
        },
        Ldrb { rd, addr } => Ldrb {
            rd: d(rd),
            addr: addr_map(addr, use_map),
        },
        Ldrsb { rd, addr } => Ldrsb {
            rd: d(rd),
            addr: addr_map(addr, use_map),
        },
        Ldrh { rd, addr } => Ldrh {
            rd: d(rd),
            addr: addr_map(addr, use_map),
        },
        Ldrsh { rd, addr } => Ldrsh {
            rd: d(rd),
            addr: addr_map(addr, use_map),
        },
        Str { rd, addr } => Str {
            rd: u(rd),
            addr: addr_map(addr, use_map),
        },
        Strb { rd, addr } => Strb {
            rd: u(rd),
            addr: addr_map(addr, use_map),
        },
        Strh { rd, addr } => Strh {
            rd: u(rd),
            addr: addr_map(addr, use_map),
        },
        Pop { regs } => Pop {
            regs: regs.iter().map(d).collect(),
        },
        Push { regs } => Push {
            regs: regs.iter().map(u).collect(),
        },
        Nop => Nop,
        Udf { imm } => Udf { imm: *imm },
        _ => return None,
    })
}

/// Apply a value-range colouring to a straight-line segment — VCR-RA-001 step
/// 3a's rewrite. `assignment` maps each vreg id (the numbering
/// [`straight_line_value_ranges`] produces — recomputed here with the identical
/// replay, so the ids cannot drift) to the physical register its colour
/// resolves to. Every register occurrence is rewritten simultaneously: uses
/// through the open range at that instruction, defs through the range born
/// there.
///
/// Returns `None` (declines, never a wrong answer) if the segment is not
/// straight-line / fully modeled, a range has no assignment, or an RMW op's
/// old and new ranges were assigned different registers (see [`rewrite_op`]).
/// Pure function — the flag-gated re-allocation pass is its only intended
/// caller.
pub fn apply_range_coloring(
    instrs: &[ArmInstruction],
    assignment: &BTreeMap<usize, Reg>,
) -> Option<Vec<ArmInstruction>> {
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new(); // reg → open vreg id
    let mut next_vreg = 0usize;
    let mut out = Vec::with_capacity(instrs.len());
    for ins in instrs {
        if !is_straight_line(&ins.op) {
            return None;
        }
        let eff = reg_effect(&ins.op)?;
        // Uses resolve through the range OPEN at this instruction (an unseen
        // register is a segment input: open its range now, same as the
        // analysis replay).
        let mut use_map: BTreeMap<Reg, Reg> = BTreeMap::new();
        for r in &eff.uses {
            let vreg = *current.entry(*r).or_insert_with(|| {
                let v = next_vreg;
                next_vreg += 1;
                v
            });
            use_map.insert(*r, *assignment.get(&vreg)?);
        }
        // Defs open new ranges.
        let mut def_map: BTreeMap<Reg, Reg> = BTreeMap::new();
        for r in &eff.defs {
            let vreg = next_vreg;
            next_vreg += 1;
            current.insert(*r, vreg);
            def_map.insert(*r, *assignment.get(&vreg)?);
        }
        out.push(ArmInstruction {
            op: rewrite_op(&ins.op, &use_map, &def_map)?,
            source_line: ins.source_line,
        });
    }
    Some(out)
}

/// Why [`validate_segment_rewrite`] rejected an `(original, rewritten)` pair.
/// Structured so a reject is diagnosable, not just a boolean.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RewriteViolation {
    /// Different instruction counts — not a renames-only rewrite, outside the
    /// validated class.
    LengthMismatch { orig: usize, rewritten: usize },
    /// Instruction `index` is outside the modeled class (no [`reg_effect`], or
    /// not straight-line) in either segment. A decline, never a guess.
    Unmodeled { index: usize },
    /// Instruction `index` has a different opcode shape in the two segments
    /// (opcode, immediates, conditions, shift kinds, symbol, or register-list
    /// length differ) — the lockstep correspondence does not hold.
    ShapeMismatch { index: usize },
    /// At instruction `index`, a definition overwrites a register that a
    /// downstream equation needs under a DIFFERENT pairing: the original's
    /// value in `orig` can no longer be shown equal to the rewritten's value
    /// in `rewritten`.
    DefClobbersEquation {
        index: usize,
        orig: Reg,
        rewritten: Reg,
    },
    /// An equation survived to segment entry without being identity: the
    /// rewritten code expects an input in `rewritten` where the original (and
    /// the pass's input-pinning contract) delivers it in `orig`.
    EntryNotIdentity { orig: Reg, rewritten: Reg },
}

/// `op` with every register operand replaced by `R0` — its register-erased
/// *shape*. Two instructions correspond under a renames-only rewrite iff their
/// shapes are equal: same opcode, same immediates/conditions/shifts/symbols,
/// same register-list lengths, same addressing-mode form. `None` for ops
/// [`rewrite_op`] does not model.
fn op_shape(op: &ArmOp) -> Option<ArmOp> {
    use Reg::*;
    let wipe: BTreeMap<Reg, Reg> = [
        R0, R1, R2, R3, R4, R5, R6, R7, R8, R9, R10, R11, R12, SP, LR, PC,
    ]
    .into_iter()
    .map(|r| (r, R0))
    .collect();
    // The RMW agreement check inside rewrite_op is trivially satisfied (both
    // maps send everything to R0), so this declines only on unmodeled ops.
    rewrite_op(op, &wipe, &wipe)
}

/// Backward-dataflow translation validator over an `(original, rewritten)`
/// straight-line segment pair — VCR-RA-003 v1 (#242), the Rideau/Leroy CC'10
/// architecture adapted to synth's phys-to-phys, renames-only rewrite class.
///
/// Instead of trusting the re-allocation pass (colourer + rewrite), this
/// independently PROVES the rewrite preserves the original's dataflow, by
/// walking both segments backward in lockstep maintaining a set of
/// **equations** `orig_reg ~ rewritten_reg`: "at this program point, for the
/// downstream code to behave identically, the rewritten execution's value in
/// `rewritten_reg` must equal the original execution's value in `orig_reg`."
///
/// - **Exit seed:** for every register the original segment *writes* (the
///   per-register last-written set), require `r ~ r` — the pass's live-out
///   pinning contract (later segments read live-outs from their original
///   registers). One refinement, because the seed models the segment's exit
///   INTERFACE: when the segment ends in a function return (`pop {..., pc}`),
///   the AAPCS caller-saved scratch registers `R2/R3/R12/LR` are dead-out by
///   calling convention (synth's own callers never read them after a call),
///   so they are not seeded — `R0`/`R1` (result registers), the callee-saved
///   set (re-defined by the `pop` itself from identical memory), and `SP`
///   remain seeded. Without this refinement the validator rejects
///   contextually-sound whole-leaf-function rewrites that recycle a dead
///   scratch register's exit slot (the flight_seam_flat filter shape).
///   Registers the original never writes hold their entry values in the
///   original; the rewritten side is NOT checked for clobbers of such
///   pass-through registers — see the honest-bound note below.
/// - **Defs (backward step):** the instruction pair's definitions correspond
///   positionally (`d_o[k] ~ d_r[k]`, guaranteed meaningful by the shape
///   check). A positional pair present in the equation set is *discharged* by
///   this instruction — given its uses agree, both sides compute the same
///   function (same shape), so the defined values agree. Any OTHER equation
///   touching a defined register (original side or rewritten side) can no
///   longer be established by code above this point → violation.
/// - **Uses (backward step):** add the positional use equations
///   `u_o[k] ~ u_r[k]` — **unconditionally**, even when the instruction's
///   register result is downstream-dead. This is deliberately stronger than
///   the minimal liveness refinement: flags (`Cmp`/`Adds`/... feed `SetCond`/
///   `SelectMove`, invisible to `reg_effect`) and memory (`Str*` data +
///   addresses, `Ldr*` addresses) stay correct because every operand that
///   feeds them is constrained equal; and the pass renames every use
///   consistently anyway, so the extra strength costs no completeness on real
///   pass output (criterion: <5% validator-attributable declines; current
///   truth on the fixtures is 0).
/// - **Entry check:** every surviving equation must be identity `r ~ r` —
///   inputs arrive in their original registers (the pass's input pinning).
///
/// RMW ops (`Movt`/`MovtSym`/`SelectMove`) need no special case: `reg_effect`
/// lists `rd` in both `defs` and `uses`, so the backward step discharges the
/// def pairing and immediately re-imposes the use pairing on the *prior*
/// value of the same field — which in concrete syntax is necessarily the same
/// register on each side.
///
/// **Honest v1 bound** (matches the pass's own cross-segment contract, which
/// pins only registers the original holds at exit): a rewritten-side write to
/// a register the original segment never defines (clobbering a pass-through
/// value) is accepted when that write is segment-internally dead. Closing
/// this requires cross-segment liveness (step 5) for both the pass and the
/// validator. Everything else in the renames-only class — wrong renames, def
/// redirects, live clobbers, swapped destinations, RMW splits — is rejected.
pub fn validate_segment_rewrite(
    orig: &[ArmInstruction],
    rewritten: &[ArmInstruction],
) -> Result<(), RewriteViolation> {
    if orig.len() != rewritten.len() {
        return Err(RewriteViolation::LengthMismatch {
            orig: orig.len(),
            rewritten: rewritten.len(),
        });
    }

    // Pass 1 (forward): model + shape-check every instruction pair.
    let mut effects: Vec<(RegEffect, RegEffect)> = Vec::with_capacity(orig.len());
    for (i, (o, r)) in orig.iter().zip(rewritten).enumerate() {
        if !is_straight_line(&o.op) || !is_straight_line(&r.op) {
            return Err(RewriteViolation::Unmodeled { index: i });
        }
        let (Some(eo), Some(er)) = (reg_effect(&o.op), reg_effect(&r.op)) else {
            return Err(RewriteViolation::Unmodeled { index: i });
        };
        let (Some(so), Some(sr)) = (op_shape(&o.op), op_shape(&r.op)) else {
            return Err(RewriteViolation::Unmodeled { index: i });
        };
        // Equal shapes imply equal def/use arity; the explicit length check is
        // a belt-and-braces guard for the positional zips below.
        if so != sr || eo.defs.len() != er.defs.len() || eo.uses.len() != er.uses.len() {
            return Err(RewriteViolation::ShapeMismatch { index: i });
        }
        effects.push((eo, er));
    }

    // Exit seed: identity equations for the original's written registers.
    // At a function return (`pop {..., pc}` as the final instruction) the
    // AAPCS caller-saved scratch registers are dead-out by convention and
    // are exempted; everywhere else every written register is conservatively
    // treated as a live-out candidate.
    let ends_in_return = matches!(
        orig.last().map(|i| &i.op),
        Some(ArmOp::Pop { regs }) if regs.contains(&Reg::PC)
    );
    let aapcs_dead_at_return = [Reg::R2, Reg::R3, Reg::R12, Reg::LR];
    let mut eqs: BTreeSet<(Reg, Reg)> = effects
        .iter()
        .flat_map(|(eo, _)| eo.defs.iter())
        .filter(|r| !(ends_in_return && aapcs_dead_at_return.contains(r)))
        .map(|r| (*r, *r))
        .collect();

    // Backward walk.
    for (i, (eo, er)) in effects.iter().enumerate().rev() {
        let pairs: BTreeSet<(Reg, Reg)> = eo
            .defs
            .iter()
            .copied()
            .zip(er.defs.iter().copied())
            .collect();
        let defs_o: BTreeSet<Reg> = eo.defs.iter().copied().collect();
        let defs_r: BTreeSet<Reg> = er.defs.iter().copied().collect();
        let mut above: BTreeSet<(Reg, Reg)> = BTreeSet::new();
        for eq in &eqs {
            if !defs_o.contains(&eq.0) && !defs_r.contains(&eq.1) {
                above.insert(*eq); // untouched: must already hold above
            } else if !pairs.contains(eq) {
                // A defined register appears under a different pairing: the
                // equation cannot be established by any code above this def.
                return Err(RewriteViolation::DefClobbersEquation {
                    index: i,
                    orig: eq.0,
                    rewritten: eq.1,
                });
            }
            // else: positionally discharged by this instruction (its uses are
            // constrained below, so both sides compute the same value).
        }
        for (uo, ur) in eo.uses.iter().zip(er.uses.iter()) {
            above.insert((*uo, *ur));
        }
        eqs = above;
    }

    // Entry: inputs arrive in their original registers.
    for (o, r) in &eqs {
        if o != r {
            return Err(RewriteViolation::EntryNotIdentity {
                orig: *o,
                rewritten: *r,
            });
        }
    }
    Ok(())
}

/// What [`reallocate_function`] did, for the flag-gated measurement pass.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ReallocStats {
    /// Straight-line segments examined.
    pub segments: usize,
    /// Segments actually rewritten by a re-allocation.
    pub reallocated: usize,
    /// Segments left untouched (unmodeled op, RMW constraint, no assignment).
    pub declined: usize,
    /// Segments whose ranges did not colour within the pool (need step-4 spill
    /// insertion — passed through untouched for now).
    pub needs_spill: usize,
    /// Segments whose rewrite the backward-dataflow validator (VCR-RA-003)
    /// REJECTED — counted inside `declined` as well, but tracked separately
    /// because a nonzero value means the pass produced a rewrite it cannot
    /// justify (a pass bug caught before it reached codegen). Must be 0 on
    /// the frozen fixtures; the roadmap kill-criterion re-evaluates the
    /// validator if attributable declines ever exceed ~5% of segments.
    pub validator_rejects: usize,
}

/// Re-allocate every maximal straight-line segment of a function over `pool`
/// (VCR-RA-001 step 3a, the consequential pass — flag-gated by the caller).
///
/// Per segment: value ranges → range interference → costed colouring → the
/// simultaneous rewrite. Conservative pinning makes each segment independently
/// sound with NO cross-segment liveness needed:
///   - every range with `def == 0` (segment inputs — conservatively including
///     instruction-0 defs, indistinguishable in the range encoding) is pinned
///     to its original register, so values produced by earlier segments are
///     read where they were left;
///   - per physical register, the LAST range opened (the one holding the
///     register's value at segment exit) is pinned to its original register,
///     so later segments find live-outs where they expect them — whether or
///     not they actually read them (cross-segment liveness is step 5's
///     refinement, not assumed here);
///   - ranges on registers outside `pool` (reserved R9–R12, SP) are identity-
///     assigned and never enter the colouring (their registers cannot collide
///     with pool colours).
///
/// Only segment-internal values reshuffle — exactly where the spurious spills
/// and duplicate materializations live. A segment that cannot be re-allocated
/// (unmodeled op, spill needed, RMW constraint) passes through untouched;
/// control-flow instructions always pass through verbatim, so labels, branch
/// targets, and instruction counts are unchanged.
///
/// Dead callee-saved-save elimination (gale, #209 v0.11.36): after
/// re-allocation packs a small function's body into low registers, the
/// prologue still saves callee-saved registers nothing uses — on the M4,
/// `push {r4-r8,lr}` + `ldmia {r4-r8,pc}` is ~12 cycles of pure overhead on a
/// 37-cycle leaf. Shrink the prologue `Push {.., LR}` / epilogue
/// `Pop {.., PC}` register lists to the callee-saved registers (R4–R8) the
/// body actually touches, padded to an EVEN total count so the 8-byte AAPCS
/// SP alignment the original even-count push established is preserved
/// everywhere.
///
/// Deliberately bounded v1 scope — returns `None` (caller keeps the original)
/// unless ALL hold:
///   - exactly one prologue `Push` containing `LR`; every `Pop` contains `PC`
///     (epilogues) and shares the same shrink;
///   - the body never touches SP (no `[sp]`-relative access, no frame
///     `add/sub sp` — shrinking the push shifts SP-relative offsets);
///   - no calls (`Bl`/`Blx`/`Call`/`CallIndirect`) — leaf only, so the AAPCS
///     call-boundary alignment question never arises beyond the even-count
///     padding;
///   - every instruction is either register-modeled (`reg_effect`) or pure
///     label control flow with no register operands (`BrTable` reads an index
///     register invisibly to `reg_effect`, so it declines; `Bx {LR}` is an
///     allowed return).
pub fn shrink_callee_saved_saves(instrs: &[ArmInstruction]) -> Option<Vec<ArmInstruction>> {
    use ArmOp::*;
    const CALLEE_SAVED: [Reg; 5] = [Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8];

    // Pass 1: classify. Find the single LR-push and the PC-pops; collect the
    // callee-saved registers the rest of the body touches; decline on
    // anything outside the modeled scope.
    let mut prologue: Option<usize> = None;
    let mut epilogues: Vec<usize> = Vec::new();
    let mut used: BTreeSet<Reg> = BTreeSet::new();
    for (i, ins) in instrs.iter().enumerate() {
        match &ins.op {
            Push { regs } => {
                if !regs.contains(&Reg::LR) || prologue.is_some() {
                    return None; // mid-body push or second prologue
                }
                prologue = Some(i);
            }
            Pop { regs } => {
                if !regs.contains(&Reg::PC) {
                    return None; // mid-body pop
                }
                epilogues.push(i);
            }
            // Pure label control flow with no register operands.
            Label { .. }
            | B { .. }
            | BOffset { .. }
            | BCondOffset { .. }
            | Bhs { .. }
            | Blo { .. }
            | Bcc { .. } => {}
            Bx { rm } if *rm == Reg::LR => {}
            op => {
                let e = reg_effect(op)?; // unmodeled (BrTable/calls/...) → decline
                for r in e.defs.iter().chain(e.uses.iter()) {
                    if *r == Reg::SP {
                        return None; // frame/SP-relative function — offsets would shift
                    }
                    if CALLEE_SAVED.contains(r) {
                        used.insert(*r);
                    }
                }
                // SP hides inside addressing modes too.
                if let Ldr { addr, .. }
                | Ldrb { addr, .. }
                | Ldrsb { addr, .. }
                | Ldrh { addr, .. }
                | Ldrsh { addr, .. }
                | Str { addr, .. }
                | Strb { addr, .. }
                | Strh { addr, .. } = op
                    && (addr.base == Reg::SP || addr.offset_reg == Some(Reg::SP))
                {
                    return None;
                }
            }
        }
    }
    let prologue = prologue?;
    if epilogues.is_empty() {
        return None;
    }

    // New save list: used callee-saved registers, padded with the lowest
    // unused one if the total (incl. LR/PC) would be odd.
    let mut saves: Vec<Reg> = CALLEE_SAVED
        .iter()
        .filter(|r| used.contains(r))
        .copied()
        .collect();
    if !(saves.len() + 1).is_multiple_of(2)
        && let Some(pad) = CALLEE_SAVED.iter().find(|r| !used.contains(r))
    {
        saves.push(*pad);
        saves.sort();
    }
    // Nothing to shrink?
    if saves.len() == CALLEE_SAVED.len() {
        return None;
    }

    let mut out = instrs.to_vec();
    let mut push_regs = saves.clone();
    push_regs.push(Reg::LR);
    out[prologue].op = Push { regs: push_regs };
    for e in epilogues {
        let mut pop_regs = saves.clone();
        pop_regs.push(Reg::PC);
        out[e].op = Pop { regs: pop_regs };
    }
    Some(out)
}

/// #490 (epic #242): does this body clobber/read any callee-saved register, so
/// the optimized path must wrap it in a `push {r4-r8,lr}` / `pop {r4-r8,pc}`
/// prologue/epilogue to honour AAPCS?
///
/// This is the **emit-side twin** of [`shrink_callee_saved_saves`]: it reads the
/// exact same per-op classification (the control-flow allowlist + `reg_effect`)
/// as *push-conditions* rather than *decline-conditions*, so the two passes
/// always agree. [`ensure_callee_saved_prologue`] emits a conservative full
/// `push {r4-r8,lr}` when this returns `true`; `shrink_callee_saved_saves` then
/// trims that push to the registers actually touched (or declines, leaving the
/// full push, on frame/call/unmodeled bodies it cannot prove safe).
///
/// **Conservative on `None` (fail-safe).** An op `reg_effect` cannot model
/// (i64-pair pseudo-ops, calls, anything outside the modeled scope) *might* write
/// a callee-saved register, so it forces the push. Under-saving is the exact
/// AAPCS violation #490 fixes; over-saving an unused register is harmless (shrink
/// pads it down, or — on a body shrink declines — it is a few dead bytes). The
/// only load-bearing answer is `false`: a spurious push on a callee-saved-free
/// leaf is permanent (shrink never *removes* a push), so the control-flow
/// allowlist and the cs-intersection test must be exact, mirroring shrink. The
/// decision runs on the **post-range-realloc** body, where low-pressure r4-r8
/// scratch has already been lowered to r0-r3, so only genuine clobbers remain.
pub fn body_uses_callee_saved(instrs: &[ArmInstruction]) -> bool {
    use ArmOp::*;
    const CALLEE_SAVED: [Reg; 5] = [Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8];
    for ins in instrs {
        match &ins.op {
            // Function-boundary markers and pure label control flow carry no
            // callee-saved data effect (mirrors shrink's allowlist exactly).
            Push { .. }
            | Pop { .. }
            | Label { .. }
            | B { .. }
            | BOffset { .. }
            | BCondOffset { .. }
            | Bhs { .. }
            | Blo { .. }
            | Bcc { .. } => {}
            Bx { rm } if *rm == Reg::LR => {}
            op => match reg_effect(op) {
                Some(e) => {
                    if e.defs
                        .iter()
                        .chain(e.uses.iter())
                        .any(|r| CALLEE_SAVED.contains(r))
                    {
                        return true;
                    }
                }
                // Unmodeled op → assume it may touch a callee-saved register.
                None => return true,
            },
        }
    }
    false
}

/// #490 (epic #242): give the optimized path the callee-saved prologue/epilogue
/// it is missing. The optimized selector uses r4-r8 as scratch / promoted locals
/// but emits no `push`/`pop`, so a caller's r4-r8 are silently clobbered — a
/// systemic AAPCS violation. When the (post-realloc) body genuinely touches a
/// callee-saved register, wrap it in a conservative full `push {r4-r8,lr}` /
/// `pop {r4-r8,pc}`; [`shrink_callee_saved_saves`] (run next) trims that to the
/// registers actually used, or declines and leaves the full save on a
/// frame/call/unmodeled body it cannot prove safe.
///
/// No-op when a prologue already exists (the direct selector emits its own
/// `push {…,lr}`) or the body is callee-saved-free (e.g. a pure-r0-r3 leaf —
/// left byte-identical, which is load-bearing: an added push could never be
/// removed later). The push is inserted at index 0, landing before any
/// `sub sp,#frame` the optimized path reserved; each `bx lr` becomes
/// `pop {…,pc}`, landing after the matching `add sp,#frame`.
pub fn ensure_callee_saved_prologue(instrs: &[ArmInstruction]) -> Vec<ArmInstruction> {
    use ArmOp::*;
    // Already has a prologue (direct path) → leave it for shrink to size.
    if instrs
        .iter()
        .any(|i| matches!(&i.op, Push { regs } if regs.contains(&Reg::LR)))
    {
        return instrs.to_vec();
    }
    if !body_uses_callee_saved(instrs) {
        return instrs.to_vec();
    }
    let mut out = Vec::with_capacity(instrs.len() + 1);
    out.push(ArmInstruction {
        op: Push {
            regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::LR],
        },
        source_line: None,
    });
    for ins in instrs {
        if matches!(&ins.op, Bx { rm } if *rm == Reg::LR) {
            out.push(ArmInstruction {
                op: Pop {
                    regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC],
                },
                source_line: ins.source_line,
            });
        } else {
            out.push(ins.clone());
        }
    }
    out
}

/// VCR-RA-002 (#390, epic #242): eliminate a provably-dead stack frame.
///
/// `compute_local_layout` reserves a frame slot — materialized as
/// `sub sp,#N` (prologue) / `add sp,#N` (epilogue) — for every non-param wasm
/// local it sees. Local promotion (v0.14.0) then homes eligible i32 locals in a
/// register instead. When promotion homes ALL of a function's locals and the
/// function neither spills, calls, nor touches i64 / stack-passed params, those
/// reserved frame bytes are never accessed: the `sub`/`add sp` pair is pure
/// overhead (~2-3 cyc on a small leaf), AND — because it writes SP —
/// [`shrink_callee_saved_saves`] declines on it (that pass bails on any SP
/// def/use, since a shrunk push would shift SP-relative offsets). Removing the
/// dead frame both saves the two instructions and restores the SP-untouched
/// precondition the shrink pass needs, so the two passes compose.
///
/// SOUNDNESS (safe-by-construction): fire ONLY when NO instruction in the body
/// reads or writes SP except the matched frame `sub`/`add` and the prologue
/// `Push` / epilogue `Pop` (which adjust SP symmetrically but never index the
/// frame region). For wasm locals that guard IS exact deadness — locals are not
/// addressable, so only `LocalGet/Set/Tee` (lowered to a promoted register or
/// `[sp,#off]`) touch them, and every OTHER SP consumer — register spills, #204
/// param-backing, the i64 pair-spill area, the #359 outgoing-arg region, and
/// incoming stack-passed params — manifests as an `[sp,#off]` access this guard
/// sees. Any such access (or any unmodeled op whose SP effect `reg_effect` can't
/// confirm absent) returns `None` and the bytes are unchanged. When it fires,
/// the removed region was provably unreferenced: SP stays balanced and no
/// surviving offset shifts. Removal-only — no instruction is added, rewritten,
/// or reordered, so the only count change is the dropped `sub`/`add` pair.
///
/// Bounded v1 scope (mirrors [`shrink_callee_saved_saves`]) — `None` unless:
///   - exactly one frame `sub sp,sp,#N`; every `add sp,sp,#M` restores the same
///     `N` (balanced epilogues; a mismatched `add sp` is some other SP
///     arithmetic → decline);
///   - no other SP def/use or `[sp]`-relative addressing anywhere in the body;
///   - every instruction is register-modeled (`reg_effect`) or pure label
///     control flow (`Label`/`B*`/`Bx {LR}`).
pub fn elide_dead_frame(instrs: &[ArmInstruction]) -> Option<Vec<ArmInstruction>> {
    use ArmOp::*;

    // Pass 1: locate the single frame allocation and its matching deallocs, and
    // verify nothing else touches SP.
    let mut frame_sub: Option<(usize, i32)> = None;
    let mut frame_adds: Vec<usize> = Vec::new();
    for (i, ins) in instrs.iter().enumerate() {
        match &ins.op {
            Sub {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(n),
            } => {
                if frame_sub.is_some() {
                    return None; // more than one frame allocation — unmodeled
                }
                frame_sub = Some((i, *n));
            }
            Add {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(_),
            } => frame_adds.push(i),
            _ => {}
        }
    }
    let (sub_idx, frame_n) = frame_sub?;
    if frame_adds.is_empty() {
        return None;
    }
    // Every frame dealloc must restore exactly `frame_n` (balanced); a different
    // immediate means this `add sp` is not the frame's counterpart → decline.
    for &ai in &frame_adds {
        if let Add {
            op2: Operand2::Imm(n),
            ..
        } = &instrs[ai].op
            && *n != frame_n
        {
            return None;
        }
    }

    // Pass 2: prove the frame is dead — no SP access outside the frame sub/adds
    // and the push/pop.
    for (i, ins) in instrs.iter().enumerate() {
        if i == sub_idx || frame_adds.contains(&i) {
            continue;
        }
        match &ins.op {
            // Push/Pop move SP but never index the frame region — allowed.
            // Pure label control flow has no register operands.
            Push { .. }
            | Pop { .. }
            | Label { .. }
            | B { .. }
            | BOffset { .. }
            | BCondOffset { .. }
            | Bhs { .. }
            | Blo { .. }
            | Bcc { .. } => {}
            Bx { rm } if *rm == Reg::LR => {}
            op => {
                // Unmodeled op (call/BrTable/i64-pair/...): cannot prove SP-free.
                let e = reg_effect(op)?;
                if e.defs.iter().chain(e.uses.iter()).any(|r| *r == Reg::SP) {
                    return None;
                }
                // SP hides inside addressing modes too.
                if let Ldr { addr, .. }
                | Ldrb { addr, .. }
                | Ldrsb { addr, .. }
                | Ldrh { addr, .. }
                | Ldrsh { addr, .. }
                | Str { addr, .. }
                | Strb { addr, .. }
                | Strh { addr, .. } = op
                    && (addr.base == Reg::SP || addr.offset_reg == Some(Reg::SP))
                {
                    return None;
                }
            }
        }
    }

    // Dead frame confirmed: drop the `sub sp` and every matching `add sp`.
    let drop: BTreeSet<usize> = std::iter::once(sub_idx)
        .chain(frame_adds.iter().copied())
        .collect();
    Some(
        instrs
            .iter()
            .enumerate()
            .filter(|(i, _)| !drop.contains(i))
            .map(|(_, ins)| ins.clone())
            .collect(),
    )
}

/// Defense-in-depth: before accepting a segment's rewrite, every interference
/// edge is re-checked against the final assignment (independent of the
/// colourer), mirroring `verify_allocation`.
pub fn reallocate_function(
    instrs: &[ArmInstruction],
    pool: &[Reg],
) -> (Vec<ArmInstruction>, ReallocStats) {
    let mut out: Vec<ArmInstruction> = Vec::with_capacity(instrs.len());
    let mut stats = ReallocStats::default();
    let mut seg: Vec<ArmInstruction> = Vec::new();
    let flush =
        |seg: &mut Vec<ArmInstruction>, out: &mut Vec<ArmInstruction>, stats: &mut ReallocStats| {
            if seg.is_empty() {
                return;
            }
            stats.segments += 1;
            match try_reallocate_segment(seg, pool) {
                SegmentOutcome::Rewritten(new) => {
                    stats.reallocated += 1;
                    out.extend(new);
                }
                SegmentOutcome::NeedsSpill => {
                    stats.needs_spill += 1;
                    out.append(seg);
                }
                SegmentOutcome::Declined => {
                    stats.declined += 1;
                    out.append(seg);
                }
                SegmentOutcome::ValidatorRejected => {
                    // The colourer + edge-recheck accepted a rewrite the
                    // backward-dataflow validator could not justify: keep the
                    // original bytes (safe) and surface the event in stats —
                    // a nonzero count is a pass bug, not a validator feature.
                    stats.declined += 1;
                    stats.validator_rejects += 1;
                    out.append(seg);
                }
            }
            seg.clear();
        };
    for ins in instrs {
        if is_straight_line(&ins.op) && reg_effect(&ins.op).is_some() {
            seg.push(ins.clone());
        } else {
            flush(&mut seg, &mut out, &mut stats);
            out.push(ins.clone());
        }
    }
    flush(&mut seg, &mut out, &mut stats);
    (out, stats)
}

enum SegmentOutcome {
    Rewritten(Vec<ArmInstruction>),
    NeedsSpill,
    Declined,
    /// The rewrite was produced but the VCR-RA-003 validator rejected it.
    ValidatorRejected,
}

fn try_reallocate_segment(seg: &[ArmInstruction], pool: &[Reg]) -> SegmentOutcome {
    let Some(ranges) = straight_line_value_ranges(seg) else {
        return SegmentOutcome::Declined;
    };
    if ranges.is_empty() {
        return SegmentOutcome::Declined;
    }
    let pool_index: BTreeMap<Reg, usize> = pool.iter().enumerate().map(|(i, r)| (*r, i)).collect();
    let adj = range_interference(&ranges);

    // Pins: inputs (def == 0) and per-register last-opened ranges (live-outs)
    // keep their original register. Reserved-register ranges are identity-
    // assigned outside the colouring.
    let mut last_opened: BTreeMap<Reg, usize> = BTreeMap::new();
    for r in &ranges {
        last_opened.insert(r.reg, r.vreg); // ranges are in creation order
    }
    let mut pins: BTreeMap<usize, usize> = BTreeMap::new();
    let mut assignment: BTreeMap<usize, Reg> = BTreeMap::new();
    let mut pool_nodes: BTreeSet<usize> = BTreeSet::new();
    for r in &ranges {
        match pool_index.get(&r.reg) {
            None => {
                // Reserved register: identity, never coloured.
                assignment.insert(r.vreg, r.reg);
            }
            Some(&idx) => {
                pool_nodes.insert(r.vreg);
                if r.def == 0 || last_opened.get(&r.reg) == Some(&r.vreg) {
                    pins.insert(r.vreg, idx);
                }
            }
        }
    }

    // Colouring input: pool ranges only (reserved registers cannot collide
    // with pool colours, so their edges are irrelevant to the colouring).
    let pool_adj: BTreeMap<usize, BTreeSet<usize>> = adj
        .iter()
        .filter(|(n, _)| pool_nodes.contains(n))
        .map(|(n, nbrs)| (*n, nbrs.intersection(&pool_nodes).copied().collect()))
        .collect();

    // Spill cost: occurrence count per range (1 per def + 1 per use event),
    // replayed with the same numbering.
    let mut costs: BTreeMap<usize, usize> = BTreeMap::new();
    {
        let mut current: BTreeMap<Reg, usize> = BTreeMap::new();
        let mut next = 0usize;
        for ins in seg {
            let Some(e) = reg_effect(&ins.op) else {
                return SegmentOutcome::Declined;
            };
            for u in &e.uses {
                let v = *current.entry(*u).or_insert_with(|| {
                    let v = next;
                    next += 1;
                    v
                });
                *costs.entry(v).or_insert(0) += 1;
            }
            for d in &e.defs {
                current.insert(*d, next);
                *costs.entry(next).or_insert(0) += 1;
                next += 1;
            }
        }
    }

    let (coloring, spilled) = color_ranges(&pool_adj, pool.len(), &pins, &costs);
    if !spilled.is_empty() {
        return SegmentOutcome::NeedsSpill;
    }
    for (v, c) in &coloring {
        assignment.insert(*v, pool[*c]);
    }

    // Defense-in-depth: re-check every interference edge against the final
    // assignment, independently of the colourer (cf. verify_allocation).
    for (n, nbrs) in &adj {
        for m in nbrs {
            match (assignment.get(n), assignment.get(m)) {
                (Some(a), Some(b)) if a != b => {}
                _ => return SegmentOutcome::Declined,
            }
        }
    }

    match apply_range_coloring(seg, &assignment) {
        // VCR-RA-003: the rewrite is accepted only if the backward-dataflow
        // translation validator can independently prove it preserves the
        // original segment's dataflow (exit live-outs + entry inputs pinned).
        // The edge-recheck above stays as defense in depth; this is the
        // acceptance gate the pass cannot bypass.
        Some(new) => match validate_segment_rewrite(seg, &new) {
            Ok(()) => SegmentOutcome::Rewritten(new),
            Err(v) => {
                if std::env::var("SYNTH_VALIDATOR_DEBUG").is_ok() {
                    eprintln!("[validator] REJECT {v:?}\n  orig: {seg:?}\n  rew:  {new:?}");
                }
                SegmentOutcome::ValidatorRejected
            }
        },
        None => SegmentOutcome::Declined,
    }
}

/// Peak **virtual-register pressure** of a straight-line segment: the maximum
/// number of distinct *values* live on any instruction edge — where a value is a
/// single def-to-last-use range, NOT a reused physical-register name. This is
/// the true register requirement the spurious physical-register interference
/// hides: the greedy selector reuses one physical register for many values, so
/// counting physical registers (the shadow pass's "would spill R1") overstates
/// the need. If this is ≤ the pool size, the segment fits with no spill once
/// virtually allocated. Returns `None` if the segment is not straight-line /
/// fully modeled. A register used before any def is an input, live from the
/// segment start.
pub fn straight_line_peak_pressure(instrs: &[ArmInstruction]) -> Option<usize> {
    let n = instrs.len();
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new(); // reg → live value id
    let mut def_at: Vec<usize> = Vec::new(); // value id → def edge (0 for inputs)
    let mut last_use: Vec<usize> = Vec::new(); // value id → last-use index
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) {
            return None;
        }
        let eff = reg_effect(&ins.op)?;
        for u in &eff.uses {
            let vid = *current.entry(*u).or_insert_with(|| {
                def_at.push(0); // input: live from the segment start
                last_use.push(0);
                def_at.len() - 1
            });
            last_use[vid] = i;
        }
        for d in &eff.defs {
            def_at.push(i);
            last_use.push(i); // dead-on-arrival until a later use extends it
            current.insert(*d, def_at.len() - 1);
        }
    }
    // A value used after its def occupies a register on edges [def, last_use).
    let mut delta = vec![0i32; n + 1];
    for vid in 0..def_at.len() {
        let (d, l) = (def_at[vid], last_use[vid]);
        if l > d {
            delta[d] += 1;
            delta[l] -= 1;
        }
    }
    let (mut cur, mut peak) = (0i32, 0i32);
    for d in delta.iter().take(n) {
        cur += *d;
        peak = peak.max(cur);
    }
    Some(peak as usize)
}

/// Peak virtual-register pressure across a whole (possibly branchy) function:
/// the max [`straight_line_peak_pressure`] over its straight-line segments (a
/// lower bound on the true register need). If ≤ the pool size, no segment forces
/// a spill once virtually allocated — so a physical-register "spill" is spurious.
pub fn function_peak_pressure(instrs: &[ArmInstruction]) -> usize {
    let mut peak = 0;
    let mut seg_start = 0;
    let flush = |start: usize, end: usize, peak: &mut usize| {
        if end > start
            && let Some(p) = straight_line_peak_pressure(&instrs[start..end])
        {
            *peak = (*peak).max(p);
        }
    };
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) || reg_effect(&ins.op).is_none() {
            flush(seg_start, i, &mut peak);
            seg_start = i + 1;
        }
    }
    flush(seg_start, instrs.len(), &mut peak);
    peak
}

fn op2_rename(op2: &Operand2, from: Reg, to: Reg) -> Operand2 {
    let sub = |r: Reg| if r == from { to } else { r };
    match op2 {
        Operand2::Reg(r) => Operand2::Reg(sub(*r)),
        Operand2::RegShift { rm, shift, amount } => Operand2::RegShift {
            rm: sub(*rm),
            shift: *shift,
            amount: *amount,
        },
        Operand2::Imm(v) => Operand2::Imm(*v),
    }
}

fn addr_rename(a: &MemAddr, from: Reg, to: Reg) -> MemAddr {
    let sub = |r: Reg| if r == from { to } else { r };
    MemAddr {
        base: sub(a.base),
        offset: a.offset,
        offset_reg: a.offset_reg.map(sub),
    }
}

/// Rewrite every *use* of `from` to `to` in `op`, leaving definitions untouched.
/// Returns `None` for ops where a use of `from` cannot be rewritten without
/// ambiguity (e.g. a read-modify-write of `from` itself, like `Movt`/`SelectMove`
/// where `from == rd`) — the caller then declines the fold, staying sound.
fn rename_use(op: &ArmOp, from: Reg, to: Reg) -> Option<ArmOp> {
    use ArmOp::*;
    let sub = |r: Reg| if r == from { to } else { r };
    Some(match op {
        Add { rd, rn, op2 } => Add {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Sub { rd, rn, op2 } => Sub {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Adds { rd, rn, op2 } => Adds {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Subs { rd, rn, op2 } => Subs {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Adc { rd, rn, op2 } => Adc {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Sbc { rd, rn, op2 } => Sbc {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        And { rd, rn, op2 } => And {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Orr { rd, rn, op2 } => Orr {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Eor { rd, rn, op2 } => Eor {
            rd: *rd,
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Rsb { rd, rn, imm } => Rsb {
            rd: *rd,
            rn: sub(*rn),
            imm: *imm,
        },
        Mov { rd, op2 } => Mov {
            rd: *rd,
            op2: op2_rename(op2, from, to),
        },
        Mvn { rd, op2 } => Mvn {
            rd: *rd,
            op2: op2_rename(op2, from, to),
        },
        Mul { rd, rn, rm } => Mul {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        Sdiv { rd, rn, rm } => Sdiv {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        Udiv { rd, rn, rm } => Udiv {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        LslReg { rd, rn, rm } => LslReg {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        LsrReg { rd, rn, rm } => LsrReg {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        AsrReg { rd, rn, rm } => AsrReg {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        RorReg { rd, rn, rm } => RorReg {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        Umull { rdlo, rdhi, rn, rm } => Umull {
            rdlo: *rdlo,
            rdhi: *rdhi,
            rn: sub(*rn),
            rm: sub(*rm),
        },
        Mls { rd, rn, rm, ra } => Mls {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
            ra: sub(*ra),
        },
        Mla { rd, rn, rm, ra } => Mla {
            rd: *rd,
            rn: sub(*rn),
            rm: sub(*rm),
            ra: sub(*ra),
        },
        Lsl { rd, rn, shift } => Lsl {
            rd: *rd,
            rn: sub(*rn),
            shift: *shift,
        },
        Lsr { rd, rn, shift } => Lsr {
            rd: *rd,
            rn: sub(*rn),
            shift: *shift,
        },
        Asr { rd, rn, shift } => Asr {
            rd: *rd,
            rn: sub(*rn),
            shift: *shift,
        },
        Ror { rd, rn, shift } => Ror {
            rd: *rd,
            rn: sub(*rn),
            shift: *shift,
        },
        Clz { rd, rm } => Clz {
            rd: *rd,
            rm: sub(*rm),
        },
        Rbit { rd, rm } => Rbit {
            rd: *rd,
            rm: sub(*rm),
        },
        Popcnt { rd, rm } => Popcnt {
            rd: *rd,
            rm: sub(*rm),
        },
        Sxtb { rd, rm } => Sxtb {
            rd: *rd,
            rm: sub(*rm),
        },
        Sxth { rd, rm } => Sxth {
            rd: *rd,
            rm: sub(*rm),
        },
        Uxtb { rd, rm } => Uxtb {
            rd: *rd,
            rm: sub(*rm),
        },
        Uxth { rd, rm } => Uxth {
            rd: *rd,
            rm: sub(*rm),
        },
        Cmp { rn, op2 } => Cmp {
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Cmn { rn, op2 } => Cmn {
            rn: sub(*rn),
            op2: op2_rename(op2, from, to),
        },
        Ldr { rd, addr } => Ldr {
            rd: *rd,
            addr: addr_rename(addr, from, to),
        },
        Ldrb { rd, addr } => Ldrb {
            rd: *rd,
            addr: addr_rename(addr, from, to),
        },
        Ldrsb { rd, addr } => Ldrsb {
            rd: *rd,
            addr: addr_rename(addr, from, to),
        },
        Ldrh { rd, addr } => Ldrh {
            rd: *rd,
            addr: addr_rename(addr, from, to),
        },
        Ldrsh { rd, addr } => Ldrsh {
            rd: *rd,
            addr: addr_rename(addr, from, to),
        },
        Str { rd, addr } => Str {
            rd: sub(*rd),
            addr: addr_rename(addr, from, to),
        },
        Strb { rd, addr } => Strb {
            rd: sub(*rd),
            addr: addr_rename(addr, from, to),
        },
        Strh { rd, addr } => Strh {
            rd: sub(*rd),
            addr: addr_rename(addr, from, to),
        },
        // Read-modify-write of the renamed reg, register lists, or unmodeled ops:
        // cannot rewrite a use of `from` here without ambiguity → decline.
        _ => return None,
    })
}

/// Find the in-segment reads of `rd` that can be safely retargeted to `ra` after
/// dropping a redundant `movw rd, #v` at `def_i` (where `ra` already holds `v`).
/// Safe only if `ra` still holds `v` at every such read AND `rd`'s value is
/// provably local — i.e. `rd` is redefined within `[def_i, seg_end)` so the
/// dropped value never escapes the segment. Returns `None` (decline) otherwise.
fn safe_cse_uses(
    instrs: &[ArmInstruction],
    def_i: usize,
    rd: Reg,
    ra: Reg,
    seg_end: usize,
) -> Option<Vec<usize>> {
    let mut uses = Vec::new();
    let mut ra_holds_v = true;
    for (offset, ins) in instrs[(def_i + 1)..seg_end].iter().enumerate() {
        let j = def_i + 1 + offset;
        let eff = reg_effect(&ins.op)?;
        if eff.uses.contains(&rd) {
            if !ra_holds_v {
                return None; // ra no longer holds v but rd is read → unsafe
            }
            rename_use(&ins.op, rd, ra)?; // the use must be rewritable to ra
            uses.push(j);
        }
        if eff.defs.contains(&ra) {
            ra_holds_v = false;
        }
        if eff.defs.contains(&rd) {
            return Some(uses); // rd redefined → its v dies here → local → safe
        }
    }
    None // rd not redefined in the segment → may be live-out → decline
}

/// Size of the general-purpose allocatable register pool (R0..R8). The
/// optimized ARM path reserves R9/R10/R11 (linmem base / scratch) and R12 (IP,
/// encoder scratch), so nine registers remain for values (#212).
const ALLOCATABLE_POOL: usize = 9;

/// The allocatable pool in preference order (low first, so a retargeted use is
/// less likely to flip a 16-bit Thumb encoding to its 32-bit form).
fn hoist_pool() -> [Reg; ALLOCATABLE_POOL] {
    use Reg::*;
    [R0, R1, R2, R3, R4, R5, R6, R7, R8]
}

/// A constant-materialization *unit* in a straight-line segment: either a single
/// `mov`/`movw` (`len == 1`) or an adjacent `movw rd,#lo ; movt rd,#hi` pair
/// (`len == 2`) that together load `value` into `rd`. Recognizing the 32-bit
/// `movw+movt` pair (PR2, #242) makes the large clamp/flat_flight constants
/// visible to const-CSE — a lone `movw` extractor sees only the low 16 bits.
struct ConstUnit {
    /// Segment-local index of the first instruction of the unit.
    start: usize,
    /// 1 for a single `mov`/`movw`, 2 for a `movw+movt` pair.
    len: usize,
    /// Destination register the constant is materialized into.
    rd: Reg,
    /// The full (reconstructed) 32-bit constant value.
    value: i32,
}

/// The constant-materialization units of a straight-line segment, in order. A
/// `movw rd,#lo` immediately followed by `movt rd,#hi` (same `rd`) is folded
/// into one 32-bit unit; anything else is a single-instruction unit.
fn const_units(seg: &[ArmInstruction]) -> Vec<ConstUnit> {
    let mut out = Vec::new();
    let mut i = 0;
    while i < seg.len() {
        if let Some((rd, lo)) = const_materialization(&seg[i].op) {
            if let ArmOp::Movw {
                rd: wrd,
                imm16: lo16,
            } = &seg[i].op
                && i + 1 < seg.len()
                && let ArmOp::Movt {
                    rd: trd,
                    imm16: hi16,
                } = &seg[i + 1].op
                && trd == wrd
            {
                let full = (*lo16 as u32 | ((*hi16 as u32) << 16)) as i32;
                out.push(ConstUnit {
                    start: i,
                    len: 2,
                    rd: *wrd,
                    value: full,
                });
                i += 2;
                continue;
            }
            out.push(ConstUnit {
                start: i,
                len: 1,
                rd,
                value: lo,
            });
        }
        i += 1;
    }
    out
}

/// Find a pool register that is provably FREE across the closed instruction
/// range `[lo, hi]` of a straight-line segment — i.e. one that can hold a hoisted
/// constant materialized at `lo` and read (for the last time) at `hi` without
/// clobbering any other live value. Sound criterion (forward scan from `lo+1`):
///   - a *use* of the candidate before it is redefined post-`lo` ⇒ the candidate
///     carries a foreign value live across the window ⇒ reject;
///   - a *def* of the candidate at or below `hi` ⇒ the hoisted value would be
///     clobbered before its last use ⇒ reject; a def strictly above `hi` ⇒ the
///     candidate is safely reusable there ⇒ accept (stop scanning).
///
/// `avoid` excludes the destination register(s) already in play and any register
/// pinned by an earlier hoist in the same segment. Returns `None` if none free —
/// the caller then declines the hoist (pressure too high in the window).
fn free_reg_over(
    seg: &[ArmInstruction],
    lo: usize,
    hi: usize,
    avoid: &BTreeSet<Reg>,
) -> Option<Reg> {
    'cand: for &p in hoist_pool().iter() {
        if avoid.contains(&p) {
            continue;
        }
        for (k, ins) in seg.iter().enumerate().skip(lo + 1) {
            // Segment is fully modeled (the caller only processes such segments),
            // so reg_effect is always Some; `?` stays sound if that ever changes.
            let eff = reg_effect(&ins.op)?;
            if eff.uses.contains(&p) {
                continue 'cand;
            }
            if eff.defs.contains(&p) {
                if k <= hi {
                    continue 'cand;
                }
                break;
            }
        }
        return Some(p);
    }
    None
}

/// Const-CSE / rematerialization-avoidance driven by the value-range analysis:
/// where a `movw rd, #v` re-materializes a constant already resident in `ra`,
/// and `ra` provably still holds `v` through every later read of `rd` (until
/// `rd` is redefined within the segment), drop the `movw` and retarget those
/// reads to `ra`. This is the allocator's rematerialization-avoidance applied as
/// a targeted transform — every rewrite is *proven* by liveness.
///
/// SIZE GUARD (#242): this pass operates on already-register-assigned
/// instructions, so it cannot itself spill — but a removal+retarget can still
/// *grow* a function by changing what a later pass or the encoder does. Two
/// concrete ways: (a) the retargeted read keeps a constant resident longer,
/// defeating a downstream immediate-fold that would have absorbed it (the
/// `gust_mix` 90→92 B regression gale measured on `--relocatable`, 2026-06-26);
/// and (b) retargeting a read from a low register to a high one flips a 16-bit
/// Thumb encoding to its 32-bit form (`ldr r0,[r3,#off]` → `ldr r0,[r8,#off]`,
/// +2 B). (a) is structurally eliminated by running this pass LAST, after every
/// immediate-fold (so foldable consts are already gone); (b) is caught here:
/// each maximal segment's staged removals/rewrites are committed only if they do
/// not increase the segment's estimated byte size
/// ([`crate::optimizer_bridge::estimate_arm_byte_size`], the #511 encoder mirror)
/// — otherwise the whole segment's CSE is declined and every materialization is
/// kept. Monotone-or-neutral on size by measurement, not by hand-wave.
///
/// WIN RECOVERY (PR2, #242): the cross-register fold above only catches a
/// constant that is *still resident* in some register. gale measured
/// 61% of flat_flight's materializations as redundant, yet almost none are of that
/// shape — the greedy selector re-materializes each clamp constant into the SAME
/// register, which is clobbered between uses, so no register holds it at the reuse.
/// PR2 adds two pieces: (1) [`const_units`] reconstructs 32-bit `movw+movt` pairs
/// so large constants are visible; (2) a same-register *extending-alias* hoist pins
/// a repeatedly re-materialized value in a register that is provably FREE across
/// the reuse window ([`free_reg_over`]), deletes the repeats, and retargets the
/// reads. Because the hoist introduces one extra live register, each segment it
/// touches is additionally gated on post-transform peak pressure
/// ([`straight_line_peak_pressure`]) ≤ [`ALLOCATABLE_POOL`] — so it can never turn
/// a fitting segment into a spilling one. This is post-hoc removal+retarget, not
/// inline two-vreg aliasing, so it does not reintroduce the alias-eviction hazard;
/// the only risk is register pressure, which the guard measures directly.
///
/// Returns the rewritten stream and the count removed. Pure; callers opt in
/// (flag-gated, differential-verified).
pub fn apply_const_cse(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    // Two independent, individually-guarded passes, run in sequence. Pass 2 runs
    // on Pass 1's *output* (not the original), so it observes the register uses
    // Pass 1 introduced — a hoist that moves a materialization's destination can
    // then correctly retarget a read Pass 1 aliased onto that register.
    let (s1, c1) = cross_reg_const_cse(instrs);
    let (s2, c2) = extending_alias_hoist(&s1);
    (s2, c1 + c2)
}

/// Pass 1 (PR1): cross-register const-CSE. A `movw rd,#v` whose value is already
/// resident in a *different* register `ra`, provably live through every later
/// read of `rd` until `rd` is redefined in-segment → drop it and retarget the
/// reads to `ra`. 16-bit / `mov #imm` only (a `movt` high half acts as a redefine
/// that clears the tracked value). Per-segment size-guarded; never grows a
/// function; declines a whole segment whose rewrite would grow it.
fn cross_reg_const_cse(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    use crate::optimizer_bridge::estimate_arm_byte_size;
    let n = instrs.len();
    let mut removed = vec![false; n];
    let mut rewrites: Vec<(usize, Reg, Reg)> = Vec::new(); // (use_index, from, to)

    let mut seg_start = 0;
    let mut process_segment = |start: usize, end: usize| {
        let mut seg_removed: Vec<usize> = Vec::new();
        let mut seg_rewrites: Vec<(usize, Reg, Reg)> = Vec::new();
        let mut held: Vec<(Reg, i32)> = Vec::new(); // reg → resident constant
        for i in start..end {
            if let Some((rd, v)) = const_materialization(&instrs[i].op) {
                if let Some(&(ra, _)) = held.iter().find(|&&(_, val)| val == v)
                    && ra != rd
                    && let Some(use_indices) = safe_cse_uses(instrs, i, rd, ra, end)
                {
                    seg_removed.push(i);
                    for j in use_indices {
                        seg_rewrites.push((j, rd, ra));
                    }
                    continue; // movw dropped; rd not added to `held`
                }
                held.retain(|&(r, _)| r != rd);
                held.push((rd, v));
            } else if let Some(eff) = reg_effect(&instrs[i].op) {
                for d in &eff.defs {
                    held.retain(|&(r, _)| r != *d);
                }
            }
        }
        if seg_removed.is_empty() {
            return;
        }
        let mut renames_seg: BTreeMap<usize, Vec<(Reg, Reg)>> = BTreeMap::new();
        for &(j, from, to) in &seg_rewrites {
            renames_seg.entry(j).or_default().push((from, to));
        }
        let orig_bytes: usize = (start..end)
            .map(|i| estimate_arm_byte_size(&instrs[i].op))
            .sum();
        let new_bytes: usize = (start..end)
            .filter(|i| !seg_removed.contains(i))
            .map(|i| {
                let mut op = instrs[i].op.clone();
                if let Some(rs) = renames_seg.get(&i) {
                    for &(from, to) in rs {
                        op = rename_use(&op, from, to).unwrap_or(op);
                    }
                }
                estimate_arm_byte_size(&op)
            })
            .sum();
        if new_bytes <= orig_bytes {
            for i in seg_removed {
                removed[i] = true;
            }
            rewrites.extend(seg_rewrites);
        }
    };
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) || reg_effect(&ins.op).is_none() {
            if i > seg_start {
                process_segment(seg_start, i);
            }
            seg_start = i + 1;
        }
    }
    if instrs.len() > seg_start {
        process_segment(seg_start, instrs.len());
    }

    if rewrites.is_empty() && !removed.iter().any(|&r| r) {
        return (instrs.to_vec(), 0);
    }
    let mut renames_at: BTreeMap<usize, Vec<(Reg, Reg)>> = BTreeMap::new();
    for (j, from, to) in rewrites {
        renames_at.entry(j).or_default().push((from, to));
    }
    let mut out = Vec::with_capacity(n);
    let mut count = 0;
    for (i, ins) in instrs.iter().enumerate() {
        if removed[i] {
            count += 1;
            continue;
        }
        let mut op = ins.op.clone();
        if let Some(rs) = renames_at.get(&i) {
            for &(from, to) in rs {
                op = rename_use(&op, from, to).unwrap_or(op);
            }
        }
        out.push(ArmInstruction {
            op,
            source_line: ins.source_line,
        });
    }
    (out, count)
}

/// Pass 2 (PR2, #242 win recovery): same-register extending-alias hoist. The
/// greedy selector re-materializes a constant into the SAME register at each
/// reuse (e.g. flat_flight's clamp `movw r3,#980 … movw r3,#980`, with `r3`
/// clobbered between — so no register holds it and Pass 1 misses
/// it). For a value re-materialized into one register ≥2× in a straight-line
/// segment, pin it in a register that is provably FREE across the reuse window
/// ([`free_reg_over`]), delete the repeat materializations, and retarget the
/// reads. Because this introduces one extra live register, every touched segment
/// is gated on post-transform peak pressure ≤ [`ALLOCATABLE_POOL`] as well as the
/// #242 no-grow size guard — so it can never turn a fitting segment into a
/// spilling one, nor grow a function.
fn extending_alias_hoist(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    use crate::optimizer_bridge::estimate_arm_byte_size;
    let n = instrs.len();
    let mut removed = vec![false; n];
    let mut rewrites: Vec<(usize, Reg, Reg)> = Vec::new(); // (use_index, from, to)
    let mut replace_at: BTreeMap<usize, ArmOp> = BTreeMap::new(); // holder materializations

    let mut seg_start = 0;
    let mut process_segment = |start: usize, end: usize| {
        let seg = &instrs[start..end];
        let units = const_units(seg);
        let unit_starts: BTreeSet<usize> = units.iter().map(|u| u.start).collect();
        let unit_len_at = |k: usize| units.iter().find(|u| u.start == k).map(|u| u.len);
        let mut groups: BTreeMap<(i32, Reg), Vec<usize>> = BTreeMap::new();
        for (ui, u) in units.iter().enumerate() {
            groups.entry((u.value, u.rd)).or_default().push(ui);
        }

        let mut seg_removed: Vec<usize> = Vec::new();
        let mut seg_rewrites: Vec<(usize, Reg, Reg)> = Vec::new();
        let mut seg_replace: BTreeMap<usize, ArmOp> = BTreeMap::new();
        let mut reserved: BTreeSet<Reg> = BTreeSet::new();

        for ((value, rd), uidxs) in groups {
            if uidxs.len() < 2 {
                continue; // nothing to fold away
            }
            // Walk from the first unit collecting the reads that observe this value
            // (`rd` holding it, bounded by clobbers), and check locality — the last
            // materialization's value must die in-segment (a live-out `rd` cannot be
            // dropped, else a later segment would read an undefined register).
            let first_start = units[uidxs[0]].start;
            let mut covered: Vec<usize> = Vec::new();
            let mut holds_v = false;
            let mut ok = true;
            let mut k = first_start;
            while k < seg.len() {
                if unit_starts.contains(&k)
                    && let Some(len) = unit_len_at(k)
                    && units
                        .iter()
                        .any(|u| u.start == k && u.rd == rd && u.value == value)
                {
                    holds_v = true;
                    k += len;
                    continue;
                }
                let Some(eff) = reg_effect(&seg[k].op) else {
                    ok = false;
                    break;
                };
                if holds_v && eff.uses.contains(&rd) {
                    if rename_use(&seg[k].op, rd, rd).is_none() {
                        ok = false;
                        break;
                    }
                    covered.push(k);
                }
                if eff.defs.contains(&rd) {
                    holds_v = false;
                }
                k += 1;
            }
            if !ok || holds_v || covered.is_empty() {
                continue;
            }
            let hi = *covered.iter().max().unwrap();
            let mut avoid = reserved.clone();
            avoid.insert(rd);
            let Some(rf) = free_reg_over(seg, first_start, hi, &avoid) else {
                continue; // no register free across the reuse window → decline
            };
            // Stage the holder materialization into `rf` (same value, new reg).
            let holder = &units[uidxs[0]];
            let staged_holder: Option<Vec<(usize, ArmOp)>> = match holder.len {
                2 => match (&seg[holder.start].op, &seg[holder.start + 1].op) {
                    (ArmOp::Movw { imm16: lo16, .. }, ArmOp::Movt { imm16: hi16, .. }) => {
                        Some(vec![
                            (
                                holder.start,
                                ArmOp::Movw {
                                    rd: rf,
                                    imm16: *lo16,
                                },
                            ),
                            (
                                holder.start + 1,
                                ArmOp::Movt {
                                    rd: rf,
                                    imm16: *hi16,
                                },
                            ),
                        ])
                    }
                    _ => None,
                },
                _ => match &seg[holder.start].op {
                    ArmOp::Movw { imm16, .. } => Some(vec![(
                        holder.start,
                        ArmOp::Movw {
                            rd: rf,
                            imm16: *imm16,
                        },
                    )]),
                    ArmOp::Mov {
                        op2: Operand2::Imm(x),
                        ..
                    } => Some(vec![(
                        holder.start,
                        ArmOp::Mov {
                            rd: rf,
                            op2: Operand2::Imm(*x),
                        },
                    )]),
                    _ => None,
                },
            };
            let Some(holder_ops) = staged_holder else {
                continue;
            };
            for (k, op) in holder_ops {
                seg_replace.insert(start + k, op);
            }
            for &ui in &uidxs[1..] {
                let u = &units[ui];
                for k in u.start..u.start + u.len {
                    seg_removed.push(start + k);
                }
            }
            for k in covered {
                seg_rewrites.push((start + k, rd, rf));
            }
            reserved.insert(rf);
        }

        if seg_removed.is_empty() && seg_replace.is_empty() {
            return;
        }
        // Build the rewritten segment and gate on it: size never grows (#242) and
        // peak pressure stays within the pool (the hoist added a live register).
        let seg_removed_set: BTreeSet<usize> = seg_removed.iter().copied().collect();
        let mut renames_seg: BTreeMap<usize, Vec<(Reg, Reg)>> = BTreeMap::new();
        for &(j, from, to) in &seg_rewrites {
            renames_seg.entry(j).or_default().push((from, to));
        }
        let rewritten: Vec<ArmInstruction> = (start..end)
            .filter(|i| !seg_removed_set.contains(i))
            .map(|i| {
                let mut op = seg_replace
                    .get(&i)
                    .cloned()
                    .unwrap_or_else(|| instrs[i].op.clone());
                if let Some(rs) = renames_seg.get(&i) {
                    for &(from, to) in rs {
                        op = rename_use(&op, from, to).unwrap_or(op);
                    }
                }
                ArmInstruction {
                    op,
                    source_line: instrs[i].source_line,
                }
            })
            .collect();
        let orig_bytes: usize = (start..end)
            .map(|i| estimate_arm_byte_size(&instrs[i].op))
            .sum();
        let new_bytes: usize = rewritten
            .iter()
            .map(|x| estimate_arm_byte_size(&x.op))
            .sum();
        let pressure_ok =
            matches!(straight_line_peak_pressure(&rewritten), Some(p) if p <= ALLOCATABLE_POOL);
        if new_bytes <= orig_bytes && pressure_ok {
            for i in seg_removed {
                removed[i] = true;
            }
            rewrites.extend(seg_rewrites);
            replace_at.extend(seg_replace);
        }
    };
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) || reg_effect(&ins.op).is_none() {
            if i > seg_start {
                process_segment(seg_start, i);
            }
            seg_start = i + 1;
        }
    }
    if instrs.len() > seg_start {
        process_segment(seg_start, instrs.len());
    }

    if rewrites.is_empty() && replace_at.is_empty() && !removed.iter().any(|&r| r) {
        return (instrs.to_vec(), 0);
    }
    let mut renames_at: BTreeMap<usize, Vec<(Reg, Reg)>> = BTreeMap::new();
    for (j, from, to) in rewrites {
        renames_at.entry(j).or_default().push((from, to));
    }
    let mut out = Vec::with_capacity(n);
    let mut count = 0;
    for (i, ins) in instrs.iter().enumerate() {
        if removed[i] {
            count += 1;
            continue;
        }
        let mut op = replace_at
            .get(&i)
            .cloned()
            .unwrap_or_else(|| ins.op.clone());
        if let Some(rs) = renames_at.get(&i) {
            for &(from, to) in rs {
                op = rename_use(&op, from, to).unwrap_or(op);
            }
        }
        out.push(ArmInstruction {
            op,
            source_line: ins.source_line,
        });
    }
    (out, count)
}

// ─── VCR-RA-001 spill re-choice spike (#242) ────────────────────────────────
//
// MOTIVATION. flat_flight's hot segment runs peak register pressure 11 > the
// R0–R8 pool of 9, so every pressure-guarded optimization (const-CSE PR2, the
// extending-alias hoist) correctly declines there, and the greedy selector's
// spill placement is naive — gale measured 17 spills + 61% redundant const
// materializations on silicon (G474RE, #209). The only lever that wins on a
// genuinely-saturated segment is smarter SPILL placement: keep the value with
// the NEAREST next use in a register and send the FURTHEST-next-use value to
// memory (Belady / farthest-first). This spike ships two bounded pieces:
//
//  1. REPORT: [`spill_choice_report`] — per straight-line segment, the actual
//     frame-slot traffic the greedy lowering emitted (`ldr`/`str [sp,#N]`)
//     vs. the reload/store count a farthest-next-use (Belady MIN) allocation
//     of the same value trace would need with a k-register pool. The delta is
//     the measured headroom the full VCR-RA-001 spill-choice rewrite can
//     recover. Pure analysis; wired behind `SYNTH_SPILL_REPORT=1`.
//
//  2. REWRITE stage 1 (the simplest strictly-profitable case):
//     [`spill_forward_segment`] — slot-value forwarding *between reloads*.
//     Where a `ldr rZ,[sp,#N]` reloads a value PROVABLY still
//     register-resident (an earlier reload / store / reg-reg move of the same
//     slot value survives unclobbered), the reload is replaced by
//     `mov rZ,rY` — or DELETED outright when `rZ` itself still holds it.
//     Every rewritten reload is one fewer load executed. This is exactly the
//     case [`forward_stack_reloads`] misses: that pass forwards only from the
//     STORE's source register, so when pressure clobbers the source (the
//     real-spill case this spike targets), its reloads survive — but reload
//     #2..#n can still forward from reload #1.
//
//  3. REWRITE stage 2 (the Belady re-choice, successor to the spike):
//     [`spill_rechoice_segment`] — where NO register still holds the slot's
//     value at the reload (stage 1's decline case; flat_flight's 3 surviving
//     pairs), the value was evicted not because the pool was full but because
//     the greedy lowering re-used the HOLDING register for an unrelated value
//     while a free register existed — exactly the choice the Belady
//     (farthest-next-use) MIN plan from [`spill_choice_report`] avoids. The
//     rewrite makes the spilled value stay register-resident by RENAMING each
//     in-window kill-def of the holder (def + every use, via [`rewrite_op`])
//     onto a register that is provably dead across that def's live range,
//     then deleting the reload (or folding it to a `mov` when it targets a
//     different register). Committed per segment only under the guards
//     spelled out on [`spill_rechoice_segment`], the load-bearing one being
//     an executable same-value-flow check: the rewritten segment's symbolic
//     value trace ([`segment_value_trace`]) must be identical to the
//     original's, including exit register and frame-slot state.
//
//  Both rewrite stages share one flag (stage 2 runs on stage 1's output),
//  DEFAULT-ON; `SYNTH_SPILL_REALLOC=0` opts out ⇒ pre-flip byte-identical.

/// Registers never tracked as slot-value holders and never counted as pool
/// values: R9 (globals) / R10 (mem-size) / R11 (mem-base) are reserved, R12 is
/// the ENCODER's scratch (encode-time expansions may clobber it without any
/// `ArmOp`-level def — #212), and SP/LR/PC are never value homes.
fn is_reserved_reg(r: Reg) -> bool {
    matches!(
        r,
        Reg::R9 | Reg::R10 | Reg::R11 | Reg::R12 | Reg::SP | Reg::LR | Reg::PC
    )
}

/// True for the word-sized `[sp, #imm]` address form — the only frame-slot
/// shape the spill passes reason about (spill slots are word-aligned,
/// non-overlapping, and accessed full-word; see
/// [`eliminate_dead_frame_stores`]'s load-bearing-assumption note).
fn sp_slot(addr: &MemAddr) -> Option<i32> {
    (addr.base == Reg::SP && addr.offset_reg.is_none()).then_some(addr.offset)
}

/// VCR-RA-001 spill-reload forwarding (#242, spike step): replace or delete a
/// frame-slot reload whose value is provably already in a register.
///
/// Per maximal straight-line, fully-modeled segment (same segmentation as
/// [`reallocate_function`]), tracks — per slot `#N` — the set of R0–R8
/// registers currently holding slot `N`'s value. Sources: the feeding
/// `str rY,[sp,#N]` (holder `rY`), a reload `ldr rY,[sp,#N]` (holder `rY`),
/// and value copies (`mov rZ,rY` extends every set containing `rY`). Kills: a
/// redefinition of the register (any modeled def, including `Movt`'s RMW), a
/// store to the slot (set reset to the new source), ANY `[sp]` access that
/// cannot be pinned to a single whole word slot (register-offset or sub-word),
/// `Push`/`Pop` (SP moves + stack memory touched), and any SP def. A reload
/// `ldr rZ,[sp,#N]` with a surviving holder `rY` becomes `mov rZ,rY` (1-for-1,
/// count-neutral, load→1-cycle move), or is DELETED when `rZ == rY`
/// (offset-safe: runs before `resolve_label_branches`, like every pass here).
///
/// SOUNDNESS is by construction: the replacement writes `rZ` with the exact
/// value the load would have fetched (the holder tracking proves memory and
/// register agree), and a deletion leaves `rZ` already holding that value —
/// every downstream register state is bit-identical. Non-SP stores are assumed
/// not to alias the frame (wasm linear memory via R11 is disjoint from the
/// machine stack — the same assumption [`forward_stack_reloads`] ships with).
///
/// COMMIT GATES, per segment (the whole segment keeps its original bytes if
/// any gate fails):
///  (a) semantics — by construction, above;
///  (b) instruction count must not grow — structural (replacements are 1-for-1,
///      deletions shrink), asserted;
///  (c) register-pressure guard: a `mov` extends the holder value's live
///      range, so the segment's post-transform peak VALUE pressure
///      ([`straight_line_peak_pressure`]) must not exceed the pre-transform
///      peak unless it still fits the R0–R8 pool ([`ALLOCATABLE_POOL`]) — the
///      rewrite never turns a fitting segment into a spilling one, and on an
///      already-saturated segment (flat_flight's peak 11) it never makes the
///      saturation worse.
///
/// Returns the rewritten stream and the number of reloads
/// forwarded/eliminated across both stages (stage 1 forwarding + stage 2
/// Belady re-choice, see the module block above — stage 2 runs on stage 1's
/// output, same flag).
/// Pure; DEFAULT-ON via the `arm_backend.rs` wiring (`SYNTH_SPILL_REALLOC=0`
/// is the opt-out).
pub fn apply_spill_realloc(instrs: &[ArmInstruction]) -> (Vec<ArmInstruction>, usize) {
    let mut out: Vec<ArmInstruction> = Vec::with_capacity(instrs.len());
    let mut total = 0usize;
    let mut seg: Vec<ArmInstruction> = Vec::new();
    let flush =
        |seg: &mut Vec<ArmInstruction>, out: &mut Vec<ArmInstruction>, total: &mut usize| {
            if seg.is_empty() {
                return;
            }
            // Stage 1: slot-value forwarding between reloads.
            let (mut cur, mut n) = match spill_forward_segment(seg) {
                Some((rewritten, n)) => (rewritten, n),
                None => (seg.clone(), 0),
            };
            // Stage 2: Belady spill-plan re-choice on the surviving reloads.
            if let Some((rewritten, m)) = spill_rechoice_segment(&cur) {
                cur = rewritten;
                n += m;
            }
            if n > 0 {
                *total += n;
                out.extend(cur);
            } else {
                out.append(seg); // nothing fired: keep the original bytes
            }
            seg.clear();
        };
    for ins in instrs {
        if is_straight_line(&ins.op) && reg_effect(&ins.op).is_some() {
            seg.push(ins.clone());
        } else {
            flush(&mut seg, &mut out, &mut total);
            out.push(ins.clone());
        }
    }
    flush(&mut seg, &mut out, &mut total);
    (out, total)
}

/// One segment of [`apply_spill_realloc`]: `Some((rewritten, count))` iff at
/// least one reload was forwarded/deleted AND every commit gate holds;
/// `None` ⇒ caller keeps the original segment bytes.
fn spill_forward_segment(seg: &[ArmInstruction]) -> Option<(Vec<ArmInstruction>, usize)> {
    // slot #N → set of R0–R8 registers currently holding slot N's value.
    let mut holders: BTreeMap<i32, BTreeSet<Reg>> = BTreeMap::new();
    // Staged edits: index → Some(op) = replace, None = delete.
    let mut staged: BTreeMap<usize, Option<ArmOp>> = BTreeMap::new();

    for (i, ins) in seg.iter().enumerate() {
        match &ins.op {
            // Full-word reload of a pinnable slot — the forwarding candidate.
            ArmOp::Ldr { rd, addr } if sp_slot(addr).is_some() => {
                let slot = sp_slot(addr).unwrap();
                let rd = *rd;
                let known = holders.get(&slot).cloned().unwrap_or_default();
                if !is_reserved_reg(rd) && known.contains(&rd) {
                    // rd already holds the slot's value — the reload is a no-op.
                    staged.insert(i, None);
                    // State unchanged: rd keeps the (identical) value.
                } else if !is_reserved_reg(rd) && !known.is_empty() {
                    let ry = *known.iter().next().unwrap(); // lowest reg: deterministic
                    staged.insert(
                        i,
                        Some(ArmOp::Mov {
                            rd,
                            op2: Operand2::Reg(ry),
                        }),
                    );
                    // rd is redefined with the slot's value (same as the ldr):
                    for set in holders.values_mut() {
                        set.remove(&rd);
                    }
                    // rd now equals ry — it joins every slot set ry belongs to
                    // (which includes `slot`).
                    for set in holders.values_mut() {
                        if set.contains(&ry) {
                            set.insert(rd);
                        }
                    }
                } else {
                    // Ordinary reload: rd is redefined and now holds slot's value.
                    for set in holders.values_mut() {
                        set.remove(&rd);
                    }
                    if !is_reserved_reg(rd) {
                        holders.entry(slot).or_default().insert(rd);
                    }
                }
            }
            // Full-word store to a pinnable slot: the slot now holds rd's value.
            ArmOp::Str { rd, addr } if sp_slot(addr).is_some() => {
                let mut set = BTreeSet::new();
                if !is_reserved_reg(*rd) {
                    set.insert(*rd);
                }
                holders.insert(sp_slot(addr).unwrap(), set);
            }
            // Any [sp] access we cannot pin to a single whole word slot:
            // register offset (unresolvable) or sub-word (partial overlap).
            ArmOp::Ldr { addr, .. } | ArmOp::Str { addr, .. } if addr.base == Reg::SP => {
                holders.clear();
            }
            ArmOp::Ldrb { addr, .. }
            | ArmOp::Ldrsb { addr, .. }
            | ArmOp::Ldrh { addr, .. }
            | ArmOp::Ldrsh { addr, .. }
            | ArmOp::Strb { addr, .. }
            | ArmOp::Strh { addr, .. }
                if addr.base == Reg::SP =>
            {
                holders.clear();
            }
            // SP moves + stack memory touched — every slot name is invalidated.
            ArmOp::Push { .. } | ArmOp::Pop { .. } => holders.clear(),
            // Register-to-register copy propagates value identity.
            ArmOp::Mov {
                rd,
                op2: Operand2::Reg(rm),
            } if rd != rm => {
                let (rd, rm) = (*rd, *rm);
                let member: Vec<i32> = holders
                    .iter()
                    .filter(|(_, s)| s.contains(&rm))
                    .map(|(k, _)| *k)
                    .collect();
                for set in holders.values_mut() {
                    set.remove(&rd);
                }
                if !is_reserved_reg(rd) {
                    for k in member {
                        if let Some(s) = holders.get_mut(&k) {
                            s.insert(rd);
                        }
                    }
                }
            }
            op => {
                // Segment precondition guarantees Some; `?` stays sound if the
                // segmentation ever drifts.
                let eff = reg_effect(op)?;
                if eff.defs.contains(&Reg::SP) {
                    holders.clear();
                } else {
                    for d in &eff.defs {
                        for set in holders.values_mut() {
                            set.remove(d);
                        }
                    }
                }
            }
        }
    }
    if staged.is_empty() {
        return None;
    }

    let mut rewritten: Vec<ArmInstruction> = Vec::with_capacity(seg.len());
    for (i, ins) in seg.iter().enumerate() {
        match staged.get(&i) {
            None => rewritten.push(ins.clone()),
            Some(None) => {} // deleted redundant reload
            Some(Some(op)) => rewritten.push(ArmInstruction {
                op: op.clone(),
                source_line: ins.source_line,
            }),
        }
    }
    // Gate (b): never grow — structural, but asserted so a future edit that
    // breaks the 1-for-1/deletion property fails loudly.
    assert!(
        rewritten.len() <= seg.len(),
        "spill_forward_segment must never grow a segment"
    );
    // Gate (c): pressure guard — a forwarding `mov` extends the holder's live
    // range; commit only if the segment still fits the pool or did not get
    // more saturated than it already was.
    let pre = straight_line_peak_pressure(seg)?;
    let post = straight_line_peak_pressure(&rewritten)?;
    if post > pre && post > ALLOCATABLE_POOL {
        return None;
    }
    Some((rewritten, staged.len()))
}

/// Symbolic value trace of one straight-line segment — the executable
/// same-value-flow oracle behind stage 2's guard (a).
///
/// Registers and word frame slots are dissolved into abstract VALUE ids
/// (birth order: lazily on first read for segment inputs, per def otherwise).
/// Pure value plumbing produces NO event and births no value: a word
/// `str [sp,#N]` binds the slot to its source's value, a word `ldr [sp,#N]`
/// re-binds the target register to the slot's value, and a plain `mov rd,rm`
/// copies value identity. Every other modeled op emits one event: the VALUES
/// it reads (in [`reg_effect`] order) and how many values it births. Two
/// streams with equal traces and equal exit register/slot maps compute the
/// same values everywhere and leave the machine in the same state — register
/// names are exactly what is quotiented out, which is what a spill-plan
/// rewrite changes and nothing more.
#[derive(Debug, PartialEq, Eq)]
struct SegmentTrace {
    /// Per observable op: (value ids read, number of values defined).
    events: Vec<(Vec<usize>, usize)>,
    /// Register → value id at segment exit.
    exit_regs: BTreeMap<Reg, usize>,
    /// Word frame slot → value id at segment exit.
    exit_slots: BTreeMap<i32, usize>,
}

/// Compute the [`SegmentTrace`] of a straight-line segment, or `None` if the
/// segment cannot be traced soundly. The `None` cases double as stage 2's
/// guard (d) — the #483-class conservatism inherited from the frame-slot DCE:
/// any sub-word (`ldrb`/`ldrh`/…) or register-offset `[sp]` access, and any
/// reload from a slot whose value is unknown (written outside the segment or
/// invalidated by an SP move) disqualify the segment.
fn segment_value_trace(seg: &[ArmInstruction]) -> Option<SegmentTrace> {
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new(); // reg → value id
    let mut slots: BTreeMap<i32, usize> = BTreeMap::new(); // slot → value id
    let mut n_values = 0usize;
    let mut events: Vec<(Vec<usize>, usize)> = Vec::new();

    fn read(r: Reg, current: &mut BTreeMap<Reg, usize>, n: &mut usize) -> usize {
        *current.entry(r).or_insert_with(|| {
            let v = *n; // segment input: born on first read
            *n += 1;
            v
        })
    }

    for ins in seg {
        match &ins.op {
            // Word spill store to a pinnable slot: value plumbing, no event.
            ArmOp::Str { rd, addr } if sp_slot(addr).is_some() => {
                let v = read(*rd, &mut current, &mut n_values);
                slots.insert(sp_slot(addr).unwrap(), v);
            }
            // Word spill reload: the slot's value must be known — an unknown
            // slot (guard d) makes the segment untraceable.
            ArmOp::Ldr { rd, addr } if sp_slot(addr).is_some() => {
                let v = *slots.get(&sp_slot(addr).unwrap())?;
                current.insert(*rd, v);
            }
            // Plain register move: value identity copy, no event. (The
            // flag-setting compare/arith forms are distinct ops and take the
            // generic arm, so flag effects are never dissolved.)
            ArmOp::Mov {
                rd,
                op2: Operand2::Reg(rm),
            } => {
                let v = read(*rm, &mut current, &mut n_values);
                current.insert(*rd, v);
            }
            op => {
                // Guard (d): sub-word or register-offset frame access.
                match op {
                    ArmOp::Ldr { addr, .. } | ArmOp::Str { addr, .. } if addr.base == Reg::SP => {
                        return None; // register-offset [sp] (word forms with
                        // an immediate slot matched above)
                    }
                    ArmOp::Ldrb { addr, .. }
                    | ArmOp::Ldrsb { addr, .. }
                    | ArmOp::Ldrh { addr, .. }
                    | ArmOp::Ldrsh { addr, .. }
                    | ArmOp::Strb { addr, .. }
                    | ArmOp::Strh { addr, .. }
                        if addr.base == Reg::SP =>
                    {
                        return None; // sub-word frame access (#483-class)
                    }
                    // SP moves + stack memory touched: slot names invalidated.
                    ArmOp::Push { .. } | ArmOp::Pop { .. } => slots.clear(),
                    _ => {}
                }
                let eff = reg_effect(op)?;
                let uses: Vec<usize> = eff
                    .uses
                    .iter()
                    .map(|u| read(*u, &mut current, &mut n_values))
                    .collect();
                events.push((uses, eff.defs.len()));
                if eff.defs.contains(&Reg::SP) {
                    slots.clear();
                }
                for d in &eff.defs {
                    let v = n_values;
                    n_values += 1;
                    current.insert(*d, v);
                }
            }
        }
    }
    Some(SegmentTrace {
        events,
        exit_regs: current,
        exit_slots: slots,
    })
}

/// Peak simultaneous VALUE pressure counting only values homed in the
/// allocatable R0–R8 pool — [`straight_line_peak_pressure`] restricted to the
/// registers that actually compete for spill slots (R9–R12/SP/LR/PC values are
/// reserved-resident and never candidates). Stage 2's guard (c) metric.
fn pool_peak_pressure(instrs: &[ArmInstruction]) -> Option<usize> {
    let pool = hoist_pool();
    let n = instrs.len();
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new();
    let mut def_at: Vec<usize> = Vec::new();
    let mut last_use: Vec<usize> = Vec::new();
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) {
            return None;
        }
        let eff = reg_effect(&ins.op)?;
        for u in &eff.uses {
            if !pool.contains(u) {
                continue;
            }
            let vid = *current.entry(*u).or_insert_with(|| {
                def_at.push(0);
                last_use.push(0);
                def_at.len() - 1
            });
            last_use[vid] = i;
        }
        for d in &eff.defs {
            if !pool.contains(d) {
                continue;
            }
            def_at.push(i);
            last_use.push(i);
            current.insert(*d, def_at.len() - 1);
        }
    }
    let mut delta = vec![0i32; n + 1];
    for vid in 0..def_at.len() {
        let (d, l) = (def_at[vid], last_use[vid]);
        if l > d {
            delta[d] += 1;
            delta[l] -= 1;
        }
    }
    let (mut cur, mut peak) = (0i32, 0i32);
    for d in delta.iter().take(n) {
        cur += *d;
        peak = peak.max(cur);
    }
    Some(peak as usize)
}

/// A surviving spill pair stage 2 attempts to dissolve: `str holder,[sp,#slot]`
/// at `store`, next word reload of the same slot at `load` into `rd`, with no
/// intervening store to the slot and no SP event in between.
struct SpillPair {
    store: usize,
    load: usize,
    holder: Reg,
    rd: Reg,
}

/// Collect the candidate spill pairs of a segment, in stream order.
fn collect_spill_pairs(seg: &[ArmInstruction]) -> Vec<SpillPair> {
    let mut live_stores: BTreeMap<i32, (usize, Reg)> = BTreeMap::new();
    let mut pairs = Vec::new();
    for (i, ins) in seg.iter().enumerate() {
        match &ins.op {
            ArmOp::Str { rd, addr } if sp_slot(addr).is_some() => {
                let slot = sp_slot(addr).unwrap();
                if is_reserved_reg(*rd) {
                    live_stores.remove(&slot);
                } else {
                    live_stores.insert(slot, (i, *rd));
                }
            }
            ArmOp::Ldr { rd, addr } if sp_slot(addr).is_some() => {
                let slot = sp_slot(addr).unwrap();
                if let Some(&(store, holder)) = live_stores.get(&slot)
                    && !is_reserved_reg(*rd)
                {
                    pairs.push(SpillPair {
                        store,
                        load: i,
                        holder,
                        rd: *rd,
                    });
                }
            }
            op => {
                // Any event that invalidates slot addressing kills the map.
                let sp_event = match op {
                    ArmOp::Push { .. } | ArmOp::Pop { .. } => true,
                    _ => reg_effect(op).is_none_or(|e| e.defs.contains(&Reg::SP)),
                };
                if sp_event {
                    live_stores.clear();
                }
            }
        }
    }
    pairs
}

/// Rename the kill-def of `r` at position `k` in `scratch` — the def AND every
/// read of that def, via [`rewrite_op`] — onto a register that is provably
/// dead across the def's live range. Returns `None` (scratch may be partially
/// edited; the caller works on a throwaway clone) if no such register exists
/// or the ops cannot be renamed (single-field RMW like `Movt`/`SelectMove`).
///
/// Deadness proof for the target `t`, all within the segment:
///  - `t` is untouched (no def, no use) at every position in `(k, q]` and not
///    read or co-defined at `k` itself, where `q` is the last read of the
///    renamed def — so the rename cannot clobber or misread a live value;
///  - the FIRST op touching `t` after `q` is a pure def of `t` (`t` ∉ its
///    uses), and such a def EXISTS in the segment — so `t`'s incoming value is
///    dead at `k` (never read again) and `t`'s exit value is that later def's,
///    unchanged by the rename. A `t` never touched again could be live-out:
///    rejected.
fn rename_kill_def(scratch: &mut [ArmInstruction], k: usize, r: Reg) -> Option<()> {
    // The def's live range: reads of `r` strictly after `k`, up to and
    // including any reads AT the next def of `r` (operands are consumed
    // before the write). No next def in the segment ⇒ the value may be
    // live-out in `r` ⇒ renaming would change exit state ⇒ decline.
    let mut uses: Vec<usize> = Vec::new();
    let mut next_def: Option<usize> = None;
    for (i, ins) in scratch.iter().enumerate().skip(k + 1) {
        let eff = reg_effect(&ins.op)?;
        if eff.uses.contains(&r) {
            uses.push(i);
        }
        if eff.defs.contains(&r) {
            next_def = Some(i);
            break;
        }
    }
    next_def?;
    let q = uses.last().copied().unwrap_or(k);

    let target = hoist_pool().into_iter().find(|&t| {
        if t == r {
            return false;
        }
        // Untouched over [k, q] (at k: not read, not co-defined).
        for (i, ins) in scratch.iter().enumerate().take(q + 1).skip(k) {
            let Some(eff) = reg_effect(&ins.op) else {
                return false;
            };
            if eff.uses.contains(&t) || (eff.defs.contains(&t) && i != k) {
                return false;
            }
            if i == k && eff.defs.contains(&t) {
                return false; // multi-def op already defines t (e.g. Umull)
            }
        }
        // First touch after q must be a pure in-segment def.
        for ins in &scratch[q + 1..] {
            let Some(eff) = reg_effect(&ins.op) else {
                return false;
            };
            if eff.uses.contains(&t) {
                return false; // read first → t's value is live
            }
            if eff.defs.contains(&t) {
                return true; // pure redefinition → dead in between
            }
        }
        false // never touched again → possibly live-out → decline
    })?;

    let rename: BTreeMap<Reg, Reg> = [(r, target)].into_iter().collect();
    let empty: BTreeMap<Reg, Reg> = BTreeMap::new();
    scratch[k].op = rewrite_op(&scratch[k].op, &empty, &rename)?;
    for &i in &uses {
        scratch[i].op = rewrite_op(&scratch[i].op, &rename, &empty)?;
    }
    Some(())
}

/// Attempt to dissolve one spill pair on a throwaway clone of the segment:
/// rename every kill-def of the holder inside the window, then delete the
/// reload (or fold it to `mov rd,holder` when it targets another register).
/// `None` ⇒ some kill-def could not be renamed; caller keeps the input.
fn dissolve_spill_pair(seg: &[ArmInstruction], pair: &SpillPair) -> Option<Vec<ArmInstruction>> {
    let mut scratch = seg.to_vec();
    // Rename kill-defs left to right; each rename removes that def of the
    // holder, so re-scanning always terminates.
    let mut i = pair.store + 1;
    while i < pair.load {
        let eff = reg_effect(&scratch[i].op)?;
        if eff.defs.contains(&pair.holder) {
            rename_kill_def(&mut scratch, i, pair.holder)?;
        }
        i += 1;
    }
    if pair.rd == pair.holder {
        scratch.remove(pair.load); // the reload is a proven no-op
    } else {
        scratch[pair.load].op = ArmOp::Mov {
            rd: pair.rd,
            op2: Operand2::Reg(pair.holder),
        };
    }
    Some(scratch)
}

/// VCR-RA-001 stage 2 — the Belady spill-plan re-choice (#242). Where the
/// [`spill_choice_report`] shows the farthest-next-use (Belady MIN) allocation
/// needs strictly less frame traffic than the segment executes, rewrite the
/// segment's spill placement toward that plan: each surviving reload whose
/// value was evicted only because the greedy lowering re-used the holding
/// register while a provably-dead register existed is dissolved by renaming
/// the clobbering def(s) onto that register ([`rename_kill_def`]) and deleting
/// the reload. Register assignments stay within the R0–R8 pool; the frame
/// never grows (no slot is added — freed slots are simply left to the
/// flag-shared dead-store sweep).
///
/// COMMIT GATES — the segment keeps its original bytes unless ALL hold:
///  (a) same value flow: the rewritten segment's [`segment_value_trace`] —
///      every op reads the same VALUES, exit register and slot state
///      identical — must equal the original's (executable, not by-argument);
///  (b) the segment must net strictly FEWER instructions and a strictly
///      smaller estimated byte size (a `mov`-only fold that nets ≥0
///      instructions is discarded), so a fired segment always shrinks and the
///      function can never grow flag-on;
///  (c) post-transform pool-value pressure ≤ the R0–R8 pool
///      ([`pool_peak_pressure`]) — the re-chosen residency must actually fit;
///  (d) sub-word or register-offset `[sp]` accesses and reloads from unknown
///      slots disqualify the whole segment (inside [`segment_value_trace`],
///      the #483-class conservatism).
///
/// Returns `Some((rewritten, reloads_dissolved))` or `None` to keep the input.
fn spill_rechoice_segment(seg: &[ArmInstruction]) -> Option<(Vec<ArmInstruction>, usize)> {
    use crate::optimizer_bridge::estimate_arm_byte_size;
    // Cheap prefilter: nothing to re-choose without a word [sp,#N] reload.
    if !seg
        .iter()
        .any(|ins| matches!(&ins.op, ArmOp::Ldr { addr, .. } if sp_slot(addr).is_some()))
    {
        return None;
    }
    // Guard (d) + baseline for guard (a).
    let baseline = segment_value_trace(seg)?;
    // Only segments where the Belady MIN plan beats the executed traffic.
    let report = segment_spill_choice(seg, ALLOCATABLE_POOL, 0)?;
    if report.belady_reloads + report.belady_spill_stores
        >= report.actual_reloads + report.actual_spill_stores
    {
        return None;
    }

    let pairs = collect_spill_pairs(seg);
    let mut cur = seg.to_vec();
    let mut dissolved = 0usize;
    // Back to front: deleting a reload only shifts positions after it, so
    // earlier pairs' recorded positions stay valid.
    for pair in pairs.iter().rev() {
        if let Some(candidate) = dissolve_spill_pair(&cur, pair)
            // Guard (a), per pair: value flow provably unchanged.
            && segment_value_trace(&candidate).as_ref() == Some(&baseline)
        {
            cur = candidate;
            dissolved += 1;
        }
    }
    if dissolved == 0 {
        return None;
    }
    // Guard (b): strictly fewer instructions AND strictly smaller bytes.
    let bytes = |s: &[ArmInstruction]| {
        s.iter()
            .map(|i| estimate_arm_byte_size(&i.op))
            .sum::<usize>()
    };
    if cur.len() >= seg.len() || bytes(&cur) >= bytes(seg) {
        return None;
    }
    // Guard (c): the re-chosen residency fits the pool.
    if pool_peak_pressure(&cur)? > ALLOCATABLE_POOL {
        return None;
    }
    Some((cur, dissolved))
}

/// Per-segment greedy-vs-Belady spill-choice report — the REPORT half of the
/// VCR-RA-001 spike (#242). See [`spill_choice_report`].
#[derive(Debug, Clone)]
pub struct SegmentSpillChoice {
    /// Function-stream index of the segment's first instruction.
    pub start: usize,
    /// Segment length in instructions.
    pub len: usize,
    /// Peak VALUE pressure of the segment ([`straight_line_peak_pressure`]).
    pub peak_pressure: usize,
    /// Frame-slot reloads the greedy lowering actually emitted
    /// (word `ldr [sp,#imm]` count).
    pub actual_reloads: usize,
    /// Frame-slot stores the greedy lowering actually emitted
    /// (word `str [sp,#imm]` count).
    pub actual_spill_stores: usize,
    /// Reloads a farthest-next-use (Belady MIN) allocation of the segment's
    /// value trace would execute with a k-register pool.
    pub belady_reloads: usize,
    /// Spill stores the Belady allocation would execute.
    pub belady_spill_stores: usize,
}

/// The greedy-vs-farthest-next-use spill-choice delta, per straight-line
/// segment: how much of the emitted frame-slot traffic a Belady (evict the
/// value with the FURTHEST next use) allocation over `k` registers would
/// avoid. `actual_* − belady_*` is the measured recovery headroom for the full
/// VCR-RA-001 spill-choice rewrite.
///
/// METHOD. The segment's frame traffic is first dissolved back into an
/// abstract VALUE trace: a `str [sp,#N]` binds slot `N` to its source's value
/// and a `ldr [sp,#N]` re-binds the target register to that same value — so a
/// value's uses after a reload are uses of the ORIGINAL value, and the spill
/// instructions themselves vanish from the ideal trace (a reload from a slot
/// whose value is unknown — written outside the segment — stays a genuine,
/// unavoidable load and is charged to Belady too). Values homed in reserved
/// registers (R9–R12/SP/LR/PC) are excluded: they do not compete for the pool.
/// Belady MIN then replays the trace with `k` register slots, evicting the
/// resident value with the farthest next use (a first eviction of a value that
/// is still needed and has no memory copy costs one store; re-touching an
/// evicted value costs one reload).
///
/// CAVEAT (stated, not hidden): the actual counts include the frame-resident
/// lowering's LOCAL-variable traffic, so the delta is the ceiling recoverable
/// by full value-based allocation (locals promoted + Belady spill choice), not
/// by spill re-choice alone. Pure analysis — changes no bytes; wired behind
/// `SYNTH_SPILL_REPORT=1`.
pub fn spill_choice_report(instrs: &[ArmInstruction], k: usize) -> Vec<SegmentSpillChoice> {
    let mut out = Vec::new();
    let mut seg_start = 0usize;
    let flush = |start: usize, end: usize, out: &mut Vec<SegmentSpillChoice>| {
        if end > start
            && let Some(r) = segment_spill_choice(&instrs[start..end], k, start)
        {
            out.push(r);
        }
    };
    for (i, ins) in instrs.iter().enumerate() {
        if !is_straight_line(&ins.op) || reg_effect(&ins.op).is_none() {
            flush(seg_start, i, &mut out);
            seg_start = i + 1;
        }
    }
    flush(seg_start, instrs.len(), &mut out);
    out
}

/// Value-trace reconstruction + Belady MIN simulation for one straight-line,
/// fully-modeled segment. `None` iff the segment cannot be modeled (should not
/// happen under [`spill_choice_report`]'s segmentation).
fn segment_spill_choice(
    seg: &[ArmInstruction],
    k: usize,
    start: usize,
) -> Option<SegmentSpillChoice> {
    // ── 1. Reconstruct the abstract value trace. ──────────────────────────
    let mut current: BTreeMap<Reg, usize> = BTreeMap::new(); // reg → value id
    let mut slot_value: BTreeMap<i32, usize> = BTreeMap::new(); // slot → value id
    let mut n_values = 0usize;
    let mut mem_origin: Vec<bool> = Vec::new(); // value born memory-resident?
    // Per position: values that must be register-resident (reads), values born
    // into a register (writes), values entering from unknown memory (charged
    // as unavoidable reloads on both sides).
    struct PosTouch {
        required: Vec<usize>,
        born: Vec<usize>,
        mem_born: Vec<usize>,
    }
    let mut touches: Vec<PosTouch> = Vec::with_capacity(seg.len());
    let mut required_at: Vec<Vec<usize>> = Vec::new(); // value → positions
    let mut actual_reloads = 0usize;
    let mut actual_spill_stores = 0usize;

    let mut new_value = |mem: bool, mem_origin: &mut Vec<bool>| -> usize {
        let v = n_values;
        n_values += 1;
        mem_origin.push(mem);
        v
    };

    for (p, ins) in seg.iter().enumerate() {
        let mut t = PosTouch {
            required: Vec::new(),
            born: Vec::new(),
            mem_born: Vec::new(),
        };
        match &ins.op {
            // Spill store: binds the slot to the source's value; not part of
            // the ideal trace (the value is already in a register here).
            ArmOp::Str { rd, addr } if sp_slot(addr).is_some() => {
                actual_spill_stores += 1;
                match current.get(rd).copied() {
                    Some(v) if !is_reserved_reg(*rd) => {
                        slot_value.insert(sp_slot(addr).unwrap(), v);
                    }
                    _ => {
                        slot_value.remove(&sp_slot(addr).unwrap());
                    }
                }
            }
            // Spill reload: re-binds the register to the slot's value. A known
            // slot value vanishes from the ideal trace; an unknown one is a
            // genuine memory-resident value entering registers.
            ArmOp::Ldr { rd, addr } if sp_slot(addr).is_some() => {
                actual_reloads += 1;
                let slot = sp_slot(addr).unwrap();
                if is_reserved_reg(*rd) {
                    current.remove(rd);
                } else {
                    match slot_value.get(&slot).copied() {
                        Some(v) => {
                            current.insert(*rd, v);
                        }
                        None => {
                            let v = new_value(true, &mut mem_origin);
                            required_at.push(Vec::new());
                            slot_value.insert(slot, v);
                            current.insert(*rd, v);
                            t.mem_born.push(v);
                        }
                    }
                }
            }
            op => {
                // Any other [sp] access invalidates the slot map (unpinnable),
                // but still has its ordinary register effect.
                let sp_touch = match op {
                    ArmOp::Ldr { addr, .. }
                    | ArmOp::Str { addr, .. }
                    | ArmOp::Ldrb { addr, .. }
                    | ArmOp::Ldrsb { addr, .. }
                    | ArmOp::Ldrh { addr, .. }
                    | ArmOp::Ldrsh { addr, .. }
                    | ArmOp::Strb { addr, .. }
                    | ArmOp::Strh { addr, .. } => addr.base == Reg::SP,
                    ArmOp::Push { .. } | ArmOp::Pop { .. } => true,
                    _ => false,
                };
                if sp_touch {
                    slot_value.clear();
                }
                let eff = reg_effect(op)?;
                for u in &eff.uses {
                    if is_reserved_reg(*u) {
                        continue;
                    }
                    let v = match current.get(u).copied() {
                        Some(v) => v,
                        None => {
                            // Segment input: arrives register-resident.
                            let v = new_value(false, &mut mem_origin);
                            required_at.push(Vec::new());
                            current.insert(*u, v);
                            v
                        }
                    };
                    t.required.push(v);
                    required_at[v].push(p);
                }
                if eff.defs.contains(&Reg::SP) {
                    slot_value.clear();
                }
                for d in &eff.defs {
                    if is_reserved_reg(*d) {
                        current.remove(d);
                        continue;
                    }
                    let v = new_value(false, &mut mem_origin);
                    required_at.push(Vec::new());
                    current.insert(*d, v);
                    t.born.push(v);
                }
            }
        }
        touches.push(t);
    }

    // ── 2. Belady MIN replay with k register slots. ───────────────────────
    let next_required = |v: usize, p: usize| -> Option<usize> {
        let reqs = &required_at[v];
        let idx = reqs.partition_point(|&q| q <= p);
        reqs.get(idx).copied()
    };
    let mut resident: BTreeSet<usize> = BTreeSet::new();
    let mut stored: BTreeSet<usize> = BTreeSet::new(); // has a memory copy
    let mut belady_reloads = 0usize;
    let mut belady_spill_stores = 0usize;

    for (p, t) in touches.iter().enumerate() {
        let make_room = |resident: &mut BTreeSet<usize>,
                         stored: &mut BTreeSet<usize>,
                         protect: &BTreeSet<usize>,
                         stores: &mut usize| {
            while resident.len() >= k {
                // Farthest next requirement; a value never needed again (None)
                // is the ideal victim and costs nothing.
                let victim = resident
                    .iter()
                    .filter(|v| !protect.contains(v))
                    .max_by_key(|&&v| next_required(v, p).unwrap_or(usize::MAX))
                    .copied();
                let Some(v) = victim else { break }; // over-wide instruction
                if next_required(v, p).is_some() && !stored.contains(&v) {
                    *stores += 1;
                    stored.insert(v);
                }
                resident.remove(&v);
            }
        };
        // Reads: every required value must be resident (protect all reads).
        let protect: BTreeSet<usize> = t.required.iter().copied().collect();
        for &v in &t.required {
            if resident.contains(&v) {
                continue;
            }
            // First touch of an input value is free (it arrives in a register);
            // re-touching an evicted (memory-backed) value is a reload.
            if stored.contains(&v) || mem_origin[v] {
                belady_reloads += 1;
            }
            make_room(
                &mut resident,
                &mut stored,
                &protect,
                &mut belady_spill_stores,
            );
            resident.insert(v);
        }
        // Writes: reads are done (operands consumed before the write), so only
        // the values born at this instruction are protected.
        let born_protect: BTreeSet<usize> =
            t.born.iter().chain(t.mem_born.iter()).copied().collect();
        for &v in &t.born {
            make_room(
                &mut resident,
                &mut stored,
                &born_protect,
                &mut belady_spill_stores,
            );
            resident.insert(v);
        }
        for &v in &t.mem_born {
            belady_reloads += 1; // unavoidable: the slot was written elsewhere
            make_room(
                &mut resident,
                &mut stored,
                &born_protect,
                &mut belady_spill_stores,
            );
            resident.insert(v);
            stored.insert(v); // its memory copy exists by construction
        }
    }

    Some(SegmentSpillChoice {
        start,
        len: seg.len(),
        peak_pressure: straight_line_peak_pressure(seg)?,
        actual_reloads,
        actual_spill_stores,
        belady_reloads,
        belady_spill_stores,
    })
}

/// Per-register def+use occurrence counts over an instruction stream — the
/// numerator of Chaitin's spill cost (each spill inserts a store per def and a
/// reload per use, so spill cost scales with occurrences). Unmodeled ops are
/// skipped; callers needing strict modelling already gate on
/// [`interference_graph`] returning `Some`, which implies every op is modeled.
pub fn use_def_counts(instrs: &[ArmInstruction]) -> BTreeMap<Reg, usize> {
    let mut counts: BTreeMap<Reg, usize> = BTreeMap::new();
    for ins in instrs {
        if let Some(e) = reg_effect(&ins.op) {
            for r in e.defs.iter().chain(e.uses.iter()) {
                *counts.entry(*r).or_insert(0) += 1;
            }
        }
    }
    counts
}

/// Run the register-allocator pipeline on a function: interference graph →
/// `k`-colouring with `precolored` reserved registers pinned and spill
/// candidates ranked by Chaitin cost (def+use count / degree) → result. `k` is
/// the allocatable-pool size (e.g. 9 for synth's R0–R8). Pure: it computes a
/// decision and does not mutate the instruction stream — the call the codegen
/// wiring (VCR-RA-001) makes, runnable today as a shadow pass.
pub fn allocate_function(
    instrs: &[ArmInstruction],
    k: usize,
    precolored: &BTreeMap<Reg, usize>,
) -> AllocationOutcome {
    let Some(graph) = interference_graph(instrs) else {
        return AllocationOutcome::Declined;
    };
    let remat_opportunities = analyze_function(instrs).redundant_consts.len();
    let costs = use_def_counts(instrs);
    match color_graph_precolored_costed(&graph, k, precolored, &costs) {
        ColorResult::Colored(coloring) => AllocationOutcome::Allocated {
            coloring,
            remat_opportunities,
        },
        ColorResult::Spilled(s) => AllocationOutcome::NeedsSpill(s),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::instruction_selector::ArmInstruction;
    use crate::rules::{ArmOp, Condition, Operand2, Reg};

    fn ins(op: ArmOp) -> ArmInstruction {
        ArmInstruction {
            op,
            source_line: None,
        }
    }

    // ---- VCR-SEL-004 cmp→select → IT-block predication ---------------------

    fn cmp(rn: Reg, rm: Reg) -> ArmInstruction {
        ins(ArmOp::Cmp {
            rn,
            op2: Operand2::Reg(rm),
        })
    }
    fn cmp0(rn: Reg) -> ArmInstruction {
        ins(ArmOp::Cmp {
            rn,
            op2: Operand2::Imm(0),
        })
    }
    fn setcond(rd: Reg, cond: Condition) -> ArmInstruction {
        ins(ArmOp::SetCond { rd, cond })
    }
    fn selmov(rd: Reg, rm: Reg, cond: Condition) -> ArmInstruction {
        ins(ArmOp::SelectMove { rd, rm, cond })
    }
    /// A pure redefinition of `rd` (def, no use) — makes a prior value provably
    /// dead, standing in for the register reuse that follows a consumed temp.
    fn redef(rd: Reg) -> ArmInstruction {
        ins(ArmOp::Movw { rd, imm16: 0 })
    }

    #[test]
    fn invert_is_exhaustive_and_involutive() {
        use Condition::*;
        let pairs = [(EQ, NE), (LT, GE), (GT, LE), (LO, HS), (HI, LS)];
        for (a, b) in pairs {
            assert_eq!(a.invert(), b, "{a:?}.invert()");
            assert_eq!(b.invert(), a, "{b:?}.invert()");
        }
        // Involution over every variant.
        for c in [EQ, NE, LT, LE, GT, GE, LO, LS, HI, HS] {
            assert_eq!(c.invert().invert(), c, "invert∘invert on {c:?}");
            assert_ne!(c.invert(), c, "a condition is never its own inverse");
        }
    }

    #[test]
    fn fuse_cmp_select_signed_two_move_form() {
        // cmp r1,r2 ; SetCond r3,LT ; cmp r3,#0 ; movne r0,r4 ; moveq r0,r5 ; <redef r3>
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            redef(Reg::R3),
        ];
        let (out, fused) = fuse_cmp_select(&seq);
        assert_eq!(fused, 1);
        // SetCond + cmp r3,#0 deleted ⇒ 6 → 4.
        assert_eq!(out.len(), 4);
        assert!(matches!(out[0].op, ArmOp::Cmp { rn: Reg::R1, .. }));
        // movne→movlt (c), moveq→movge (invert c).
        assert!(matches!(
            out[1].op,
            ArmOp::SelectMove {
                rd: Reg::R0,
                rm: Reg::R4,
                cond: Condition::LT
            }
        ));
        assert!(matches!(
            out[2].op,
            ArmOp::SelectMove {
                rd: Reg::R0,
                rm: Reg::R5,
                cond: Condition::GE
            }
        ));
        // no SetCond and no `cmp _,#0` survive.
        assert!(!out.iter().any(|i| matches!(i.op, ArmOp::SetCond { .. })));
        assert!(!out.iter().any(|i| matches!(
            &i.op,
            ArmOp::Cmp {
                op2: Operand2::Imm(0),
                ..
            }
        )));
    }

    #[test]
    fn fuse_cmp_select_unsigned_condition() {
        // unsigned `<` lowers to LO; inverse is HS.
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LO),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            redef(Reg::R3),
        ];
        let (out, fused) = fuse_cmp_select(&seq);
        assert_eq!(fused, 1);
        assert!(matches!(
            out[1].op,
            ArmOp::SelectMove {
                cond: Condition::LO,
                ..
            }
        ));
        assert!(matches!(
            out[2].op,
            ArmOp::SelectMove {
                cond: Condition::HS,
                ..
            }
        ));
    }

    #[test]
    fn fuse_cmp_select_gust_mix_back_to_back_inplace_clamps() {
        // The literal gust_mix shape: clamp r4 to [r6, r5] via two in-place
        // selects (single predicated move each, no `moveq`):
        //   cmp r4,r5 ; SetCond r3,GT ; cmp r3,#0 ; movne r4,r5   (upper clamp)
        //   cmp r4,r6 ; SetCond r3,LT ; cmp r3,#0 ; movne r4,r6   (lower clamp)
        // r3 is dead between (clamp 2's SetCond redefines it) and after (redef).
        let seq = vec![
            cmp(Reg::R4, Reg::R5),
            setcond(Reg::R3, Condition::GT),
            cmp0(Reg::R3),
            selmov(Reg::R4, Reg::R5, Condition::NE),
            cmp(Reg::R4, Reg::R6),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R4, Reg::R6, Condition::NE),
            redef(Reg::R3),
        ];
        let (out, fused) = fuse_cmp_select(&seq);
        assert_eq!(fused, 2, "both clamps fuse");
        // 9 → 5 (two SetCond + two cmp,#0 removed).
        assert_eq!(out.len(), 5);
        // The textbook predicated clamps: movgt r4,r5 and movlt r4,r6.
        assert!(matches!(
            out[1].op,
            ArmOp::SelectMove {
                rm: Reg::R5,
                cond: Condition::GT,
                ..
            }
        ));
        assert!(matches!(
            out[3].op,
            ArmOp::SelectMove {
                rm: Reg::R6,
                cond: Condition::LT,
                ..
            }
        ));
    }

    #[test]
    fn no_fuse_when_d_is_live_downstream() {
        // r3 (the boolean) is READ after the select ⇒ SetCond cannot be deleted.
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            ins(ArmOp::Add {
                rd: Reg::R7,
                rn: Reg::R3, // reads the boolean
                op2: Operand2::Imm(1),
            }),
        ];
        let (out, fused) = fuse_cmp_select(&seq);
        assert_eq!(fused, 0, "must decline — boolean is consumed");
        assert_eq!(out.len(), seq.len());
    }

    #[test]
    fn no_fuse_when_flags_clobbered_in_window() {
        // A flag-setting op sits between SetCond and the select's cmp ⇒ the
        // comparison's flags would not survive ⇒ decline.
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            ins(ArmOp::Subs {
                rd: Reg::R6,
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R7),
            }),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            redef(Reg::R3),
        ];
        let (_out, fused) = fuse_cmp_select(&seq);
        assert_eq!(fused, 0, "must decline — flags clobbered in the window");
    }

    #[test]
    fn no_fuse_when_predecessor_not_a_compare() {
        // SetCond not preceded by a flag-setting compare ⇒ no flags to reuse.
        let seq = vec![
            ins(ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Imm(5),
            }),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            redef(Reg::R3),
        ];
        let (_out, fused) = fuse_cmp_select(&seq);
        assert_eq!(fused, 0, "must decline — predecessor is not Cmp/Cmn");
    }

    #[test]
    fn no_fuse_when_dst_aliases_boolean() {
        // dst == D: refuse (keeps the dead-check unambiguous).
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R3, Reg::R4, Condition::NE),
            redef(Reg::R3),
        ];
        let (_out, fused) = fuse_cmp_select(&seq);
        assert_eq!(fused, 0, "must decline — dst aliases the boolean register");
    }

    #[test]
    fn no_fuse_when_boolean_not_redefined_and_no_return() {
        // r3 is neither redefined NOR followed by a recognized return terminator —
        // the scan runs off the end of the slice, which stays conservative
        // (`false`): without seeing the function exit we cannot prove r3 not
        // live-out. (Add a `pop {…,pc}` / `bx lr` and it fuses — see below.)
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
        ];
        let (_out, fused) = fuse_cmp_select(&seq);
        assert_eq!(fused, 0, "must decline — no redef and no return terminator");
    }

    // ---- #7: return-terminator deadness (the two-move arm becomes reachable) ----

    /// `pop {regs}` epilogue containing PC — a function return.
    fn ret_pop() -> ArmInstruction {
        ins(ArmOp::Pop {
            regs: vec![Reg::R4, Reg::R5, Reg::PC],
        })
    }

    #[test]
    fn fuse_two_move_abandoned_boolean_before_pop_return() {
        // The shape the real selector emits: a two-move select whose boolean (r3)
        // is ABANDONED — never redefined — then a `pop {…,pc}` return. r3 ∉ {R0,R1}
        // ⇒ not live-out ⇒ dead ⇒ fuse. This is the case #444's redef-only guard
        // declined; it makes the two-move `mov{invert(c)}` arm reachable.
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            ret_pop(),
        ];
        let (out, fused) = fuse_cmp_select(&seq);
        assert_eq!(fused, 1, "abandoned boolean before a return is dead ⇒ fuse");
        // movne→movlt (c), moveq→movge (invert c) — the two-move arm exercised.
        assert!(matches!(
            out[1].op,
            ArmOp::SelectMove {
                cond: Condition::LT,
                ..
            }
        ));
        assert!(matches!(
            out[2].op,
            ArmOp::SelectMove {
                cond: Condition::GE,
                ..
            }
        ));
        assert!(!out.iter().any(|i| matches!(i.op, ArmOp::SetCond { .. })));
    }

    #[test]
    fn fuse_two_move_abandoned_boolean_before_bx_lr() {
        // Leaf return via `bx lr` — also a return terminator (reg_effect bails on
        // Bx, so this only fuses because is_return_terminator recognizes it).
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            ins(ArmOp::Bx { rm: Reg::LR }),
        ];
        let (_out, fused) = fuse_cmp_select(&seq);
        assert_eq!(
            fused, 1,
            "bx lr is a return ⇒ abandoned non-result boolean is dead"
        );
    }

    #[test]
    fn fuse_stats_splits_two_move_from_in_place() {
        // The diagnostic split feeding SYNTH_FUSE_STATS + the fusion census. A
        // two-move shape (both `movne`/`moveq` present) counts as two_move; an
        // in-place shape (only `movne`, dst already holds v2) counts as in_place
        // (= total − two_move). Locks the census's blast-radius arithmetic.
        let two_move_seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            ret_pop(),
        ];
        let (_o, total, two_move) = fuse_cmp_select_with_stats(&two_move_seq);
        assert_eq!((total, two_move), (1, 1), "the moveq arm ⇒ two-move");

        // In-place: no `moveq` — dst (r0) is left holding v2 on the false edge.
        let in_place_seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            ret_pop(),
        ];
        let (_o2, total2, two_move2) = fuse_cmp_select_with_stats(&in_place_seq);
        assert_eq!(
            (total2, two_move2),
            (1, 0),
            "single move ⇒ in-place, not two-move"
        );
    }

    // ---- perf lever 1: redundant stack-reload elimination (#390) ----

    fn str_sp(rd: Reg, slot: i32) -> ArmInstruction {
        ins(ArmOp::Str {
            rd,
            addr: MemAddr::imm(Reg::SP, slot),
        })
    }
    fn ldr_sp(rd: Reg, slot: i32) -> ArmInstruction {
        ins(ArmOp::Ldr {
            rd,
            addr: MemAddr::imm(Reg::SP, slot),
        })
    }
    fn movi(rd: Reg, imm: i32) -> ArmInstruction {
        ins(ArmOp::Mov {
            rd,
            op2: Operand2::Imm(imm),
        })
    }

    #[test]
    fn fold_imm_shift_basic_folds_movw_into_lsl() {
        // movw r7,#24 ; <neutral> ; lsl r8,r6,r7 ; movw r7,#0 (redef ⇒ r7 dead)
        // ⇒ lsl r8,r6,#24 and the movw is removed (−1 instruction).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 24,
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R1,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::LslReg {
                rd: Reg::R8,
                rn: Reg::R6,
                rm: Reg::R7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0,
            }), // redef ⇒ r7 dead after the shift
        ];
        let (out, n) = fold_immediate_shifts(&seq);
        assert_eq!(n, 1);
        assert_eq!(out.len(), seq.len() - 1, "the folded movw is removed");
        assert!(
            out.iter().any(|i| matches!(
                i.op,
                ArmOp::Lsl {
                    rd: Reg::R8,
                    rn: Reg::R6,
                    shift: 24
                }
            )),
            "register shift folded to immediate lsl #24"
        );
        assert!(
            !out.iter().any(|i| matches!(i.op, ArmOp::LslReg { .. })),
            "no register-form shift remains"
        );
    }

    #[test]
    fn fold_imm_shift_lsr_and_asr() {
        for (reg_op, is_asr) in [
            (
                ArmOp::LsrReg {
                    rd: Reg::R2,
                    rn: Reg::R3,
                    rm: Reg::R4,
                },
                false,
            ),
            (
                ArmOp::AsrReg {
                    rd: Reg::R2,
                    rn: Reg::R3,
                    rm: Reg::R4,
                },
                true,
            ),
        ] {
            let seq = vec![
                ins(ArmOp::Movw {
                    rd: Reg::R4,
                    imm16: 5,
                }),
                ins(reg_op),
                ins(ArmOp::Movw {
                    rd: Reg::R4,
                    imm16: 0,
                }),
            ];
            let (out, n) = fold_immediate_shifts(&seq);
            assert_eq!(n, 1);
            let folded_asr = out
                .iter()
                .any(|i| matches!(i.op, ArmOp::Asr { shift: 5, .. }));
            let folded_lsr = out
                .iter()
                .any(|i| matches!(i.op, ArmOp::Lsr { shift: 5, .. }));
            assert_eq!(folded_asr, is_asr);
            assert_eq!(folded_lsr, !is_asr);
        }
    }

    #[test]
    fn fold_imm_shift_declines_amount_out_of_range() {
        // shift amount 40 (> 31) is not encodable as an immediate ⇒ no fold.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 40,
            }),
            ins(ArmOp::LslReg {
                rd: Reg::R8,
                rn: Reg::R6,
                rm: Reg::R7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0,
            }),
        ];
        let (out, n) = fold_immediate_shifts(&seq);
        assert_eq!(n, 0);
        assert_eq!(out.len(), seq.len());
    }

    #[test]
    fn fold_imm_shift_declines_when_amount_reg_is_also_the_value() {
        // lsl r8,r7,r7 — r7 is both value (rn) and amount (rm); dropping the movw
        // would lose the value, so decline.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 5,
            }),
            ins(ArmOp::LslReg {
                rd: Reg::R8,
                rn: Reg::R7,
                rm: Reg::R7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0,
            }),
        ];
        let (_, n) = fold_immediate_shifts(&seq);
        assert_eq!(n, 0);
    }

    #[test]
    fn fold_imm_shift_declines_when_amount_live_after_shift() {
        // r7 is read AFTER the shift (not dead) ⇒ the movw can't be dropped.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 8,
            }),
            ins(ArmOp::LslReg {
                rd: Reg::R8,
                rn: Reg::R6,
                rm: Reg::R7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R7,
                op2: Operand2::Imm(1),
            }), // reads r7
        ];
        let (_, n) = fold_immediate_shifts(&seq);
        assert_eq!(n, 0);
    }

    #[test]
    fn fold_imm_shift_declines_across_unmodeled_op() {
        // an unmodeled op (label/branch) between the movw and the shift ⇒ bail.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 8,
            }),
            ins(ArmOp::Label {
                name: "L".to_string(),
            }),
            ins(ArmOp::LslReg {
                rd: Reg::R8,
                rn: Reg::R6,
                rm: Reg::R7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0,
            }),
        ];
        let (_, n) = fold_immediate_shifts(&seq);
        assert_eq!(n, 0);
    }

    // ---- fold_uxth (#428) ----

    #[test]
    fn fold_uxth_basic_folds_mask_and_into_uxth() {
        // movw r7,#0xffff ; and r8,r6,r7 ; movw r7,#0 (redef ⇒ r7 dead)
        // ⇒ uxth r8,r6 and the movw is removed.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0xffff,
            }),
            ins(ArmOp::And {
                rd: Reg::R8,
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R7),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0,
            }),
        ];
        let (out, n) = fold_uxth(&seq);
        assert_eq!(n, 1);
        assert_eq!(out.len(), seq.len() - 1, "the folded movw is removed");
        assert!(
            out.iter().any(|i| matches!(
                i.op,
                ArmOp::Uxth {
                    rd: Reg::R8,
                    rm: Reg::R6
                }
            )),
            "mask-and folded to uxth r8,r6"
        );
        assert!(
            !out.iter().any(|i| matches!(i.op, ArmOp::And { .. })),
            "no AND remains"
        );
    }

    #[test]
    fn fold_uxth_uxtb_for_0xff_mask() {
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 0x00ff,
            }),
            ins(ArmOp::And {
                rd: Reg::R2,
                rn: Reg::R3,
                op2: Operand2::Reg(Reg::R4),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 0,
            }),
        ];
        let (out, n) = fold_uxth(&seq);
        assert_eq!(n, 1);
        assert!(
            out.iter().any(|i| matches!(
                i.op,
                ArmOp::Uxtb {
                    rd: Reg::R2,
                    rm: Reg::R3
                }
            )),
            "0xff mask folds to uxtb"
        );
    }

    #[test]
    fn fold_uxth_handles_commutative_mask_in_rn() {
        // and r8,r7,r6 with the mask in rn (r7) ⇒ source is r6.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0xffff,
            }),
            ins(ArmOp::And {
                rd: Reg::R8,
                rn: Reg::R7,
                op2: Operand2::Reg(Reg::R6),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0,
            }),
        ];
        let (out, n) = fold_uxth(&seq);
        assert_eq!(n, 1);
        assert!(
            out.iter().any(|i| matches!(
                i.op,
                ArmOp::Uxth {
                    rd: Reg::R8,
                    rm: Reg::R6
                }
            )),
            "commutative: mask in rn ⇒ uxth of the op2 source"
        );
    }

    #[test]
    fn fold_uxth_folds_when_and_writes_back_to_mask_reg() {
        // The common codegen shape: `and r3,r0,r3` reuses the mask reg as the dest.
        // The fold `uxth r3,r0` redefines r3, so the movw is dead even though r3 is
        // read afterward (it then holds the AND result, not the mask).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 0xffff,
            }),
            ins(ArmOp::And {
                rd: Reg::R3,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R3),
            }),
            ins(ArmOp::LslReg {
                rd: Reg::R3,
                rn: Reg::R3,
                rm: Reg::R5,
            }), // reads r3 (the AND result) — must NOT block the fold
        ];
        let (out, n) = fold_uxth(&seq);
        assert_eq!(n, 1, "and-writes-back-to-mask still folds");
        assert!(
            out.iter().any(|i| matches!(
                i.op,
                ArmOp::Uxth {
                    rd: Reg::R3,
                    rm: Reg::R0
                }
            )),
            "folded to uxth r3,r0"
        );
    }

    #[test]
    fn fold_uxth_declines_non_mask_constant() {
        // 0x1234 is neither 0xffff nor 0xff ⇒ not a zero-extend ⇒ no fold.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0x1234,
            }),
            ins(ArmOp::And {
                rd: Reg::R8,
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R7),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0,
            }),
        ];
        let (_, n) = fold_uxth(&seq);
        assert_eq!(n, 0);
    }

    #[test]
    fn fold_uxth_declines_when_mask_live_after_and() {
        // r7 is read again after the AND ⇒ the movw is not a dead store ⇒ no fold.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 0xffff,
            }),
            ins(ArmOp::And {
                rd: Reg::R8,
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R7),
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R7,
                op2: Operand2::Imm(1),
            }), // reads r7 ⇒ live
        ];
        let (_, n) = fold_uxth(&seq);
        assert_eq!(n, 0);
    }

    #[test]
    fn forward_reload_basic_becomes_mov() {
        // str r0,[sp,4] ; <neutral> ; ldr r1,[sp,4]  ⇒  the ldr becomes mov r1,r0.
        let seq = vec![
            str_sp(Reg::R0, 4),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R3,
                op2: Operand2::Imm(1),
            }),
            ldr_sp(Reg::R1, 4),
        ];
        let (out, n) = forward_stack_reloads(&seq);
        assert_eq!(n, 1);
        assert!(matches!(
            out[2].op,
            ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Reg(Reg::R0)
            }
        ));
        // The store is kept (slot may be read past a later bail point).
        assert!(matches!(out[0].op, ArmOp::Str { .. }));
    }

    #[test]
    fn forward_reload_multi_same_slot() {
        // One store feeds two reloads ⇒ both forward to mov.
        let seq = vec![str_sp(Reg::R0, 8), ldr_sp(Reg::R1, 8), ldr_sp(Reg::R2, 8)];
        let (out, n) = forward_stack_reloads(&seq);
        assert_eq!(n, 2);
        assert!(matches!(out[1].op, ArmOp::Mov { rd: Reg::R1, .. }));
        assert!(matches!(out[2].op, ArmOp::Mov { rd: Reg::R2, .. }));
    }

    #[test]
    fn forward_reload_stops_when_rx_clobbered() {
        // r0 is overwritten before the reload ⇒ the slot's value is stale in r0; decline.
        let seq = vec![str_sp(Reg::R0, 4), movi(Reg::R0, 99), ldr_sp(Reg::R1, 4)];
        let (out, n) = forward_stack_reloads(&seq);
        assert_eq!(n, 0);
        assert!(matches!(out[2].op, ArmOp::Ldr { .. }));
    }

    #[test]
    fn forward_reload_tracks_latest_store_after_slot_rewrite() {
        // The slot is rewritten (str r2,[sp,4]) before the reload. The FIRST store
        // (r0) must NOT forward across the rewrite; the reload forwards from the LIVE
        // store (r2) ⇒ exactly one rewrite, and it is `mov r1,r2` (not the stale r0).
        let seq = vec![str_sp(Reg::R0, 4), str_sp(Reg::R2, 4), ldr_sp(Reg::R1, 4)];
        let (out, n) = forward_stack_reloads(&seq);
        assert_eq!(n, 1);
        assert!(
            matches!(
                out[2].op,
                ArmOp::Mov {
                    rd: Reg::R1,
                    op2: Operand2::Reg(Reg::R2)
                }
            ),
            "reload must forward the LATEST store's value (r2), not the stale r0"
        );
    }

    #[test]
    fn forward_reload_bails_across_branch() {
        // A branch (reg_effect None) sits between ⇒ cannot prove the slot/reg survive
        // the other edge; decline. Same lynchpin as fuse_cmp_select.
        let seq = vec![
            str_sp(Reg::R0, 4),
            ins(ArmOp::B {
                label: "L".to_string(),
            }),
            ldr_sp(Reg::R1, 4),
        ];
        let (out, n) = forward_stack_reloads(&seq);
        assert_eq!(n, 0);
        assert!(matches!(out[2].op, ArmOp::Ldr { .. }));
    }

    #[test]
    fn forward_reload_different_slot_untouched() {
        // A reload of a DIFFERENT slot is not forwarded from this store.
        let seq = vec![str_sp(Reg::R0, 4), ldr_sp(Reg::R1, 8)];
        let (_out, n) = forward_stack_reloads(&seq);
        assert_eq!(n, 0);
    }

    #[test]
    fn no_fuse_two_move_boolean_in_result_reg() {
        // The boolean is in R0 — a result register, so it COULD be the value the
        // caller reads at the return. Cannot prove dead ⇒ decline. (This is the
        // load-bearing `d ∉ {R0,R1}` guard.)
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R0, Condition::LT),
            cmp0(Reg::R0),
            selmov(Reg::R3, Reg::R4, Condition::NE),
            selmov(Reg::R3, Reg::R5, Condition::EQ),
            ret_pop(),
        ];
        let (_out, fused) = fuse_cmp_select(&seq);
        assert_eq!(
            fused, 0,
            "boolean in a result reg may be live-out ⇒ decline"
        );
    }

    #[test]
    fn no_fuse_two_move_branch_in_tail_before_return() {
        // A branch sits between the select and the return — the forward scan bails
        // (reg_effect None) rather than walk past a control-flow split where the
        // boolean could be live on another edge.
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            ins(ArmOp::B {
                label: "L".to_string(),
            }),
            ret_pop(),
        ];
        let (_out, fused) = fuse_cmp_select(&seq);
        assert_eq!(
            fused, 0,
            "a branch in the tail ⇒ can't prove dead ⇒ decline"
        );
    }

    #[test]
    fn no_fuse_two_move_bx_to_non_lr_is_not_a_return() {
        // `bx rN` (rN≠LR) is a computed jump / tail call, NOT a plain return — its
        // live-out is not {R0,R1}, so it must stay conservative.
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            ins(ArmOp::Bx { rm: Reg::R7 }),
        ];
        let (_out, fused) = fuse_cmp_select(&seq);
        assert_eq!(fused, 0, "bx to a non-LR reg is not a return ⇒ decline");
    }

    #[test]
    fn no_fuse_two_move_label_in_tail_is_a_join_point() {
        // A Label (a potential branch target / join point) sits between the select
        // and the return. The forward scan must bail (reg_effect returns None for a
        // Label) rather than assume the boolean is not live on some incoming edge we
        // can't see by scanning forward. This LOCKS the soundness lynchpin: if anyone
        // ever teaches reg_effect a `Label => Some(empty)` arm, the scan would walk
        // through the join point and this test fails loudly.
        let seq = vec![
            cmp(Reg::R1, Reg::R2),
            setcond(Reg::R3, Condition::LT),
            cmp0(Reg::R3),
            selmov(Reg::R0, Reg::R4, Condition::NE),
            selmov(Reg::R0, Reg::R5, Condition::EQ),
            ins(ArmOp::Label {
                name: "L".to_string(),
            }),
            ret_pop(),
        ];
        let (_out, fused) = fuse_cmp_select(&seq);
        assert_eq!(
            fused, 0,
            "a Label (join point) in the tail ⇒ can't prove dead ⇒ decline"
        );
    }

    #[test]
    fn fuse_mul_add_reproduces_gale_filter_pattern() {
        // gale #257 flat_flight filter: gyro*980 + accel*20
        //   movw r4,#980 ; mul r5,r3,r4 ; movw r7,#20 ; mul r8,r6,r7 ; add r2,r5,r8
        // → the first mul (r5=r3*r4) fuses into the add: mla r2,r3,r4,r8 (mul r5 gone).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 980,
            }),
            ins(ArmOp::Mul {
                rd: Reg::R5,
                rn: Reg::R3,
                rm: Reg::R4,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R7,
                imm16: 20,
            }),
            ins(ArmOp::Mul {
                rd: Reg::R8,
                rn: Reg::R6,
                rm: Reg::R7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R8),
            }),
        ];
        let (out, fused) = fuse_mul_add(&seq);
        assert_eq!(fused, 1);
        assert_eq!(out.len(), 4, "one mul removed (5 → 4 instrs)");
        // The add became mla r2, r3, r4, r8; mul r5 is gone; mul r8 stays.
        assert!(out.iter().any(|i| matches!(
            &i.op,
            ArmOp::Mla {
                rd: Reg::R2,
                rn: Reg::R3,
                rm: Reg::R4,
                ra: Reg::R8
            }
        )));
        assert!(
            !out.iter()
                .any(|i| matches!(&i.op, ArmOp::Mul { rd: Reg::R5, .. })),
            "the fused mul is removed"
        );
        assert!(
            out.iter()
                .any(|i| matches!(&i.op, ArmOp::Mul { rd: Reg::R8, .. })),
            "the non-fused mul stays"
        );
    }

    #[test]
    fn fuse_mul_add_declines_when_mul_result_used_again() {
        // mul r5,r3,r4 ; add r2,r5,r8 ; str r5,[r0]  — r5 read after the add → no fuse.
        let seq = vec![
            ins(ArmOp::Mul {
                rd: Reg::R5,
                rn: Reg::R3,
                rm: Reg::R4,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R8),
            }),
            ins(ArmOp::Str {
                rd: Reg::R5,
                addr: crate::rules::MemAddr::imm(Reg::R0, 0),
            }),
        ];
        let (out, fused) = fuse_mul_add(&seq);
        assert_eq!(fused, 0, "mul result is live after the add → not fusable");
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn fuse_mul_add_fires_when_mul_result_is_reused_for_a_new_value_later() {
        // #257 real flat_flight shape: r8 = r6*r7 is consumed ONLY by the add,
        // then r8 is REDEFINED (movw) and reused for an unrelated value. The
        // greedy allocator's reuse of r8 must NOT block the fusion — the old
        // whole-function "r8 read anywhere?" scan wrongly counted the reads of
        // the *new* r8 and fired zero times on the deployed object.
        //   mul r8,r6,r7 ; add r2,r5,r8 ; movw r8,#980 ; mul r2,r7,r8
        let seq = vec![
            ins(ArmOp::Mul {
                rd: Reg::R8,
                rn: Reg::R6,
                rm: Reg::R7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R8),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R8,
                imm16: 980,
            }), // r8 redefined → unrelated value
            ins(ArmOp::Mul {
                rd: Reg::R2,
                rn: Reg::R7,
                rm: Reg::R8,
            }), // reads the NEW r8
        ];
        let (out, fused) = fuse_mul_add(&seq);
        assert_eq!(
            fused, 1,
            "reuse of r8 for a new value must not block fusion"
        );
        assert!(
            out.iter().any(|i| matches!(
                &i.op,
                ArmOp::Mla {
                    rd: Reg::R2,
                    rn: Reg::R6,
                    rm: Reg::R7,
                    ra: Reg::R5
                }
            )),
            "the op2-operand mul fuses with r5 as the accumulator"
        );
    }

    #[test]
    fn fuse_mul_add_declines_when_mul_input_clobbered_between() {
        // mul r5,r3,r4 ; movw r4,#1 (clobbers mul input r4) ; add r2,r5,r8
        // → mla would read the WRONG r4 → must NOT fuse.
        let seq = vec![
            ins(ArmOp::Mul {
                rd: Reg::R5,
                rn: Reg::R3,
                rm: Reg::R4,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 1,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R8),
            }),
        ];
        let (_out, fused) = fuse_mul_add(&seq);
        assert_eq!(
            fused, 0,
            "mul input r4 clobbered before the add → not fusable"
        );
    }

    // ─────────────────────────────────────────────────────────────────
    // #242 / VCR-RA — reg_effect ↔ rewrite_op def/use CONSISTENCY oracle.
    //
    // The register allocator reads an op's def/use classification two ways that
    // MUST agree: `reg_effect` (liveness — which registers an op defines vs
    // uses) and `rewrite_op` (renaming — which fields it rewrites through the
    // def-map vs the use-map). If they drift — an op edited in one but not the
    // other, or a new op modeled inconsistently — the allocator renames a def
    // as a use (or vice versa) and silently miscompiles. liveness.rs is the
    // actively-churned heart of VCR-RA, and nothing pinned this invariant.
    //
    // This is the Track-A (allocator) analogue of the #511 Track-B (encoder)
    // agreement oracle. There is no third ground truth here, so the achievable
    // invariant is mutual CONSISTENCY, checked structurally: build the def/use
    // maps FROM `reg_effect`'s classification (def regs → a def sentinel, use
    // regs → a use sentinel, read-modify-write regs → one shared sentinel so
    // `rewrite_op` doesn't decline), apply `rewrite_op`, then read the result
    // back with `reg_effect`. If the two agree on every field, every register
    // was rerouted to a sentinel; a SURVIVING original register means
    // `rewrite_op` routed a field through the opposite map — the drift.
    //
    // Scope: a regression GUARD, not a bug fix — the classification agrees for
    // all modeled ops today (measured). It freezes that agreement so a future
    // edit that desyncs the two trips loudly.

    /// Sentinels outside the operand registers used in `modeled_cases` (R0..R7).
    const DEF_SENTINEL: Reg = Reg::R10;
    const USE_SENTINEL: Reg = Reg::R11;

    /// Operand registers used to build the cases (R0..R7) — none equal a sentinel.
    const OPERAND_REGS: [Reg; 8] = [
        Reg::R0,
        Reg::R1,
        Reg::R2,
        Reg::R3,
        Reg::R4,
        Reg::R5,
        Reg::R6,
        Reg::R7,
    ];

    /// Assert `reg_effect` and `rewrite_op` classify every field of `op`
    /// identically (see the module note above). Panics on drift.
    fn assert_def_use_consistent(label: &str, op: &ArmOp) {
        let e = reg_effect(op)
            .unwrap_or_else(|| panic!("{label}: reg_effect returned None for a modeled op"));
        let defs: BTreeSet<Reg> = e.defs.iter().copied().collect();
        let uses: BTreeSet<Reg> = e.uses.iter().copied().collect();
        let mut def_map: BTreeMap<Reg, Reg> = BTreeMap::new();
        let mut use_map: BTreeMap<Reg, Reg> = BTreeMap::new();
        for &r in &defs {
            if uses.contains(&r) {
                // RMW field (def AND use of one register): both maps must agree
                // or rewrite_op declines, so route it to a single sentinel.
                def_map.insert(r, DEF_SENTINEL);
                use_map.insert(r, DEF_SENTINEL);
            } else {
                def_map.insert(r, DEF_SENTINEL);
            }
        }
        for &r in &uses {
            if !defs.contains(&r) {
                use_map.insert(r, USE_SENTINEL);
            }
        }
        let rewritten = rewrite_op(op, &use_map, &def_map)
            .unwrap_or_else(|| panic!("{label}: rewrite_op declined an op reg_effect models"));
        let e2 = reg_effect(&rewritten)
            .unwrap_or_else(|| panic!("{label}: rewritten op no longer modeled"));
        let survivors: Vec<Reg> = e2
            .defs
            .iter()
            .chain(e2.uses.iter())
            .copied()
            .filter(|r| OPERAND_REGS.contains(r))
            .collect();
        assert!(
            survivors.is_empty(),
            "{label}: reg_effect/rewrite_op def-use DRIFT — original registers \
             {survivors:?} survived rerouting (a field classified differently by \
             the two). reg_effect: defs={:?} uses={:?}",
            e.defs,
            e.uses,
        );

        // The survivor check above routes a read-modify-write register (one
        // `reg_effect` reports in BOTH defs and uses) to a single shared
        // sentinel, so it can't tell an RMW field from a def-only or use-only
        // one — both reroute cleanly. Pin the RMW property directly: for each
        // such register, `rewrite_op` must DECLINE (its documented
        // disagreement-is-a-decline contract) when the def-map and use-map send
        // it to DIFFERENT registers. If `rewrite_op` drifted to treat the field
        // as def-only or use-only, it would consult one map and return `Some` —
        // caught here. Keyed off the RMW structure, so a future dual-role op is
        // covered automatically.
        for &r in defs.intersection(&uses) {
            let d: BTreeMap<Reg, Reg> = [(r, DEF_SENTINEL)].into();
            let u: BTreeMap<Reg, Reg> = [(r, USE_SENTINEL)].into();
            assert!(
                rewrite_op(op, &u, &d).is_none(),
                "{label}: RMW register {r:?} is def+use in reg_effect, but \
                 rewrite_op did NOT decline when the def-map and use-map \
                 disagree on it — rewrite_op no longer treats the field as \
                 read-modify-write (def/use drift on a dual-role field)."
            );
        }
    }

    /// One representative instance of every ArmOp variant the allocator models,
    /// each field a distinct operand register so a misrouted field is visible.
    fn modeled_cases() -> Vec<(&'static str, ArmOp)> {
        use ArmOp::*;
        let r = OPERAND_REGS;
        let mem = |b: Reg, o: Reg| crate::rules::MemAddr {
            base: b,
            offset: 0,
            offset_reg: Some(o),
        };
        let reg = |x: Reg| Operand2::Reg(x);
        vec![
            (
                "Add",
                Add {
                    rd: r[0],
                    rn: r[1],
                    op2: reg(r[2]),
                },
            ),
            (
                "Sub",
                Sub {
                    rd: r[0],
                    rn: r[1],
                    op2: reg(r[2]),
                },
            ),
            (
                "Adds",
                Adds {
                    rd: r[0],
                    rn: r[1],
                    op2: reg(r[2]),
                },
            ),
            (
                "Subs",
                Subs {
                    rd: r[0],
                    rn: r[1],
                    op2: reg(r[2]),
                },
            ),
            (
                "Adc",
                Adc {
                    rd: r[0],
                    rn: r[1],
                    op2: reg(r[2]),
                },
            ),
            (
                "Sbc",
                Sbc {
                    rd: r[0],
                    rn: r[1],
                    op2: reg(r[2]),
                },
            ),
            (
                "And",
                And {
                    rd: r[0],
                    rn: r[1],
                    op2: reg(r[2]),
                },
            ),
            (
                "Orr",
                Orr {
                    rd: r[0],
                    rn: r[1],
                    op2: reg(r[2]),
                },
            ),
            (
                "Eor",
                Eor {
                    rd: r[0],
                    rn: r[1],
                    op2: reg(r[2]),
                },
            ),
            (
                "Mul",
                Mul {
                    rd: r[0],
                    rn: r[1],
                    rm: r[2],
                },
            ),
            (
                "Umull",
                Umull {
                    rdlo: r[0],
                    rdhi: r[1],
                    rn: r[2],
                    rm: r[3],
                },
            ),
            (
                "Sdiv",
                Sdiv {
                    rd: r[0],
                    rn: r[1],
                    rm: r[2],
                },
            ),
            (
                "Udiv",
                Udiv {
                    rd: r[0],
                    rn: r[1],
                    rm: r[2],
                },
            ),
            (
                "Mls",
                Mls {
                    rd: r[0],
                    rn: r[1],
                    rm: r[2],
                    ra: r[3],
                },
            ),
            (
                "Mla",
                Mla {
                    rd: r[0],
                    rn: r[1],
                    rm: r[2],
                    ra: r[3],
                },
            ),
            (
                "Lsl",
                Lsl {
                    rd: r[0],
                    rn: r[1],
                    shift: 1,
                },
            ),
            (
                "Lsr",
                Lsr {
                    rd: r[0],
                    rn: r[1],
                    shift: 1,
                },
            ),
            (
                "Asr",
                Asr {
                    rd: r[0],
                    rn: r[1],
                    shift: 1,
                },
            ),
            (
                "Ror",
                Ror {
                    rd: r[0],
                    rn: r[1],
                    shift: 1,
                },
            ),
            (
                "LslReg",
                LslReg {
                    rd: r[0],
                    rn: r[1],
                    rm: r[2],
                },
            ),
            (
                "LsrReg",
                LsrReg {
                    rd: r[0],
                    rn: r[1],
                    rm: r[2],
                },
            ),
            (
                "AsrReg",
                AsrReg {
                    rd: r[0],
                    rn: r[1],
                    rm: r[2],
                },
            ),
            (
                "RorReg",
                RorReg {
                    rd: r[0],
                    rn: r[1],
                    rm: r[2],
                },
            ),
            (
                "Rsb",
                Rsb {
                    rd: r[0],
                    rn: r[1],
                    imm: 4,
                },
            ),
            ("Clz", Clz { rd: r[0], rm: r[1] }),
            ("Rbit", Rbit { rd: r[0], rm: r[1] }),
            ("Popcnt", Popcnt { rd: r[0], rm: r[1] }),
            ("Sxtb", Sxtb { rd: r[0], rm: r[1] }),
            ("Sxth", Sxth { rd: r[0], rm: r[1] }),
            ("Uxtb", Uxtb { rd: r[0], rm: r[1] }),
            ("Uxth", Uxth { rd: r[0], rm: r[1] }),
            (
                "Mov",
                Mov {
                    rd: r[0],
                    op2: reg(r[1]),
                },
            ),
            (
                "Mvn",
                Mvn {
                    rd: r[0],
                    op2: reg(r[1]),
                },
            ),
            ("Movw", Movw { rd: r[0], imm16: 1 }),
            ("Movt", Movt { rd: r[0], imm16: 1 }),
            (
                "MovwSym",
                MovwSym {
                    rd: r[0],
                    symbol: "s".into(),
                    addend: 0,
                },
            ),
            (
                "MovtSym",
                MovtSym {
                    rd: r[0],
                    symbol: "s".into(),
                    addend: 0,
                },
            ),
            (
                "LdrSym",
                LdrSym {
                    rd: r[0],
                    symbol: "s".into(),
                    addend: 0,
                },
            ),
            (
                "Cmp",
                Cmp {
                    rn: r[0],
                    op2: reg(r[1]),
                },
            ),
            (
                "Cmn",
                Cmn {
                    rn: r[0],
                    op2: reg(r[1]),
                },
            ),
            (
                "Ldr",
                Ldr {
                    rd: r[0],
                    addr: mem(r[1], r[2]),
                },
            ),
            (
                "Str",
                Str {
                    rd: r[0],
                    addr: mem(r[1], r[2]),
                },
            ),
            (
                "Ldrb",
                Ldrb {
                    rd: r[0],
                    addr: mem(r[1], r[2]),
                },
            ),
            (
                "Ldrsb",
                Ldrsb {
                    rd: r[0],
                    addr: mem(r[1], r[2]),
                },
            ),
            (
                "Ldrh",
                Ldrh {
                    rd: r[0],
                    addr: mem(r[1], r[2]),
                },
            ),
            (
                "Ldrsh",
                Ldrsh {
                    rd: r[0],
                    addr: mem(r[1], r[2]),
                },
            ),
            (
                "Strb",
                Strb {
                    rd: r[0],
                    addr: mem(r[1], r[2]),
                },
            ),
            (
                "Strh",
                Strh {
                    rd: r[0],
                    addr: mem(r[1], r[2]),
                },
            ),
            (
                "SetCond",
                SetCond {
                    rd: r[0],
                    cond: Condition::EQ,
                },
            ),
            (
                "SelectMove",
                SelectMove {
                    rd: r[0],
                    rm: r[1],
                    cond: Condition::EQ,
                },
            ),
            (
                "Select",
                Select {
                    rd: r[0],
                    rval1: r[1],
                    rval2: r[2],
                    rcond: r[3],
                },
            ),
            (
                "Push",
                Push {
                    regs: vec![r[0], r[1], r[2]],
                },
            ),
            (
                "Pop",
                Pop {
                    regs: vec![r[0], r[1], r[2]],
                },
            ),
            ("Udf", Udf { imm: 0 }),
            ("Nop", Nop),
        ]
    }

    /// No-wildcard spec of which `ArmOp` variants the allocator models. A new
    /// `ArmOp` variant will not compile here until it is classified — the
    /// tripwire that forces a new op to be consciously added to (or excluded
    /// from) the allocator's def/use model. (Forces classification; adding the
    /// matching `modeled_cases` entry when `true` is a manual step, as in #511.)
    fn is_modeled(op: &ArmOp) -> bool {
        use ArmOp::*;
        match op {
            Add { .. }
            | Sub { .. }
            | Adds { .. }
            | Subs { .. }
            | Adc { .. }
            | Sbc { .. }
            | And { .. }
            | Orr { .. }
            | Eor { .. }
            | Mul { .. }
            | Umull { .. }
            | Sdiv { .. }
            | Udiv { .. }
            | Mls { .. }
            | Mla { .. }
            | Lsl { .. }
            | Lsr { .. }
            | Asr { .. }
            | Ror { .. }
            | LslReg { .. }
            | LsrReg { .. }
            | AsrReg { .. }
            | RorReg { .. }
            | Rsb { .. }
            | Clz { .. }
            | Rbit { .. }
            | Popcnt { .. }
            | Sxtb { .. }
            | Sxth { .. }
            | Uxtb { .. }
            | Uxth { .. }
            | Mov { .. }
            | Mvn { .. }
            | Movw { .. }
            | Movt { .. }
            | MovwSym { .. }
            | MovtSym { .. }
            | LdrSym { .. }
            | Cmp { .. }
            | Cmn { .. }
            | Ldr { .. }
            | Str { .. }
            | Ldrb { .. }
            | Ldrsb { .. }
            | Ldrh { .. }
            | Ldrsh { .. }
            | Strb { .. }
            | Strh { .. }
            | SetCond { .. }
            | SelectMove { .. }
            | Select { .. }
            | Push { .. }
            | Pop { .. }
            | Udf { .. }
            | Nop => true,

            // Not modeled by the allocator's def/use layer: control flow and
            // address pseudo-ops with no renamable GP-register fields, the
            // i64-pair family (lowered before allocation), and all FP/SIMD.
            MemorySize { .. }
            | MemoryGrow { .. }
            | Label { .. }
            | B { .. }
            | BOffset { .. }
            | BCondOffset { .. }
            | Bhs { .. }
            | Blo { .. }
            | Bcc { .. }
            | Bl { .. }
            | Bx { .. }
            | Blx { .. }
            | LocalGet { .. }
            | LocalSet { .. }
            | LocalTee { .. }
            | GlobalGet { .. }
            | GlobalSet { .. }
            | BrTable { .. }
            | Call { .. }
            | CallIndirect { .. }
            | I64SetCond { .. }
            | I64SetCondZ { .. }
            | I64Mul { .. }
            | I64Shl { .. }
            | I64ShrS { .. }
            | I64ShrU { .. }
            | I64Add { .. }
            | I64Sub { .. }
            | I64DivS { .. }
            | I64DivU { .. }
            | I64RemS { .. }
            | I64RemU { .. }
            | I64And { .. }
            | I64Or { .. }
            | I64Xor { .. }
            | I64Rotl { .. }
            | I64Rotr { .. }
            | I64Clz { .. }
            | I64Ctz { .. }
            | I64Popcnt { .. }
            | I64Eqz { .. }
            | I64Eq { .. }
            | I64Ne { .. }
            | I64LtS { .. }
            | I64LtU { .. }
            | I64LeS { .. }
            | I64LeU { .. }
            | I64GtS { .. }
            | I64GtU { .. }
            | I64GeS { .. }
            | I64GeU { .. }
            | I64Const { .. }
            | I64Ldr { .. }
            | I64Str { .. }
            | I64ExtendI32S { .. }
            | I64ExtendI32U { .. }
            | I64Extend8S { .. }
            | I64Extend16S { .. }
            | I64Extend32S { .. }
            | I32WrapI64 { .. }
            | F32Add { .. }
            | F32Sub { .. }
            | F32Mul { .. }
            | F32Div { .. }
            | F32Abs { .. }
            | F32Neg { .. }
            | F32Sqrt { .. }
            | F32Ceil { .. }
            | F32Floor { .. }
            | F32Trunc { .. }
            | F32Nearest { .. }
            | F32Min { .. }
            | F32Max { .. }
            | F32Copysign { .. }
            | F32Eq { .. }
            | F32Ne { .. }
            | F32Lt { .. }
            | F32Le { .. }
            | F32Gt { .. }
            | F32Ge { .. }
            | F32Const { .. }
            | F32Load { .. }
            | F32Store { .. }
            | F32ConvertI32S { .. }
            | F32ConvertI32U { .. }
            | F32ConvertI64S { .. }
            | F32ConvertI64U { .. }
            | F32ReinterpretI32 { .. }
            | I32ReinterpretF32 { .. }
            | I32TruncF32S { .. }
            | I32TruncF32U { .. }
            | F64Add { .. }
            | F64Sub { .. }
            | F64Mul { .. }
            | F64Div { .. }
            | F64Abs { .. }
            | F64Neg { .. }
            | F64Sqrt { .. }
            | F64Ceil { .. }
            | F64Floor { .. }
            | F64Trunc { .. }
            | F64Nearest { .. }
            | F64Min { .. }
            | F64Max { .. }
            | F64Copysign { .. }
            | F64Eq { .. }
            | F64Ne { .. }
            | F64Lt { .. }
            | F64Le { .. }
            | F64Gt { .. }
            | F64Ge { .. }
            | F64Const { .. }
            | F64Load { .. }
            | F64Store { .. }
            | F64ConvertI32S { .. }
            | F64ConvertI32U { .. }
            | F64ConvertI64S { .. }
            | F64ConvertI64U { .. }
            | F64PromoteF32 { .. }
            | F64ReinterpretI64 { .. }
            | I64ReinterpretF64 { .. }
            | I64TruncF64S { .. }
            | I64TruncF64U { .. }
            | I32TruncF64S { .. }
            | I32TruncF64U { .. }
            | MveLoad { .. }
            | MveStore { .. }
            | MveConst { .. }
            | MveAnd { .. }
            | MveOrr { .. }
            | MveEor { .. }
            | MveMvn { .. }
            | MveBic { .. }
            | MveAddI { .. }
            | MveSubI { .. }
            | MveMulI { .. }
            | MveNegI { .. }
            | MveCmpEqI { .. }
            | MveCmpNeI { .. }
            | MveCmpLtS { .. }
            | MveCmpLtU { .. }
            | MveCmpGtS { .. }
            | MveCmpGtU { .. }
            | MveCmpLeS { .. }
            | MveCmpLeU { .. }
            | MveCmpGeS { .. }
            | MveCmpGeU { .. }
            | MveDup { .. }
            | MveExtractLane { .. }
            | MveInsertLane { .. }
            | MveAddF32 { .. }
            | MveSubF32 { .. }
            | MveMulF32 { .. }
            | MveNegF32 { .. }
            | MveAbsF32 { .. }
            | MveCmpEqF32 { .. }
            | MveCmpNeF32 { .. }
            | MveCmpLtF32 { .. }
            | MveCmpLeF32 { .. }
            | MveCmpGtF32 { .. }
            | MveCmpGeF32 { .. }
            | MveDupF32 { .. }
            | MveExtractLaneF32 { .. }
            | MveReplaceLaneF32 { .. }
            | MveDivF32 { .. }
            | MveSqrtF32 { .. } => false,
        }
    }

    #[test]
    fn reg_effect_rewrite_op_def_use_consistency() {
        // Every modeled op: the two def/use views must agree (see module note).
        for (label, op) in modeled_cases() {
            assert!(
                is_modeled(&op),
                "{label}: in modeled_cases but is_modeled=false"
            );
            assert!(
                reg_effect(&op).is_some(),
                "{label}: modeled but reg_effect returned None"
            );
            assert_def_use_consistent(label, &op);
        }
        // A SAMPLE of NOT-modeled ops (not exhaustive): both layers must agree
        // they're unmodeled (reg_effect=None), and the spec must say so. This
        // spot-ties is_modeled to reality on the false side; the real assurance
        // that the false side is complete is the careful 55-variant extraction
        // behind `modeled_cases`, not this sample.
        let unmodeled: Vec<(&str, ArmOp)> = vec![
            ("Bx", ArmOp::Bx { rm: Reg::R0 }),
            ("Bl", ArmOp::Bl { label: "f".into() }),
            (
                "I64Mul",
                ArmOp::I64Mul {
                    rd_lo: Reg::R0,
                    rd_hi: Reg::R1,
                    rn_lo: Reg::R2,
                    rn_hi: Reg::R3,
                    rm_lo: Reg::R4,
                    rm_hi: Reg::R5,
                },
            ),
        ];
        for (label, op) in unmodeled {
            assert!(
                !is_modeled(&op),
                "{label}: is_modeled=true for an unmodeled op"
            );
            assert!(
                reg_effect(&op).is_none(),
                "{label}: reg_effect models an op is_modeled says it doesn't"
            );
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
    fn reg_effect_models_conditional_move_as_read_modify_write() {
        // SelectMove rd, rm, cond — rd preserved on the false branch → both a
        // def and a use of rd; rm is a use. (Keeps clamp chains in one segment.)
        let e = reg_effect(&ArmOp::SelectMove {
            rd: Reg::R2,
            rm: Reg::R3,
            cond: Condition::EQ,
        })
        .unwrap();
        assert_eq!(e.defs, vec![Reg::R2]);
        assert_eq!(e.uses, vec![Reg::R2, Reg::R3]);
    }

    #[test]
    fn reg_effect_models_select_reads_all_three_inputs() {
        let e = reg_effect(&ArmOp::Select {
            rd: Reg::R0,
            rval1: Reg::R1,
            rval2: Reg::R2,
            rcond: Reg::R3,
        })
        .unwrap();
        assert_eq!(e.defs, vec![Reg::R0]);
        assert_eq!(e.uses, vec![Reg::R1, Reg::R2, Reg::R3]);
    }

    #[test]
    fn redundant_const_seen_across_a_conditional_move_now_that_it_is_modeled() {
        // movw r0,#0x7e ; selectmove r1,r2,EQ ; movw r3,#0x7e
        // The SelectMove no longer breaks the segment, so the second 0x7e is
        // detected as redundant (r0 still resident) — the #209 clamp pattern.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::SelectMove {
                rd: Reg::R1,
                rm: Reg::R2,
                cond: Condition::EQ,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 0x7e,
            }),
        ];
        let r = redundant_const_defs(&seq).expect("SelectMove is now modeled, no segment break");
        assert_eq!(
            r.len(),
            1,
            "the clamp bound is seen as redundant across the IT move"
        );
        assert_eq!(r[0].available_in, Reg::R0);
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
    fn redundant_const_flags_rematerialization_while_resident() {
        // movw r0,#0x7e ; add r2,r1,r0 ; movw r3,#0x7e
        // The second 0x7e is redundant — r0 still holds it.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 0x7e,
            }),
        ];
        let r = redundant_const_defs(&seq).unwrap();
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].index, 2);
        assert_eq!(r[0].value, 0x7e);
        assert_eq!(r[0].available_in, Reg::R0);
    }

    #[test]
    fn redundant_const_respects_clobber() {
        // movw r0,#0x7e ; movw r0,#0x10 ; movw r1,#0x7e
        // r0 was overwritten, so 0x7e is NOT resident → the last is not redundant.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x10,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 0x7e,
            }),
        ];
        assert_eq!(redundant_const_defs(&seq), Some(vec![]));
    }

    #[test]
    fn redundant_const_counts_flat_flight_clamp_pattern() {
        // The measured flat_flight waste: one int8 clamp bound (#0x7e) loaded
        // into a fresh register 6 times with the first still live throughout.
        // 5 of the 6 are redundant.
        let mut seq = Vec::new();
        for k in 0..6u32 {
            seq.push(ins(ArmOp::Movw {
                rd: [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5][k as usize],
                imm16: 0x7e,
            }));
            // a consumer that keeps the earlier value live (reads R0)
            seq.push(ins(ArmOp::Add {
                rd: Reg::R6,
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R0),
            }));
        }
        let r = redundant_const_defs(&seq).unwrap();
        assert_eq!(r.len(), 5, "5 of 6 clamp materializations are redundant");
        assert!(
            r.iter()
                .all(|c| c.value == 0x7e && c.available_in == Reg::R0)
        );
    }

    #[test]
    fn redundant_const_movt_pair_is_not_a_pure_const() {
        // movw r0,#7 ; movt r0,#1  (r0 = 0x10007) ; movw r1,#7
        // After Movt, r0 no longer holds the pure 16-bit 7 → last is NOT redundant.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Movt {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 7,
            }),
        ];
        assert_eq!(redundant_const_defs(&seq), Some(vec![]));
    }

    #[test]
    fn frame_dce_removes_store_overwritten_before_read() {
        // str r0,[sp,#4] ; add ... ; str r1,[sp,#4]  — slot #4 overwritten with no
        // intervening read ⇒ the FIRST store is dead.
        let seq = vec![
            str_sp(Reg::R0, 4),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R3,
                op2: Operand2::Imm(1),
            }),
            str_sp(Reg::R1, 4),
        ];
        let (out, n) = eliminate_dead_frame_stores(&seq);
        assert_eq!(n, 1, "overwritten-before-read store is dead");
        assert_eq!(out.len(), 2);
        // The surviving store is the live one (r1) into slot #4.
        assert!(matches!(out[1].op, ArmOp::Str { rd: Reg::R1, .. }));
    }

    #[test]
    fn frame_dce_keeps_store_that_is_read() {
        // str r0,[sp,#4] ; ldr r1,[sp,#4]  — the slot is read ⇒ store is live.
        let seq = vec![str_sp(Reg::R0, 4), ldr_sp(Reg::R1, 4)];
        let (out, n) = eliminate_dead_frame_stores(&seq);
        assert_eq!(n, 0, "a store whose slot is loaded is never removed");
        assert_eq!(out, seq);
    }

    #[test]
    fn frame_dce_distinct_slots_do_not_alias() {
        // str r0,[sp,#4] ; str r1,[sp,#8] ; str r2,[sp,#4]  — #8 does not alias #4,
        // so the first #4 store is still dead (overwritten by the second #4 store).
        let seq = vec![str_sp(Reg::R0, 4), str_sp(Reg::R1, 8), str_sp(Reg::R2, 4)];
        let (out, n) = eliminate_dead_frame_stores(&seq);
        assert_eq!(n, 1, "distinct immediate slots are independent");
        assert!(
            !out.iter()
                .any(|i| matches!(&i.op, ArmOp::Str { rd: Reg::R0, .. }))
        );
    }

    #[test]
    fn frame_dce_keeps_store_across_a_call() {
        // str r0,[sp,#4] ; bl f ; str r1,[sp,#4]  — a callee could read the slot as
        // an outgoing stack argument ⇒ conservatively keep the first store.
        let seq = vec![
            str_sp(Reg::R0, 4),
            ins(ArmOp::Bl { label: "f".into() }),
            str_sp(Reg::R1, 4),
        ];
        let (_out, n) = eliminate_dead_frame_stores(&seq);
        assert_eq!(n, 0, "a call before the overwrite blocks the removal");
    }

    #[test]
    fn frame_dce_keeps_store_across_sp_change() {
        // str r0,[sp,#4] ; add sp,sp,#8 ; str r1,[sp,#4]  — sp moved, so [sp,#4] no
        // longer names the same location ⇒ conservatively keep.
        let seq = vec![
            str_sp(Reg::R0, 4),
            ins(ArmOp::Add {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(8),
            }),
            str_sp(Reg::R1, 4),
        ];
        let (_out, n) = eliminate_dead_frame_stores(&seq);
        assert_eq!(n, 0, "an SP change blocks the removal");
    }

    #[test]
    fn frame_dce_keeps_store_before_subword_read_of_slot() {
        // str r0,[sp,#4] ; ldrb r1,[sp,#4] ; str r2,[sp,#4]  — the byte load READS
        // slot #4, so the first store is NOT dead even though a later store
        // overwrites the slot. A sub-word slot access must block the removal.
        let seq = vec![
            str_sp(Reg::R0, 4),
            ins(ArmOp::Ldrb {
                rd: Reg::R1,
                addr: MemAddr::imm(Reg::SP, 4),
            }),
            str_sp(Reg::R2, 4),
        ];
        let (_out, n) = eliminate_dead_frame_stores(&seq);
        assert_eq!(n, 0, "a sub-word read of the slot blocks the removal");
    }

    #[test]
    fn frame_dce_never_crosses_a_branch() {
        // str r0,[sp,#4] ; <branch> ; str r1,[sp,#4]  — control could reach a
        // reader on the other side of the branch ⇒ the first store is kept.
        let seq = vec![
            str_sp(Reg::R0, 4),
            ins(ArmOp::BOffset { offset: 4 }),
            str_sp(Reg::R1, 4),
        ];
        let (_out, n) = eliminate_dead_frame_stores(&seq);
        assert_eq!(n, 0, "a branch between the stores blocks the removal");
    }

    #[test]
    fn frame_dce_keeps_store_before_ambiguous_reg_offset_access() {
        // str r0,[sp,#4] ; ldr r1,[sp,r2] ; str r3,[sp,#4]  — the register-offset
        // load could target slot #4 ⇒ keep.
        let seq = vec![
            str_sp(Reg::R0, 4),
            ins(ArmOp::Ldr {
                rd: Reg::R1,
                addr: MemAddr::reg(Reg::SP, Reg::R2),
            }),
            str_sp(Reg::R3, 4),
        ];
        let (_out, n) = eliminate_dead_frame_stores(&seq);
        assert_eq!(n, 0, "an unresolvable sp-relative access blocks removal");
    }

    // ---- whole-function frame-slot liveness (eliminate_unread_frame_stores) ----

    /// The flat_flight epilogue shape: `add sp,#K; pop {…, pc}`.
    fn teardown(k: i32) -> [ArmInstruction; 2] {
        [
            ins(ArmOp::Add {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(k),
            }),
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC],
            }),
        ]
    }

    #[test]
    fn unread_store_reaching_function_end_is_dropped() {
        // str r0,[sp,#8] ; add r1,… ; add sp,#88 ; pop {r4,pc} — slot #8 is never
        // read anywhere; the teardown does not count as a read. This is exactly
        // the reach-end case the segment-local pass keeps (flat_flight's 2 stores).
        let mut seq = vec![
            str_sp(Reg::R0, 8),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R2,
                op2: Operand2::Imm(1),
            }),
        ];
        seq.extend(teardown(88));
        // The segment-local pass proves nothing here (no overwrite).
        assert_eq!(eliminate_dead_frame_stores(&seq).1, 0);
        let (out, n) = eliminate_unread_frame_stores(&seq);
        assert_eq!(n, 1, "an unread reach-end store is provably dead");
        assert_eq!(out.len(), seq.len() - 1);
        assert!(!out.iter().any(|i| matches!(&i.op, ArmOp::Str { .. })));
    }

    #[test]
    fn unread_store_read_via_back_edge_is_kept() {
        // L: ldr r1,[sp,#8] ; … ; str r0,[sp,#8] ; bcc L ; teardown — the ONLY
        // read of slot #8 is BEFORE the store in program order, reachable only
        // through the loop back-edge. A linear scan would call the store dead;
        // the may-reach walk must not.
        let mut seq = vec![
            ins(ArmOp::Label { name: "L".into() }),
            ldr_sp(Reg::R1, 8),
            str_sp(Reg::R0, 8),
            ins(ArmOp::Bcc {
                cond: Condition::NE,
                label: "L".into(),
            }),
        ];
        seq.extend(teardown(16));
        let (out, n) = eliminate_unread_frame_stores(&seq);
        assert_eq!(n, 0, "a slot read via a loop back-edge is live");
        assert_eq!(out, seq);
    }

    #[test]
    fn unread_store_subword_read_blocks() {
        // str r0,[sp,#8] ; ldrb r1,[sp,#10] ; teardown — the byte load reads a
        // byte INSIDE slot #8's word ⇒ live (sub-word reads count as reads of
        // their containing word, the #483-class rule).
        let mut seq = vec![
            str_sp(Reg::R0, 8),
            ins(ArmOp::Ldrb {
                rd: Reg::R1,
                addr: MemAddr::imm(Reg::SP, 10),
            }),
        ];
        seq.extend(teardown(16));
        let (_out, n) = eliminate_unread_frame_stores(&seq);
        assert_eq!(
            n, 0,
            "a sub-word read inside the slot's word keeps the store"
        );
        // A byte read OUTSIDE the slot's word does not alias it.
        let mut seq2 = vec![
            str_sp(Reg::R0, 8),
            ins(ArmOp::Ldrb {
                rd: Reg::R1,
                addr: MemAddr::imm(Reg::SP, 12),
            }),
        ];
        seq2.extend(teardown(16));
        let (_out, n2) = eliminate_unread_frame_stores(&seq2);
        assert_eq!(n2, 1, "a byte read of a DIFFERENT word does not alias");
    }

    #[test]
    fn unread_store_unknown_index_declines_function() {
        // str r0,[sp,#8] ; ldr r1,[sp,r2] ; teardown — a register-offset sp
        // access could touch any slot: the whole function declines.
        let mut seq = vec![
            str_sp(Reg::R0, 8),
            ins(ArmOp::Ldr {
                rd: Reg::R1,
                addr: MemAddr::reg(Reg::SP, Reg::R2),
            }),
        ];
        seq.extend(teardown(16));
        let (out, n) = eliminate_unread_frame_stores(&seq);
        assert_eq!(
            n, 0,
            "an unresolvable sp access declines the whole function"
        );
        assert_eq!(out, seq);
    }

    #[test]
    fn unread_store_frame_escape_declines_function() {
        // str r0,[sp,#8] ; add r2,sp,#8 ; teardown — the slot's ADDRESS escapes
        // into r2; a later plain `ldr [r2]` could read it invisibly. Decline.
        let mut seq = vec![
            str_sp(Reg::R0, 8),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::SP,
                op2: Operand2::Imm(8),
            }),
        ];
        seq.extend(teardown(16));
        let (out, n) = eliminate_unread_frame_stores(&seq);
        assert_eq!(n, 0, "a frame-address escape declines the whole function");
        assert_eq!(out, seq);

        // mov r2, sp is the same escape.
        let mut seq2 = vec![
            str_sp(Reg::R0, 8),
            ins(ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::SP),
            }),
        ];
        seq2.extend(teardown(16));
        assert_eq!(eliminate_unread_frame_stores(&seq2).1, 0);
    }

    #[test]
    fn unread_store_call_declines_function() {
        // str r0,[sp,#0] ; bl f ; teardown — a callee may read an outgoing
        // stack-argument slot through its own view of SP. Decline.
        let mut seq = vec![str_sp(Reg::R0, 0), ins(ArmOp::Bl { label: "f".into() })];
        seq.extend(teardown(16));
        let (out, n) = eliminate_unread_frame_stores(&seq);
        assert_eq!(n, 0, "a call declines the whole function");
        assert_eq!(out, seq);
    }

    #[test]
    fn unread_store_mispaired_pop_reads_slot() {
        // str r0,[sp,#4] ; pop {r4,r5,pc} — NO `add sp` first: the pop reads
        // [sp,#0..#12), which OVERLAPS slot #4 ⇒ live. The Pop-is-teardown rule
        // is displacement-checked, not assumed.
        let seq = vec![
            str_sp(Reg::R0, 4),
            ins(ArmOp::Pop {
                regs: vec![Reg::R4, Reg::R5, Reg::PC],
            }),
        ];
        let (_out, n) = eliminate_unread_frame_stores(&seq);
        assert_eq!(n, 0, "a pop that reads the slot's bytes keeps the store");
    }

    #[test]
    fn unread_store_read_on_one_branch_arm_is_kept() {
        // str r0,[sp,#8] ; bcc T ; teardown ; T: ldr r1,[sp,#8] ; teardown —
        // one successor reads the slot, the other returns: may-reach must keep.
        let mut seq = vec![
            str_sp(Reg::R0, 8),
            ins(ArmOp::Bcc {
                cond: Condition::EQ,
                label: "T".into(),
            }),
        ];
        seq.extend(teardown(16));
        seq.push(ins(ArmOp::Label { name: "T".into() }));
        seq.push(ldr_sp(Reg::R1, 8));
        seq.extend(teardown(16));
        let (_out, n) = eliminate_unread_frame_stores(&seq);
        assert_eq!(n, 0, "a read on ANY reachable path keeps the store");
    }

    #[test]
    fn unread_store_overwrite_kills_path_and_later_read_is_of_new_value() {
        // str r0,[sp,#8] ; str r1,[sp,#8] ; ldr r2,[sp,#8] ; teardown — the
        // second store covers the slot before any read: store #1 is dead (the
        // read observes r1's value); store #2 is live.
        let mut seq = vec![str_sp(Reg::R0, 8), str_sp(Reg::R1, 8), ldr_sp(Reg::R2, 8)];
        seq.extend(teardown(16));
        let (out, n) = eliminate_unread_frame_stores(&seq);
        assert_eq!(
            n, 1,
            "overwritten-before-read store is dead; the live one stays"
        );
        assert!(matches!(out[0].op, ArmOp::Str { rd: Reg::R1, .. }));
    }

    #[test]
    fn unread_store_sp_tracking_across_frame_adjust() {
        // str r0,[sp,#8] ; sub sp,#4 ; ldr r1,[sp,#12] ; add sp,#4 ; teardown —
        // after `sub sp,#4` the SAME bytes are named [sp,#12]: the walk tracks
        // the displacement and sees the read.
        let mut seq = vec![
            str_sp(Reg::R0, 8),
            ins(ArmOp::Sub {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(4),
            }),
            ldr_sp(Reg::R1, 12),
            ins(ArmOp::Add {
                rd: Reg::SP,
                rn: Reg::SP,
                op2: Operand2::Imm(4),
            }),
        ];
        seq.extend(teardown(16));
        let (_out, n) = eliminate_unread_frame_stores(&seq);
        assert_eq!(n, 0, "a renamed read after an SP adjust is still a read");
    }

    #[test]
    fn eliminate_dead_stores_removes_overwritten_def() {
        // movw r0,#7 ; movw r0,#9 ; add r1,r0,#0
        // The first movw is a dead store → removed; result keeps 2 instructions.
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
        let (out, removed) = eliminate_dead_stores(&seq);
        assert_eq!(removed, 1);
        assert_eq!(out.len(), 2);
        // The surviving movw is the live one (#9), then the add.
        assert!(matches!(out[0].op, ArmOp::Movw { imm16: 9, .. }));
        assert!(matches!(out[1].op, ArmOp::Add { .. }));
    }

    #[test]
    fn eliminate_dead_stores_is_noop_when_nothing_dead() {
        // A clean sequence (each def used) is returned byte-for-byte unchanged.
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
        ];
        let (out, removed) = eliminate_dead_stores(&seq);
        assert_eq!(removed, 0);
        assert_eq!(out.len(), seq.len());
        assert_eq!(out, seq, "no dead stores → identical stream");
    }

    #[test]
    fn eliminate_dead_stores_never_crosses_a_branch() {
        // movw r0,#7 ; <branch> ; movw r0,#9
        // The first movw is the END of segment 1 (no in-segment overwrite), so it
        // is NOT dead (its value could be live past the branch) → nothing removed.
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
        let (out, removed) = eliminate_dead_stores(&seq);
        assert_eq!(
            removed, 0,
            "a def at a segment boundary is never dead-removed"
        );
        assert_eq!(out.len(), 3);
    }

    #[test]
    fn analyze_function_segments_across_a_branch() {
        // Segment 1: movw r0,#0x7e ; movw r1,#0x7e (r1 redundant)
        // <branch boundary>
        // Segment 2: movw r2,#0x7e ; movw r3,#0x7e (r3 redundant — fresh state)
        // The per-block detector would decline on the whole stream (branch);
        // analyze_function finds the redundancy in BOTH segments.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 0x7e,
            }),
            ins(ArmOp::BOffset { offset: 8 }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 0x7e,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 0x7e,
            }),
        ];
        // whole-stream per-block detector declines:
        assert_eq!(redundant_const_defs(&seq), None);
        // function-wide analysis finds both:
        let a = analyze_function(&seq);
        assert_eq!(a.segments, 2);
        assert_eq!(a.skipped, 1, "the branch is the skipped boundary");
        let idxs: Vec<usize> = a.redundant_consts.iter().map(|c| c.index).collect();
        assert_eq!(
            idxs,
            vec![1, 4],
            "global indices of the two redundant loads"
        );
    }

    #[test]
    fn analyze_function_resets_state_at_boundary() {
        // movw r0,#5 ; <branch> ; movw r1,#5
        // r0's #5 must NOT be considered resident after the branch → not redundant.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 5,
            }),
            ins(ArmOp::BOffset { offset: 4 }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 5,
            }),
        ];
        let a = analyze_function(&seq);
        assert!(
            a.redundant_consts.is_empty(),
            "no cross-boundary redundancy may be claimed"
        );
        assert_eq!(a.segments, 2);
    }

    #[test]
    fn redundant_const_declines_on_branch() {
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::BOffset { offset: 4 }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 0x7e,
            }),
        ];
        assert_eq!(redundant_const_defs(&seq), None);
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

    // ---- CFG-aware liveness (cfg_liveness) ---------------------------------

    #[test]
    fn cfg_liveness_straight_line_block_identifies_inputs() {
        // movw r0,#1 ; add r2,r0,r1
        // One block. r0 is defined locally (not live-in); r1 is read without a
        // prior def → it is a function input, live on entry. live_out = ∅.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let cfg = cfg_liveness(&seq).expect("straight-line stream is analyzable");
        assert_eq!(cfg.blocks.len(), 1);
        assert!(cfg.blocks[0].succ.is_empty(), "no branch → no successor");
        assert_eq!(
            cfg.live_in[0],
            BTreeSet::from([Reg::R1]),
            "only r1 (a read-before-write input) is live on entry"
        );
        assert!(
            cfg.live_out[0].is_empty(),
            "exit block live_out is empty (ABI return-liveness is layered in later)"
        );
    }

    #[test]
    fn cfg_liveness_propagates_across_conditional_branch() {
        // B0: movw r5,#42 ; bcc NE,"skip"   (succ: skip-block + fallthrough)
        // B1: mov r6,r5                       (fallthrough; reads r5)
        // B2: Label "skip" ; add r7,r5,r5     (target; reads r5)
        //
        // r5 is defined in B0 and read on *both* paths → it must be live OUT of
        // B0 and live IN of both successors, but NOT live-in of B0 (defined there).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R5,
                imm16: 42,
            }),
            ins(ArmOp::Bcc {
                cond: Condition::NE,
                label: "skip".into(),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R6,
                op2: Operand2::Reg(Reg::R5),
            }),
            ins(ArmOp::Label {
                name: "skip".into(),
            }),
            ins(ArmOp::Add {
                rd: Reg::R7,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R5),
            }),
        ];
        let cfg = cfg_liveness(&seq).expect("label-form branch is analyzable");
        assert_eq!(cfg.blocks.len(), 3, "three basic blocks");
        // B0 ends in a conditional branch → two successors.
        assert_eq!(cfg.blocks[0].succ.len(), 2);
        // r5 is born in B0: live-out yes, live-in no.
        assert!(cfg.live_out[0].contains(&Reg::R5));
        assert!(
            !cfg.live_in[0].contains(&Reg::R5),
            "r5 is defined in B0, so it is not an entry input"
        );
        // Both successors see r5 live on entry.
        for &s in &cfg.blocks[0].succ {
            assert!(
                cfg.live_in[s].contains(&Reg::R5),
                "r5 must be live entering successor block {s}"
            );
        }
    }

    #[test]
    fn cfg_liveness_unconditional_branch_has_single_successor() {
        // b "join" ; <unreachable filler> ; Label "join" ; nop
        let seq = vec![
            ins(ArmOp::B {
                label: "join".into(),
            }),
            ins(ArmOp::Label {
                name: "join".into(),
            }),
            ins(ArmOp::Nop),
        ];
        let cfg = cfg_liveness(&seq).expect("unconditional label branch is analyzable");
        assert_eq!(
            cfg.blocks[0].succ.len(),
            1,
            "an unconditional branch has exactly one successor (no fallthrough)"
        );
    }

    // ---- Interference graph (interference_graph) ---------------------------

    #[test]
    fn interference_simultaneously_live_regs_interfere() {
        // movw r1,#5 ; movw r2,#7 ; add r3,r1,r2
        // r1 and r2 are both live at the add → they interfere. r3 is defined
        // when nothing else is live-out → it interferes with NOTHING (it may
        // reuse r1's or r2's register: the precision a naive graph would lose).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 5,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R3,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R2),
            }),
        ];
        let g = interference_graph(&seq).expect("analyzable");
        assert!(g.interferes(Reg::R1, Reg::R2), "r1,r2 overlap at the add");
        assert!(
            !g.interferes(Reg::R1, Reg::R3),
            "r3 is defined after r1 dies → no interference (reuse allowed)"
        );
        assert!(!g.interferes(Reg::R2, Reg::R3));
        assert_eq!(g.edge_count(), 1, "the only edge is r1—r2");
        assert_eq!(g.degree(Reg::R1), 1);
        assert_eq!(g.degree(Reg::R3), 0);
    }

    #[test]
    fn interference_sequential_reuse_does_not_interfere() {
        // movw r1,#5 ; mov r0,r1 ; movw r1,#9 ; mov r2,r1
        // The first r1 dies into r0 before r1 is redefined → the two distinct
        // live ranges of r1 don't add a self-edge, and r0/r2 never coexist.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 5,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 9,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let g = interference_graph(&seq).expect("analyzable");
        assert!(
            !g.interferes(Reg::R0, Reg::R2),
            "r0 and r2 have disjoint live ranges"
        );
    }

    #[test]
    fn interference_co_defs_interfere() {
        // umull r0,r1,r2,r3 — the two result registers must be distinct, so the
        // co-defined r0 and r1 interfere even though neither is otherwise live.
        let seq = vec![ins(ArmOp::Umull {
            rdlo: Reg::R0,
            rdhi: Reg::R1,
            rn: Reg::R2,
            rm: Reg::R3,
        })];
        let g = interference_graph(&seq).expect("analyzable");
        assert!(
            g.interferes(Reg::R0, Reg::R1),
            "umull's rdlo and rdhi must not share a register"
        );
    }

    #[test]
    fn interference_value_live_across_a_branch_interferes_with_both_paths() {
        // r5 live across a conditional; a fresh def on each path while r5 is
        // still live must interfere with r5.
        //   movw r5,#42 ; bcc NE,"skip"
        //   mov r6,r5            (r6 defined while r5 live → interfere)
        //   Label skip ; add r7,r5,r5
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R5,
                imm16: 42,
            }),
            ins(ArmOp::Bcc {
                cond: Condition::NE,
                label: "skip".into(),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R6,
                op2: Operand2::Reg(Reg::R5),
            }),
            ins(ArmOp::Label {
                name: "skip".into(),
            }),
            ins(ArmOp::Add {
                rd: Reg::R7,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R5),
            }),
        ];
        let g = interference_graph(&seq).expect("analyzable");
        // r6 is defined where r5 is still live (r5 reaches the add on the other
        // path) → they interfere.
        assert!(g.interferes(Reg::R5, Reg::R6), "r6 defined while r5 live");
    }

    #[test]
    fn interference_declines_when_liveness_declines() {
        // A call is outside the CFG scope → cfg_liveness declines → so does this.
        let seq = vec![ins(ArmOp::Bl { label: "f".into() })];
        assert_eq!(interference_graph(&seq), None);
    }

    #[test]
    fn cfg_liveness_declines_on_call_and_offset_branch() {
        // A direct call is outside the modeled (leaf-only) scope → decline.
        let with_call = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Bl { label: "f".into() }),
        ];
        assert_eq!(cfg_liveness(&with_call), None, "calls are not yet modeled");

        // A numeric-offset branch is not label-resolvable → decline.
        let with_offset = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::BOffset { offset: -2 }),
        ];
        assert_eq!(
            cfg_liveness(&with_offset),
            None,
            "numeric-offset branches are not CFG-resolvable here"
        );
    }

    // ---- Graph colouring (color_graph) -------------------------------------

    /// Assert `colour` is a valid `k`-colouring of `g`: every node has a colour
    /// in `0..k` and no edge joins two equally-coloured nodes.
    fn assert_valid_coloring(g: &InterferenceGraph, colour: &BTreeMap<Reg, usize>, k: usize) {
        for n in g.nodes() {
            let c = *colour.get(&n).expect("every node is coloured");
            assert!(c < k, "colour in range");
            for m in g.neighbors(n) {
                assert_ne!(colour[&n], colour[&m], "adjacent nodes differ");
            }
        }
    }

    fn clique(regs: &[Reg]) -> InterferenceGraph {
        let mut g = InterferenceGraph::default();
        for (i, a) in regs.iter().enumerate() {
            g.node(*a);
            for b in &regs[i + 1..] {
                g.add_edge(*a, *b);
            }
        }
        g
    }

    #[test]
    fn color_graph_empty_is_colored() {
        let g = InterferenceGraph::default();
        assert_eq!(color_graph(&g, 3), ColorResult::Colored(BTreeMap::new()));
    }

    #[test]
    fn color_graph_colors_a_path_with_two_colors() {
        // R0—R1—R2 (a path): 2-colourable (R0,R2 share, R1 differs).
        let mut g = InterferenceGraph::default();
        g.add_edge(Reg::R0, Reg::R1);
        g.add_edge(Reg::R1, Reg::R2);
        match color_graph(&g, 2) {
            ColorResult::Colored(c) => assert_valid_coloring(&g, &c, 2),
            ColorResult::Spilled(s) => panic!("path is 2-colourable, got spill {s:?}"),
        }
    }

    #[test]
    fn color_graph_k4_clique_spills_at_k3() {
        // K4 needs 4 colours; with k=3 the heuristic must report a spill.
        let g = clique(&[Reg::R0, Reg::R1, Reg::R2, Reg::R3]);
        match color_graph(&g, 3) {
            ColorResult::Spilled(s) => assert!(!s.is_empty(), "K4 is not 3-colourable"),
            ColorResult::Colored(_) => panic!("K4 cannot be 3-coloured"),
        }
    }

    #[test]
    fn color_graph_k4_clique_colors_at_k4() {
        // With enough colours, the same clique colours with all distinct values.
        let g = clique(&[Reg::R0, Reg::R1, Reg::R2, Reg::R3]);
        match color_graph(&g, 4) {
            ColorResult::Colored(c) => {
                assert_valid_coloring(&g, &c, 4);
                let distinct: BTreeSet<usize> = c.values().copied().collect();
                assert_eq!(distinct.len(), 4, "a clique uses all colours");
            }
            ColorResult::Spilled(s) => panic!("K4 is 4-colourable, got spill {s:?}"),
        }
    }

    #[test]
    fn color_graph_k0_spills_any_node() {
        let mut g = InterferenceGraph::default();
        g.node(Reg::R0);
        assert!(matches!(color_graph(&g, 0), ColorResult::Spilled(_)));
    }

    #[test]
    fn costed_spill_picks_the_cheapest_node_not_the_smallest_reg() {
        // K4 at k=3: every node has degree 3, so degree alone cannot
        // discriminate — the degree-only heuristic falls back to the smallest
        // register (R0). With costs, R3 is by far the cheapest to spill
        // (fewest def+use occurrences), so Chaitin's cost/degree metric must
        // pick it instead. Spilling R3 leaves K3, which 3-colours, so the
        // spill set is exactly {R3}.
        let g = clique(&[Reg::R0, Reg::R1, Reg::R2, Reg::R3]);
        let costs: BTreeMap<Reg, usize> =
            [(Reg::R0, 10), (Reg::R1, 10), (Reg::R2, 10), (Reg::R3, 2)].into();
        match color_graph_precolored_costed(&g, 3, &BTreeMap::new(), &costs) {
            ColorResult::Spilled(s) => {
                assert_eq!(s, BTreeSet::from([Reg::R3]), "cheapest node spills");
            }
            ColorResult::Colored(_) => panic!("K4 cannot be 3-coloured"),
        }
    }

    #[test]
    fn empty_costs_reproduce_the_degree_only_choice() {
        // Same K4 at k=3 with NO costs: all nodes default to cost 1, the
        // ratios tie, and the tie-break picks the smallest register — the
        // historic degree-only behavior, byte-for-byte.
        let g = clique(&[Reg::R0, Reg::R1, Reg::R2, Reg::R3]);
        match color_graph(&g, 3) {
            ColorResult::Spilled(s) => {
                assert_eq!(
                    s,
                    BTreeSet::from([Reg::R0]),
                    "degree-only tie → smallest reg"
                );
            }
            ColorResult::Colored(_) => panic!("K4 cannot be 3-coloured"),
        }
    }

    #[test]
    fn use_def_counts_sums_defs_and_uses() {
        // movw r0,#7        → r0: 1 def
        // add  r1, r0, r0   → r1: 1 def, r0: +2 uses
        // add  r2, r1, r0   → r2: 1 def, r1: +1 use, r0: +1 use
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R0),
            }),
        ];
        let c = use_def_counts(&seq);
        assert_eq!(c.get(&Reg::R0), Some(&4));
        assert_eq!(c.get(&Reg::R1), Some(&2));
        assert_eq!(c.get(&Reg::R2), Some(&1));
    }

    #[test]
    fn range_interference_overlap_and_dies_at_birth() {
        // movw r0,#1        → A = r0[0..1]
        // add  r1, r0, r0   → A consumed AT 1 as B = r1[1..2] is born
        // mov  r2, r1       → B consumed AT 2 as C = r2[2..2] is born
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let ranges = straight_line_value_ranges(&seq).expect("straight-line");
        let adj = range_interference(&ranges);
        // Dies-at-birth: each value is consumed exactly as its successor is
        // born, so NO pair interferes — the whole chain colours with k=1,
        // which is exactly the register reuse the greedy selector performs.
        let edges: usize = adj.values().map(|s| s.len()).sum();
        assert_eq!(edges, 0, "a pure consume-chain has no interference");
        let (coloring, spilled) = color_ranges(&adj, 1, &BTreeMap::new(), &BTreeMap::new());
        assert!(spilled.is_empty());
        assert_eq!(coloring.len(), ranges.len());
    }

    #[test]
    fn range_interference_simultaneously_live_values_interfere() {
        // movw r0,#1 ; movw r1,#2 ; add r2,r0,r1
        // A = r0[0..2] and B = r1[1..2]: B is defined at 1 while A is still
        // live (read at 2) → they interfere and need 2 colours.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 2,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let ranges = straight_line_value_ranges(&seq).expect("straight-line");
        let adj = range_interference(&ranges);
        let a = ranges.iter().find(|r| r.reg == Reg::R0).unwrap().vreg;
        let b = ranges.iter().find(|r| r.reg == Reg::R1).unwrap().vreg;
        assert!(adj[&a].contains(&b), "simultaneously-live values interfere");
        // k=1 must spill; k=2 must colour (C reuses a dead register's colour).
        let (_, spilled1) = color_ranges(&adj, 1, &BTreeMap::new(), &BTreeMap::new());
        assert!(!spilled1.is_empty());
        let (coloring2, spilled2) = color_ranges(&adj, 2, &BTreeMap::new(), &BTreeMap::new());
        assert!(spilled2.is_empty());
        // Validity: no interfering pair shares a colour.
        for (n, nbrs) in &adj {
            for m in nbrs {
                assert_ne!(coloring2[n], coloring2[m], "{n} vs {m} share a colour");
            }
        }
    }

    #[test]
    fn range_coloring_eliminates_the_spurious_physical_spill() {
        // The VCR-RA-001 motivation in miniature. The greedy selector reuses
        // ONE physical register (r0) for three sequential values:
        //   movw r0,#1 ; mov r3,r0 ; movw r0,#2 ; mov r4,r0 ; movw r0,#3 ; mov r5,r0
        // plus r3/r4/r5 all read at the end → r3,r4,r5 simultaneously live.
        // Physical names: r0 is one overloaded node. Value ranges: r0 splits
        // into THREE independent ranges (each dies at its mov), so the true
        // pressure is 4 (three accumulators + one in-flight const), NOT the
        // 6 distinct values. Ranges must colour at k=4.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R3,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 2,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R4,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 3,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R5,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Add {
                rd: Reg::R6,
                rn: Reg::R3,
                op2: Operand2::Reg(Reg::R4),
            }),
            ins(ArmOp::Add {
                rd: Reg::R6,
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R5),
            }),
        ];
        let ranges = straight_line_value_ranges(&seq).expect("straight-line");
        // r0 split into three distinct ranges — the de-overloading itself.
        let r0_ranges = ranges.iter().filter(|r| r.reg == Reg::R0).count();
        assert_eq!(r0_ranges, 3, "r0 reuse splits into three value ranges");
        let adj = range_interference(&ranges);
        let (coloring, spilled) = color_ranges(&adj, 4, &BTreeMap::new(), &BTreeMap::new());
        assert!(
            spilled.is_empty(),
            "true value pressure is 4 — ranges colour where physical names overload"
        );
        for (n, nbrs) in &adj {
            for m in nbrs {
                assert_ne!(coloring[n], coloring[m]);
            }
        }
    }

    #[test]
    fn color_ranges_honours_precoloured_input_pins() {
        // Input range pinned to its incoming register's pool index: the pin
        // survives and constrains neighbours.
        let seq = vec![
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let ranges = straight_line_value_ranges(&seq).expect("straight-line");
        let input = ranges
            .iter()
            .find(|r| r.reg == Reg::R0 && r.def == 0)
            .unwrap()
            .vreg;
        let adj = range_interference(&ranges);
        let pins: BTreeMap<usize, usize> = [(input, 0)].into();
        let (coloring, spilled) = color_ranges(&adj, 3, &pins, &BTreeMap::new());
        assert!(spilled.is_empty());
        assert_eq!(coloring[&input], 0, "pinned input keeps its colour");
        for nb in &adj[&input] {
            assert_ne!(coloring[nb], 0, "neighbours avoid the pinned colour");
        }
    }

    #[test]
    fn apply_range_coloring_handles_register_swaps_simultaneously() {
        // movw r0,#1 ; movw r1,#2 ; add r2,r0,r1
        // Assignment swaps the two constants' registers (A:r0→R1, B:r1→R0).
        // Sequential single-pair renaming would alias them; the simultaneous
        // rewrite must produce: movw r1,#1 ; movw r0,#2 ; add r2,r1,r0.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 2,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        // vreg ids in replay order: 0 = movw r0's def, 1 = movw r1's def,
        // 2 = add's def.
        let assignment: BTreeMap<usize, Reg> = [(0, Reg::R1), (1, Reg::R0), (2, Reg::R2)].into();
        let out = apply_range_coloring(&seq, &assignment).expect("rewrites");
        assert_eq!(
            out[0].op,
            ArmOp::Movw {
                rd: Reg::R1,
                imm16: 1
            }
        );
        assert_eq!(
            out[1].op,
            ArmOp::Movw {
                rd: Reg::R0,
                imm16: 2
            }
        );
        assert_eq!(
            out[2].op,
            ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R1,
                op2: Operand2::Reg(Reg::R0)
            }
        );
    }

    #[test]
    fn apply_range_coloring_identity_is_a_noop() {
        // Assignment mapping every range back to its original register must
        // reproduce the input byte-for-byte.
        use crate::rules::MemAddr;
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Str {
                rd: Reg::R1,
                addr: MemAddr {
                    base: Reg::R11,
                    offset: 4,
                    offset_reg: None,
                },
            }),
        ];
        let ranges = straight_line_value_ranges(&seq).expect("straight-line");
        let identity: BTreeMap<usize, Reg> = ranges.iter().map(|r| (r.vreg, r.reg)).collect();
        let out = apply_range_coloring(&seq, &identity).expect("rewrites");
        assert_eq!(out, seq, "identity assignment is a no-op");
    }

    #[test]
    fn range_reallocation_end_to_end_shrinks_the_register_set() {
        // The full 3a pipeline on the spurious-spill miniature: ranges →
        // interference → colour at k=4 → rewrite. The input uses 7 distinct
        // physical registers; the re-allocated output must use at most 4 and
        // stay a valid straight-line program with the same value structure.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R3,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 2,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R4,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 3,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R5,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Add {
                rd: Reg::R6,
                rn: Reg::R3,
                op2: Operand2::Reg(Reg::R4),
            }),
            ins(ArmOp::Add {
                rd: Reg::R6,
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R5),
            }),
        ];
        let ranges = straight_line_value_ranges(&seq).expect("straight-line");
        let adj = range_interference(&ranges);
        let (coloring, spilled) = color_ranges(&adj, 4, &BTreeMap::new(), &BTreeMap::new());
        assert!(spilled.is_empty());
        // colour index → pool register R0..R3.
        let pool = [Reg::R0, Reg::R1, Reg::R2, Reg::R3];
        let assignment: BTreeMap<usize, Reg> =
            coloring.iter().map(|(v, c)| (*v, pool[*c])).collect();
        let out = apply_range_coloring(&seq, &assignment).expect("rewrites");
        // The rewritten program touches at most 4 physical registers.
        let used: BTreeSet<Reg> = out
            .iter()
            .flat_map(|i| {
                let e = reg_effect(&i.op).unwrap();
                e.defs.into_iter().chain(e.uses)
            })
            .collect();
        assert!(used.len() <= 4, "re-allocated set {used:?} exceeds k=4");
        // And it is still a well-formed straight-line program with the same
        // value structure (same number of ranges).
        let out_ranges = straight_line_value_ranges(&out).expect("still straight-line");
        assert_eq!(out_ranges.len(), ranges.len());
    }

    #[test]
    fn apply_range_coloring_declines_rmw_color_mismatch() {
        // movw r0 ; movt r0 — movt reads AND writes r0 (one field), so its
        // old and new ranges must land in the same register. An assignment
        // that splits them is declined, not guessed at.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Movt {
                rd: Reg::R0,
                imm16: 2,
            }),
        ];
        // vreg 0 = movw def, vreg 1 = movt's new range (its use hits vreg 0).
        let split: BTreeMap<usize, Reg> = [(0, Reg::R0), (1, Reg::R1)].into();
        assert_eq!(apply_range_coloring(&seq, &split), None);
        // The agreeing assignment rewrites fine.
        let agree: BTreeMap<usize, Reg> = [(0, Reg::R2), (1, Reg::R2)].into();
        let out = apply_range_coloring(&seq, &agree).expect("agreeing RMW ok");
        assert_eq!(
            out[1].op,
            ArmOp::Movt {
                rd: Reg::R2,
                imm16: 2
            }
        );
    }

    #[test]
    fn reallocate_function_pins_inputs_and_liveouts_and_reshuffles_internals() {
        // r5 carries TWO values: an interior one (born at 1, consumed at 2 —
        // neither an input nor r5's final range, so UNPINNED) and a final one
        // (born at 3 — live-out, pinned). The interior range is edge-free
        // after its dies-at-birth boundaries, so lowest-free re-colours it to
        // R0 (sharing with the r0 input is legal: that input dies exactly as
        // the interior value is born). Inputs/live-outs stay put.
        let seq = vec![
            ins(ArmOp::Add {
                rd: Reg::R5,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::R5),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R5,
                imm16: 3,
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R2),
            }),
        ];
        let pool = [
            Reg::R0,
            Reg::R1,
            Reg::R2,
            Reg::R3,
            Reg::R4,
            Reg::R5,
            Reg::R6,
            Reg::R7,
            Reg::R8,
        ];
        let (out, stats) = reallocate_function(&seq, &pool);
        assert_eq!(stats.segments, 1);
        assert_eq!(stats.reallocated, 1);
        // Wait — instruction 0 defines r5's INTERIOR value... at index 0, so
        // it is conservatively pinned as a def-0 range. The genuinely free
        // range is checked below only if the pass moved it; either way the
        // pinned ranges MUST be in place and the program structure preserved.
        match &out[3].op {
            ArmOp::Add { rd, rn, op2 } => {
                assert_eq!(*rd, Reg::R1, "live-out pinned to its register");
                assert_eq!(*rn, Reg::R5, "r5 final range (live-out) pinned");
                assert!(
                    matches!(op2, Operand2::Reg(_)),
                    "r2 value still read from a register"
                );
            }
            other => panic!("unexpected op {other:?}"),
        }
        // Structure preserved exactly.
        assert_eq!(out.len(), seq.len());
        assert_eq!(
            straight_line_value_ranges(&out).unwrap().len(),
            straight_line_value_ranges(&seq).unwrap().len()
        );
    }

    #[test]
    fn reallocate_function_passes_control_flow_through_verbatim() {
        // Two straight-line chunks separated by a label + branch: both chunks
        // are processed, the control flow is untouched, instruction count and
        // order are preserved.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 7,
            }),
            ins(ArmOp::Label {
                name: "L1".to_string(),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R5,
                imm16: 8,
            }),
            ins(ArmOp::B {
                label: "L1".to_string(),
            }),
        ];
        let pool = [Reg::R0, Reg::R1, Reg::R2, Reg::R3, Reg::R4, Reg::R5];
        let (out, stats) = reallocate_function(&seq, &pool);
        assert_eq!(out.len(), seq.len(), "no instruction added or removed");
        assert_eq!(stats.segments, 2);
        assert!(matches!(&out[1].op, ArmOp::Label { name } if name == "L1"));
        assert!(matches!(&out[3].op, ArmOp::B { label } if label == "L1"));
        // Single-instruction segments: the lone def is both instruction-0 def
        // and live-out → pinned to its own register → byte-identical.
        assert_eq!(out[0], seq[0]);
        assert_eq!(out[2], seq[2]);
    }

    #[test]
    fn reallocate_function_preserves_callee_saved_value_across_call() {
        // VCR-RA local-promotion fast-follow (#390, #242): the empirical question
        // the leaf-only v1 gate (PR #458) was set on — can the range-reallocator
        // move a promoted local's callee-saved home to a CALLER-saved register
        // that an intervening `bl` would clobber? This probes the reallocator
        // directly with the exact shape promotion+call produces.
        //
        // r5 carries a value DEFINED before a `Bl` and READ after it (a promoted
        // local live across a call). Segment A also has interior pressure (r6/r7)
        // to tempt the lowest-free colourer. The `Bl` is non-straight-line, so it
        // FLUSHES the segment (reallocate_function:2341) — segment A and segment B
        // are coloured independently, and r5's range in A is the last-opened range
        // for r5 ⇒ pinned as a live-out to its ORIGINAL register. So r5 must stay
        // r5 (callee-saved, survives the bl by AAPCS) across the boundary.
        use crate::rules::Reg::*;
        let seq = vec![
            ins(ArmOp::Movw { rd: R5, imm16: 42 }), // promoted local -> r5 (callee-saved)
            ins(ArmOp::Movw { rd: R6, imm16: 1 }),  // interior pressure
            ins(ArmOp::Add {
                rd: R6,
                rn: R6,
                op2: Operand2::Reg(R6),
            }), // r6 dies here
            ins(ArmOp::Bl {
                label: "helper".into(),
            }), // clobbers r0-r3,r12 — SPLITS segments
            ins(ArmOp::Add {
                rd: R0,
                rn: R5,
                op2: Operand2::Imm(7),
            }), // read r5 AFTER the call
        ];
        let pool = [R0, R1, R2, R3, R4, R5, R6, R7, R8];
        let (out, stats) = reallocate_function(&seq, &pool);

        // Structure preserved; the Bl passed through untouched at the boundary.
        assert_eq!(out.len(), seq.len());
        assert_eq!(
            stats.segments, 2,
            "the Bl splits the function into two segments"
        );
        assert!(matches!(&out[3].op, ArmOp::Bl { label } if label == "helper"));

        // The cross-call value's definition stays in a CALLEE-saved register
        // (r4..r8) — NOT remapped to a caller-saved reg the bl clobbers.
        let def_reg = match &out[0].op {
            ArmOp::Movw { rd, .. } => *rd,
            other => panic!("unexpected def op {other:?}"),
        };
        assert!(
            matches!(def_reg, R4 | R5 | R6 | R7 | R8),
            "cross-call value must stay callee-saved, got {def_reg:?}"
        );
        // And the post-call read reads that SAME register (the value survived).
        match &out[4].op {
            ArmOp::Add { rn, .. } => assert_eq!(
                *rn, def_reg,
                "post-call read must read the preserved register"
            ),
            other => panic!("unexpected read op {other:?}"),
        }
        // Specifically r5 (the live-out pin keeps the original register).
        assert_eq!(
            def_reg, R5,
            "live-out pinned to its original callee-saved reg"
        );
    }

    #[test]
    fn reallocate_function_keeps_reserved_registers_identity() {
        // A load through R11 (memory base, outside the pool): R11 must stay
        // R11 even though everything else is fair game.
        use crate::rules::MemAddr;
        let seq = vec![
            ins(ArmOp::Ldr {
                rd: Reg::R6,
                addr: MemAddr {
                    base: Reg::R11,
                    offset: 8,
                    offset_reg: None,
                },
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R6,
                op2: Operand2::Imm(1),
            }),
        ];
        let pool = [Reg::R0, Reg::R1, Reg::R2];
        let (out, _) = reallocate_function(&seq, &pool);
        match &out[0].op {
            ArmOp::Ldr { addr, .. } => {
                assert_eq!(addr.base, Reg::R11, "reserved base register untouched");
            }
            other => panic!("unexpected op {other:?}"),
        }
        match &out[1].op {
            ArmOp::Add { rd, .. } => assert_eq!(*rd, Reg::R0, "live-out pinned"),
            other => panic!("unexpected op {other:?}"),
        }
    }

    #[test]
    fn reallocate_function_is_sound_and_near_identity_on_packed_greedy_code() {
        // On greedy code with NO spills and NO duplicate constants, the
        // conservative pass (inputs + per-register live-outs pinned) has
        // little freedom — the honest property is SOUNDNESS, not shrinkage.
        //
        // VCR-RA-003 UPDATE: the backward-dataflow validator found that the
        // colourer's candidate rewrite for THIS segment relocates the first
        // r6 value onto r0 AFTER r0's pinned last range dies (dies-at-birth
        // non-interference), changing r0's EXIT value (3 → r3+r4). For a
        // mid-function segment a downstream read of r0 would then be a
        // miscompile — the pinning protects where the last range LIVES, not
        // the register's exit state. The validator therefore REJECTS the
        // rewrite and the pass keeps the original bytes: soundness is now
        // FULL identity here, enforced by the gate rather than assumed.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R3,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 2,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R4,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 3,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R5,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Add {
                rd: Reg::R6,
                rn: Reg::R3,
                op2: Operand2::Reg(Reg::R4),
            }),
            ins(ArmOp::Add {
                rd: Reg::R6,
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R5),
            }),
        ];
        let pool = [
            Reg::R0,
            Reg::R1,
            Reg::R2,
            Reg::R3,
            Reg::R4,
            Reg::R5,
            Reg::R6,
            Reg::R7,
            Reg::R8,
        ];
        let (out, stats) = reallocate_function(&seq, &pool);
        assert_eq!(stats.segments, 1);
        assert_eq!(
            stats.validator_rejects, 1,
            "the exit-state-changing candidate rewrite must be caught"
        );
        assert_eq!(stats.reallocated, 0);
        // The rejected segment passes through byte-identical — the safe
        // fallback IS the original greedy code.
        assert_eq!(out, seq);
    }

    fn prologue() -> ArmInstruction {
        ins(ArmOp::Push {
            regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::LR],
        })
    }
    fn epilogue() -> ArmInstruction {
        ins(ArmOp::Pop {
            regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC],
        })
    }

    #[test]
    fn shrink_saves_drops_dead_callee_saved_and_pads_even() {
        // Body lives entirely in r0/r1 (the post-realloc filter shape): all of
        // r4-r8 are dead, so the save list shrinks to {r4(pad), lr} — padded
        // to an even count to preserve the 8-byte AAPCS SP alignment.
        let seq = vec![
            prologue(),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            epilogue(),
        ];
        let out = shrink_callee_saved_saves(&seq).expect("shrinks");
        assert_eq!(
            out[0].op,
            ArmOp::Push {
                regs: vec![Reg::R4, Reg::LR]
            }
        );
        assert_eq!(
            out[3].op,
            ArmOp::Pop {
                regs: vec![Reg::R4, Reg::PC]
            }
        );
        // Body untouched.
        assert_eq!(out[1], seq[1]);
        assert_eq!(out[2], seq[2]);
    }

    #[test]
    fn shrink_saves_keeps_used_callee_saved() {
        // Body uses r5: the save list keeps it ({r5, lr} = even, no padding).
        let seq = vec![
            prologue(),
            ins(ArmOp::Add {
                rd: Reg::R5,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(Reg::R5),
            }),
            epilogue(),
        ];
        let out = shrink_callee_saved_saves(&seq).expect("shrinks");
        assert_eq!(
            out[0].op,
            ArmOp::Push {
                regs: vec![Reg::R5, Reg::LR]
            }
        );
    }

    #[test]
    fn shrink_saves_declines_on_calls_sp_and_brtable() {
        use crate::rules::MemAddr;
        // Call in body → not a leaf → decline.
        let with_call = vec![
            prologue(),
            ins(ArmOp::Bl {
                label: "func_1".to_string(),
            }),
            epilogue(),
        ];
        assert_eq!(shrink_callee_saved_saves(&with_call), None);
        // SP-relative store → frame offsets would shift → decline.
        let with_sp = vec![
            prologue(),
            ins(ArmOp::Str {
                rd: Reg::R0,
                addr: MemAddr {
                    base: Reg::SP,
                    offset: 4,
                    offset_reg: None,
                },
            }),
            epilogue(),
        ];
        assert_eq!(shrink_callee_saved_saves(&with_sp), None);
        // BrTable reads an index register invisibly to reg_effect → decline.
        let with_brtable = vec![
            prologue(),
            ins(ArmOp::BrTable {
                rd: Reg::R1,
                index_reg: Reg::R0,
                targets: vec![],
                default: 0,
            }),
            epilogue(),
        ];
        assert_eq!(shrink_callee_saved_saves(&with_brtable), None);
    }

    #[test]
    fn shrink_saves_handles_multiple_epilogues_and_branches() {
        // Two return paths + a label/branch between them: both pops shrink
        // identically, control flow untouched.
        let seq = vec![
            prologue(),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::B {
                label: "L_end".to_string(),
            }),
            epilogue(),
            ins(ArmOp::Label {
                name: "L_end".to_string(),
            }),
            epilogue(),
        ];
        let out = shrink_callee_saved_saves(&seq).expect("shrinks");
        for i in [3usize, 5] {
            assert_eq!(
                out[i].op,
                ArmOp::Pop {
                    regs: vec![Reg::R4, Reg::PC]
                }
            );
        }
        assert_eq!(out[2], seq[2]);
        assert_eq!(out[4], seq[4]);
    }

    // ---- ensure_callee_saved_prologue (#490) ----

    #[test]
    fn ensure_prologue_wraps_body_that_touches_callee_saved() {
        // Optimized-path shape: no prologue, body writes r4/r5, returns via bx lr.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R4,
                imm16: 100,
            }),
            ins(ArmOp::Add {
                rd: Reg::R5,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R4),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(Reg::R5),
            }),
            ins(ArmOp::Bx { rm: Reg::LR }),
        ];
        let out = ensure_callee_saved_prologue(&seq);
        assert_eq!(
            out[0].op,
            ArmOp::Push {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::LR]
            }
        );
        assert_eq!(
            out.last().unwrap().op,
            ArmOp::Pop {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC]
            }
        );
        // Body untouched between the new prologue and epilogue.
        assert_eq!(out[1..=3], seq[0..=2]);
        // And shrink then sizes it to the registers actually used ({r4,r5} → pad).
        let shrunk = shrink_callee_saved_saves(&out).expect("shrinks");
        assert_eq!(
            shrunk[0].op,
            ArmOp::Push {
                regs: vec![Reg::R4, Reg::R5, Reg::R6, Reg::LR]
            }
        );
    }

    #[test]
    fn ensure_prologue_leaves_callee_saved_free_leaf_untouched() {
        // Pure r0-r3 leaf: no callee-saved register touched → no push added
        // (a spurious push would be permanent — shrink never removes one).
        let seq = vec![
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Bx { rm: Reg::LR }),
        ];
        assert_eq!(ensure_callee_saved_prologue(&seq), seq);
        assert!(!body_uses_callee_saved(&seq));
    }

    #[test]
    fn ensure_prologue_is_conservative_on_unmodeled_ops() {
        // An op reg_effect cannot model (here a Bl call) might clobber a
        // callee-saved register → force the push (fail-safe). shrink then
        // declines on the call and leaves the full save.
        let seq = vec![
            ins(ArmOp::Bl {
                label: "func_1".to_string(),
            }),
            ins(ArmOp::Bx { rm: Reg::LR }),
        ];
        assert!(body_uses_callee_saved(&seq));
        let out = ensure_callee_saved_prologue(&seq);
        assert!(matches!(&out[0].op, ArmOp::Push { regs } if regs.contains(&Reg::LR)));
        assert_eq!(shrink_callee_saved_saves(&out), None);
    }

    #[test]
    fn ensure_prologue_skips_body_that_already_has_one() {
        // Direct-path output already carries its own `push {…,lr}` → no-op
        // (shrink owns sizing it; double-wrapping would corrupt the frame).
        let seq = vec![
            prologue(),
            ins(ArmOp::Add {
                rd: Reg::R5,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            epilogue(),
        ];
        assert_eq!(ensure_callee_saved_prologue(&seq), seq);
    }

    // ---- elide_dead_frame (VCR-RA-002, #390) ----

    fn frame_sub(n: i32) -> ArmInstruction {
        ins(ArmOp::Sub {
            rd: Reg::SP,
            rn: Reg::SP,
            op2: Operand2::Imm(n),
        })
    }
    fn frame_add(n: i32) -> ArmInstruction {
        ins(ArmOp::Add {
            rd: Reg::SP,
            rn: Reg::SP,
            op2: Operand2::Imm(n),
        })
    }

    #[test]
    fn elide_dead_frame_removes_unreferenced_frame() {
        // Promoted-leaf shape: a `sub sp,#16` reserves slots for locals that all
        // live in registers; the body never touches SP. The frame is dead.
        let body_a = ins(ArmOp::Add {
            rd: Reg::R4,
            rn: Reg::R0,
            op2: Operand2::Imm(1),
        });
        let body_b = ins(ArmOp::Mov {
            rd: Reg::R0,
            op2: Operand2::Reg(Reg::R4),
        });
        let seq = vec![
            prologue(),
            frame_sub(16),
            body_a.clone(),
            body_b.clone(),
            frame_add(16),
            epilogue(),
        ];
        let out = elide_dead_frame(&seq).expect("dead frame elided");
        // sub/add sp gone; everything else verbatim and in order.
        assert_eq!(
            out,
            vec![prologue(), body_a, body_b, epilogue()],
            "only the sub/add sp pair is removed"
        );
    }

    #[test]
    fn elide_dead_frame_declines_on_sp_relative_access() {
        use crate::rules::MemAddr;
        // A spill/local lives in the frame → `[sp,#off]` access → frame is LIVE.
        let seq = vec![
            prologue(),
            frame_sub(16),
            ins(ArmOp::Str {
                rd: Reg::R0,
                addr: MemAddr {
                    base: Reg::SP,
                    offset: 4,
                    offset_reg: None,
                },
            }),
            frame_add(16),
            epilogue(),
        ];
        assert_eq!(elide_dead_frame(&seq), None);
    }

    #[test]
    fn elide_dead_frame_declines_on_unbalanced_add_sp() {
        // An `add sp,#8` that does not match the `sub sp,#16` is some other SP
        // arithmetic, not the frame's counterpart → decline conservatively.
        let seq = vec![
            prologue(),
            frame_sub(16),
            ins(ArmOp::Mov {
                rd: Reg::R4,
                op2: Operand2::Imm(0),
            }),
            frame_add(8),
            epilogue(),
        ];
        assert_eq!(elide_dead_frame(&seq), None);
    }

    #[test]
    fn elide_dead_frame_declines_on_unmodeled_sp_effect() {
        // A call sits inside the frame: `reg_effect` declines `Bl` (its SP/clobber
        // effect is not modeled), so we cannot prove the frame dead → decline.
        let seq = vec![
            prologue(),
            frame_sub(16),
            ins(ArmOp::Bl {
                label: "func_1".to_string(),
            }),
            frame_add(16),
            epilogue(),
        ];
        assert_eq!(elide_dead_frame(&seq), None);
    }

    #[test]
    fn elide_dead_frame_noop_when_no_frame() {
        // No `sub sp` at all (frame_size == 0) → nothing to elide.
        let seq = vec![
            prologue(),
            ins(ArmOp::Add {
                rd: Reg::R4,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            epilogue(),
        ];
        assert_eq!(elide_dead_frame(&seq), None);
    }

    #[test]
    fn elide_dead_frame_removes_across_multiple_epilogues() {
        // Two return paths each restore the frame; both `add sp` are removed.
        let seq = vec![
            prologue(),
            frame_sub(8),
            ins(ArmOp::B {
                label: "L_end".to_string(),
            }),
            frame_add(8),
            epilogue(),
            ins(ArmOp::Label {
                name: "L_end".to_string(),
            }),
            frame_add(8),
            epilogue(),
        ];
        let out = elide_dead_frame(&seq).expect("dead frame elided");
        assert_eq!(
            out,
            vec![
                prologue(),
                ins(ArmOp::B {
                    label: "L_end".to_string(),
                }),
                epilogue(),
                ins(ArmOp::Label {
                    name: "L_end".to_string(),
                }),
                epilogue(),
            ],
        );
    }

    #[test]
    fn precolored_node_keeps_its_colour_and_constrains_neighbours() {
        // Triangle R0—R1—R2; pin R0 to colour 2. With k=3, R1/R2 must avoid 2
        // (and each other), so they take {0,1}.
        let g = clique(&[Reg::R0, Reg::R1, Reg::R2]);
        let pre = BTreeMap::from([(Reg::R0, 2usize)]);
        match color_graph_precolored(&g, 3, &pre) {
            ColorResult::Colored(c) => {
                assert_eq!(c[&Reg::R0], 2, "precoloured node keeps its colour");
                assert_ne!(c[&Reg::R1], 2);
                assert_ne!(c[&Reg::R2], 2);
                assert_ne!(c[&Reg::R1], c[&Reg::R2]);
            }
            ColorResult::Spilled(s) => panic!("3-colourable with the pin, got {s:?}"),
        }
    }

    #[test]
    fn precoloring_can_force_a_spill_by_exhausting_colours() {
        // R2 interferes with R0 and R1; pin R0=0, R1=1. With only k=2 colours
        // both are taken in R2's neighbourhood → R2 must spill, even though the
        // bare graph (a path) is 2-colourable without the pins.
        let mut g = InterferenceGraph::default();
        g.add_edge(Reg::R2, Reg::R0);
        g.add_edge(Reg::R2, Reg::R1);
        let pre = BTreeMap::from([(Reg::R0, 0usize), (Reg::R1, 1usize)]);
        match color_graph_precolored(&g, 2, &pre) {
            ColorResult::Spilled(s) => assert!(s.contains(&Reg::R2)),
            ColorResult::Colored(c) => panic!("R2 has no free colour, got {c:?}"),
        }
        // One more colour resolves it: R2 takes colour 2.
        match color_graph_precolored(&g, 3, &pre) {
            ColorResult::Colored(c) => assert_eq!(c[&Reg::R2], 2),
            ColorResult::Spilled(s) => panic!("k=3 leaves a free colour, got {s:?}"),
        }
    }

    #[test]
    fn color_graph_delegates_to_empty_precoloring() {
        // The plain entry point must agree with the precoloured one given no pins.
        let g = clique(&[Reg::R0, Reg::R1, Reg::R2, Reg::R3]);
        assert_eq!(
            color_graph(&g, 4),
            color_graph_precolored(&g, 4, &BTreeMap::new())
        );
    }

    // ---- Allocation verifier (verify_allocation) ---------------------------

    #[test]
    fn verify_allocation_accepts_color_graph_output() {
        // The producer and the checker must agree: any colouring color_graph
        // returns verifies clean. (Independent code paths → real cross-check.)
        for regs in [
            vec![Reg::R0, Reg::R1, Reg::R2],
            vec![Reg::R0, Reg::R1, Reg::R2, Reg::R3],
        ] {
            let g = clique(&regs);
            let k = regs.len();
            match color_graph(&g, k) {
                ColorResult::Colored(c) => {
                    assert_eq!(verify_allocation(&g, &c), Ok(()));
                }
                ColorResult::Spilled(s) => panic!("clique is k-colourable, got {s:?}"),
            }
        }
    }

    #[test]
    fn verify_allocation_rejects_interfering_same_colour() {
        // R0—R1 interfere but are both assigned colour 0 → SameColor.
        let mut g = InterferenceGraph::default();
        g.add_edge(Reg::R0, Reg::R1);
        let bad = BTreeMap::from([(Reg::R0, 0usize), (Reg::R1, 0usize)]);
        match verify_allocation(&g, &bad) {
            Err(AllocationConflict::SameColor { color, .. }) => assert_eq!(color, 0),
            other => panic!("expected SameColor, got {other:?}"),
        }
    }

    #[test]
    fn verify_allocation_rejects_unassigned_node() {
        // R1 is in the graph but missing from the assignment → Unassigned.
        let mut g = InterferenceGraph::default();
        g.add_edge(Reg::R0, Reg::R1);
        let partial = BTreeMap::from([(Reg::R0, 0usize)]);
        assert_eq!(
            verify_allocation(&g, &partial),
            Err(AllocationConflict::Unassigned(Reg::R1))
        );
    }

    // ---- Allocator driver (allocate_function) ------------------------------

    #[test]
    fn allocate_function_produces_a_valid_allocation_and_counts_remat() {
        // movw r0,#7 ; mov r1,r0 ; movw r2,#7  — r2's #7 is redundant (resident
        // in r0). The driver allocates a valid colouring and reports 1 remat
        // opportunity (the #209 const-CSE headroom).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 7,
            }),
        ];
        match allocate_function(&seq, 9, &BTreeMap::new()) {
            AllocationOutcome::Allocated {
                coloring,
                remat_opportunities,
            } => {
                let g = interference_graph(&seq).unwrap();
                assert_eq!(verify_allocation(&g, &coloring), Ok(()));
                assert_eq!(remat_opportunities, 1, "the resident #7 is CSE-able");
            }
            other => panic!("expected Allocated, got {other:?}"),
        }
    }

    #[test]
    fn peak_pressure_counts_simultaneously_live_values_not_physical_regs() {
        // movw r0,#1 ; movw r1,#2 ; movw r2,#3 ; add r3,r0,r1 ; add r4,r2,r3
        // At the third movw, v0/v1/v2 are all live → peak 3. (The point: this is
        // value pressure; physical-register reuse would not change it.)
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 2,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 3,
            }),
            ins(ArmOp::Add {
                rd: Reg::R3,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Add {
                rd: Reg::R4,
                rn: Reg::R2,
                op2: Operand2::Reg(Reg::R3),
            }),
        ];
        assert_eq!(straight_line_peak_pressure(&seq), Some(3));
        assert_eq!(function_peak_pressure(&seq), 3);
    }

    #[test]
    fn const_cse_folds_a_redundant_clamp_bound_into_the_resident_register() {
        // movw r0,#0x7e ; cmp r5,r0 ; movw r1,#0x7e ; cmp r6,r1 ; movw r1,#99
        // r1's #0x7e is redundant (r0 holds it); r1 is redefined (movw #99) so its
        // value is local → fold: drop `movw r1,#0x7e`, rewrite `cmp r6,r1`→`cmp r6,r0`.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7e,
            }),
            ins(ArmOp::Cmp {
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 0x7e,
            }),
            ins(ArmOp::Cmp {
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 99,
            }),
        ];
        let (out, removed) = apply_const_cse(&seq);
        assert_eq!(removed, 1, "the redundant movw r1,#0x7e is dropped");
        assert_eq!(out.len(), 4);
        // The cmp on r6 now reads the resident r0.
        assert!(out.iter().any(|i| matches!(
            &i.op,
            ArmOp::Cmp {
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R0)
            }
        )));
        // The original movw r1,#0x7e is gone; the later movw r1,#99 stays.
        assert!(!out.iter().any(|i| matches!(
            &i.op,
            ArmOp::Movw {
                rd: Reg::R1,
                imm16: 0x7e
            }
        )));
        assert!(out.iter().any(|i| matches!(
            &i.op,
            ArmOp::Movw {
                rd: Reg::R1,
                imm16: 99
            }
        )));
    }

    #[test]
    fn const_cse_declines_when_resident_register_is_clobbered_before_use() {
        // movw r0,#7 ; movw r1,#7 ; movw r0,#3 (clobbers r0) ; add r2,r4,r1 ; movw r1,#9
        // r1's #7 is "resident in r0" at def, but r0 is overwritten before r1's
        // use → folding would read the wrong r0 → must NOT fold.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 3,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R4,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 9,
            }),
        ];
        let (_out, removed) = apply_const_cse(&seq);
        assert_eq!(removed, 0, "resident reg clobbered before use → no fold");
    }

    #[test]
    fn const_cse_declines_when_value_may_be_live_out_of_segment() {
        // movw r0,#7 ; movw r1,#7 ; add r2,r4,r1   (r1 never redefined → its #7
        // may be live past the segment) → conservatively do not fold.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 7,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 7,
            }),
            ins(ArmOp::Add {
                rd: Reg::R2,
                rn: Reg::R4,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let (_out, removed) = apply_const_cse(&seq);
        assert_eq!(
            removed, 0,
            "rd not redefined in segment → may be live-out → no fold"
        );
    }

    #[test]
    fn const_cse_size_guard_declines_when_retarget_flips_16bit_to_32bit() {
        // #242 size guard (non-vacuity proof, half 1 of 2). A const resident in a
        // HIGH register (r8) is re-materialized in a LOW register (r3) and used as
        // the base of three 16-bit `ldr`s. Retargeting r3→r8 flips each `ldr` to
        // its 32-bit form (low base <8 ⇒ 2 B, base r8 ⇒ 4 B): +2 B × 3 = +6 B,
        // versus the −4 B saved by dropping the redundant `movw r3`. Net +2 B, so
        // the guard must DECLINE the whole segment and keep every materialization.
        let mem = |b: Reg, o: i32| crate::rules::MemAddr {
            base: b,
            offset: o,
            offset_reg: None,
        };
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R8,
                imm16: 100,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 100,
            }),
            ins(ArmOp::Ldr {
                rd: Reg::R0,
                addr: mem(Reg::R3, 0),
            }),
            ins(ArmOp::Ldr {
                rd: Reg::R1,
                addr: mem(Reg::R3, 4),
            }),
            ins(ArmOp::Ldr {
                rd: Reg::R2,
                addr: mem(Reg::R3, 8),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 5,
            }),
        ];
        let (out, removed) = apply_const_cse(&seq);
        assert_eq!(
            removed, 0,
            "guard declines: retarget would grow the segment"
        );
        assert_eq!(
            out, seq,
            "declined segment is returned byte-for-byte unchanged"
        );
    }

    #[test]
    fn const_cse_size_guard_commits_when_retarget_keeps_16bit_encoding() {
        // #242 size guard (non-vacuity proof, half 2 of 2). IDENTICAL structure to
        // the decline test, except the resident register is LOW (r2): retargeting
        // r3→r2 keeps every `ldr` 16-bit (base still <8), so the segment shrinks by
        // the dropped `movw` (−4 B) and the guard COMMITS. This isolates the guard
        // to the encoding-width effect — the only difference is the register class.
        let mem = |b: Reg, o: i32| crate::rules::MemAddr {
            base: b,
            offset: o,
            offset_reg: None,
        };
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 100,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 100,
            }),
            ins(ArmOp::Ldr {
                rd: Reg::R0,
                addr: mem(Reg::R3, 0),
            }),
            ins(ArmOp::Ldr {
                rd: Reg::R1,
                addr: mem(Reg::R3, 4),
            }),
            ins(ArmOp::Ldr {
                rd: Reg::R4,
                addr: mem(Reg::R3, 8),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 5,
            }),
        ];
        let (out, removed) = apply_const_cse(&seq);
        assert_eq!(
            removed, 1,
            "guard commits: retarget keeps the segment smaller"
        );
        // The three loads now read the resident r2.
        assert_eq!(
            out.iter()
                .filter(|i| matches!(&i.op, ArmOp::Ldr { addr, .. } if addr.base == Reg::R2))
                .count(),
            3,
            "all three loads retargeted to the low resident register r2"
        );
    }

    #[test]
    fn const_units_reconstructs_a_32bit_movw_movt_pair() {
        // #242 PR2 item 1: a `movw r0,#lo ; movt r0,#hi` pair is one 32-bit unit;
        // a lone `movw` / a `movt` to a different reg is not folded.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 0x7960,
            }),
            ins(ArmOp::Movt {
                rd: Reg::R0,
                imm16: 0xFFFE,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 42,
            }),
        ];
        let units = const_units(&seq);
        assert_eq!(units.len(), 2, "the pair + the lone movw");
        assert_eq!((units[0].rd, units[0].len), (Reg::R0, 2));
        assert_eq!(
            units[0].value, -100000,
            "0xFFFE7960 reconstructs to -100000 as i32"
        );
        assert_eq!(
            (units[1].rd, units[1].len, units[1].value),
            (Reg::R1, 1, 42)
        );
    }

    #[test]
    fn const_cse_hoists_a_same_register_reuse_into_a_free_register_242() {
        // #242 PR2 win recovery: `movw r2,#500` is materialized into r2, r2 is
        // clobbered (to #9) between uses, then #500 is re-materialized into r2 —
        // the SAME register, so Pass 1 misses it (no register
        // holds 500 at the reuse). The extending-alias hoist pins 500 in a FREE
        // register (r0), drops the repeat, and retargets both uses. r2 is redefined
        // at the end (#1) so its value is local.
        let add = |rd, rn| {
            ins(ArmOp::Add {
                rd,
                rn,
                op2: Operand2::Reg(rn),
            })
        };
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 500,
            }),
            add(Reg::R3, Reg::R2),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 9,
            }),
            add(Reg::R4, Reg::R2),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 500,
            }),
            add(Reg::R5, Reg::R2),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 1,
            }),
        ];
        let (out, removed) = apply_const_cse(&seq);
        assert_eq!(removed, 1, "the repeat `movw r2,#500` is dropped");
        // Exactly one `movw _,#500` survives, into a register other than r2.
        let mats: Vec<Reg> = out
            .iter()
            .filter_map(|i| match &i.op {
                ArmOp::Movw { rd, imm16: 500 } => Some(*rd),
                _ => None,
            })
            .collect();
        assert_eq!(mats.len(), 1, "one hoisted materialization of 500 remains");
        let rf = mats[0];
        assert_ne!(rf, Reg::R2, "hoisted into a free register, not r2");
        // Both const-uses read the hoisted register, not the clobbered r2.
        assert_eq!(
            out.iter()
                .filter(
                    |i| matches!(&i.op, ArmOp::Add { rn, op2: Operand2::Reg(m), .. }
                    if *rn == rf && *m == rf)
                )
                .count(),
            2,
            "both `add _,500,500` uses retargeted to the hoisted register"
        );
    }

    #[test]
    fn const_cse_hoist_declines_when_value_is_live_out_of_segment_242() {
        // Same shape but WITHOUT the trailing redefine of r2 — the last `movw
        // r2,#500` leaves 500 live-out of the segment, so dropping it would strand
        // a later read of r2. The hoist must decline (locality guard).
        let add = |rd, rn| {
            ins(ArmOp::Add {
                rd,
                rn,
                op2: Operand2::Reg(rn),
            })
        };
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 500,
            }),
            add(Reg::R3, Reg::R2),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 9,
            }),
            add(Reg::R4, Reg::R2),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 500,
            }),
            add(Reg::R5, Reg::R2),
        ];
        let (_out, removed) = apply_const_cse(&seq);
        assert_eq!(removed, 0, "value live-out → hoist declines");
    }

    #[test]
    fn value_ranges_split_a_reused_physical_register_into_distinct_vregs() {
        // movw r1,#1 ; mov r0,r1 ; movw r1,#2 ; mov r2,r1
        // R1 holds two unrelated values → two distinct virtual registers. This
        // is the split that turns the overloaded physical-reg node (one spurious
        // spill) into separately-colourable values.
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 1,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 2,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::R1),
            }),
        ];
        let ranges = straight_line_value_ranges(&seq).expect("straight-line");
        let r1_ranges: Vec<_> = ranges.iter().filter(|r| r.reg == Reg::R1).collect();
        assert_eq!(
            r1_ranges.len(),
            2,
            "R1 splits into two virtual registers (one per value)"
        );
        // First R1 range: def 0, last-used at 1 (the mov r0,r1).
        assert_eq!((r1_ranges[0].def, r1_ranges[0].last_use), (0, 1));
        // Second R1 range: def 2, last-used at 3 (the mov r2,r1).
        assert_eq!((r1_ranges[1].def, r1_ranges[1].last_use), (2, 3));
    }

    #[test]
    fn peak_pressure_unaffected_by_physical_register_reuse() {
        // The same value churned through ONE physical register has pressure 1 —
        // exactly the case the physical-register interference graph overstates.
        // movw r0,#1 ; mov r1,r0 ; movw r0,#2 ; mov r2,r0  → never >1 live at once
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Reg(Reg::R0),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 2,
            }),
            ins(ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::R0),
            }),
        ];
        // r0 holds two different values sequentially; peak simultaneous = 1.
        assert_eq!(straight_line_peak_pressure(&seq), Some(1));
    }

    #[test]
    fn allocate_function_declines_on_unmodeled_construct() {
        let seq = vec![ins(ArmOp::Bl { label: "f".into() })];
        assert_eq!(
            allocate_function(&seq, 9, &BTreeMap::new()),
            AllocationOutcome::Declined
        );
    }

    #[test]
    fn allocate_function_spills_when_pool_too_small() {
        // A K4 clique of registers needs 4 colours; with k=3 the driver reports
        // a spill rather than hard-failing (the whole point of VCR-RA-001).
        let seq = vec![
            ins(ArmOp::Movw {
                rd: Reg::R0,
                imm16: 1,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 2,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 3,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R3,
                imm16: 4,
            }),
            // one instruction reading all four → all four simultaneously live
            ins(ArmOp::Add {
                rd: Reg::R4,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Add {
                rd: Reg::R4,
                rn: Reg::R2,
                op2: Operand2::Reg(Reg::R3),
            }),
        ];
        // k=2 cannot colour 3+ simultaneously-live values → spill, not crash.
        assert!(matches!(
            allocate_function(&seq, 2, &BTreeMap::new()),
            AllocationOutcome::NeedsSpill(_)
        ));
    }

    #[test]
    fn verify_allocation_accepts_a_nonadjacent_shared_colour() {
        // R0 and R2 do NOT interfere (a path R0—R1—R2), so they may share a
        // colour: {R0:0, R1:1, R2:0} is valid.
        let mut g = InterferenceGraph::default();
        g.add_edge(Reg::R0, Reg::R1);
        g.add_edge(Reg::R1, Reg::R2);
        let ok = BTreeMap::from([(Reg::R0, 0usize), (Reg::R1, 1usize), (Reg::R2, 0usize)]);
        assert_eq!(verify_allocation(&g, &ok), Ok(()));
    }

    // =====================================================================
    // VCR-RA-003: backward-dataflow translation validator
    // =====================================================================

    use crate::rules::MemAddr;

    const VPOOL: [Reg; 9] = [
        Reg::R0,
        Reg::R1,
        Reg::R2,
        Reg::R3,
        Reg::R4,
        Reg::R5,
        Reg::R6,
        Reg::R7,
        Reg::R8,
    ];

    /// A #209-style int8 clamp chain: cmp + SelectMove (RMW) + store, with an
    /// internal temp. Inputs: r0 (value), r11 (reserved base).
    fn clamp_segment() -> Vec<ArmInstruction> {
        vec![
            ins(ArmOp::Movw {
                rd: Reg::R2,
                imm16: 127,
            }),
            ins(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R2),
            }),
            ins(ArmOp::SelectMove {
                rd: Reg::R0,
                rm: Reg::R2,
                cond: Condition::GT,
            }),
            ins(ArmOp::Mvn {
                rd: Reg::R3,
                op2: Operand2::Imm(127),
            }),
            ins(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R3),
            }),
            ins(ArmOp::SelectMove {
                rd: Reg::R0,
                rm: Reg::R3,
                cond: Condition::LT,
            }),
            ins(ArmOp::Strb {
                rd: Reg::R0,
                addr: MemAddr::imm(Reg::R11, 4),
            }),
        ]
    }

    /// Umull reciprocal-mult shape (#209 Opt 1b) + a shifted-operand add.
    fn umull_segment() -> Vec<ArmInstruction> {
        vec![
            ins(ArmOp::Movw {
                rd: Reg::R1,
                imm16: 52429,
            }),
            ins(ArmOp::Movt {
                rd: Reg::R1,
                imm16: 52428,
            }),
            ins(ArmOp::Umull {
                rdlo: Reg::R2,
                rdhi: Reg::R3,
                rn: Reg::R0,
                rm: Reg::R1,
            }),
            ins(ArmOp::Lsr {
                rd: Reg::R4,
                rn: Reg::R3,
                shift: 2,
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R4,
                op2: Operand2::RegShift {
                    rm: Reg::R2,
                    shift: crate::rules::ShiftType::LSR,
                    amount: 31,
                },
            }),
        ]
    }

    /// Indexed loads/stores through the reserved memory base + ALU.
    fn loadstore_segment() -> Vec<ArmInstruction> {
        vec![
            ins(ArmOp::Ldr {
                rd: Reg::R3,
                addr: MemAddr {
                    base: Reg::R11,
                    offset: 0,
                    offset_reg: Some(Reg::R1),
                },
            }),
            ins(ArmOp::Ldr {
                rd: Reg::R4,
                addr: MemAddr::imm(Reg::R11, 8),
            }),
            ins(ArmOp::Add {
                rd: Reg::R5,
                rn: Reg::R3,
                op2: Operand2::Reg(Reg::R4),
            }),
            ins(ArmOp::Str {
                rd: Reg::R5,
                addr: MemAddr {
                    base: Reg::R11,
                    offset: 0,
                    offset_reg: Some(Reg::R1),
                },
            }),
        ]
    }

    /// Compare/flag-materialize/sign-extend chain (defless flag-setter, a
    /// flags-only def, unary ops).
    fn setcond_segment() -> Vec<ArmInstruction> {
        vec![
            ins(ArmOp::Sub {
                rd: Reg::R3,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }),
            ins(ArmOp::Cmp {
                rn: Reg::R3,
                op2: Operand2::Imm(0),
            }),
            ins(ArmOp::SetCond {
                rd: Reg::R4,
                cond: Condition::EQ,
            }),
            ins(ArmOp::Sxtb {
                rd: Reg::R5,
                rm: Reg::R4,
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R4,
                op2: Operand2::Reg(Reg::R5),
            }),
        ]
    }

    /// The reshuffle-prone shape from
    /// `reallocate_function_pins_inputs_and_liveouts_and_reshuffles_internals`:
    /// r5 carries two values, the interior one re-colourable.
    fn reshuffle_segment() -> Vec<ArmInstruction> {
        vec![
            ins(ArmOp::Add {
                rd: Reg::R5,
                rn: Reg::R0,
                op2: Operand2::Imm(1),
            }),
            ins(ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::R5),
            }),
            ins(ArmOp::Movw {
                rd: Reg::R5,
                imm16: 3,
            }),
            ins(ArmOp::Add {
                rd: Reg::R1,
                rn: Reg::R5,
                op2: Operand2::Reg(Reg::R2),
            }),
        ]
    }

    /// Contains a DEAD def (movw r6 overwritten unused) — the documented
    /// survivor class for redirect mutations — plus an input use (r1).
    fn dead_def_segment() -> Vec<ArmInstruction> {
        vec![
            ins(ArmOp::Movw {
                rd: Reg::R6,
                imm16: 1,
            }),
            ins(ArmOp::Movw {
                rd: Reg::R6,
                imm16: 2,
            }),
            ins(ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R6,
                op2: Operand2::Reg(Reg::R1),
            }),
        ]
    }

    #[test]
    fn validator_accepts_identity_rewrites() {
        for seg in [
            clamp_segment(),
            umull_segment(),
            loadstore_segment(),
            setcond_segment(),
            reshuffle_segment(),
            dead_def_segment(),
        ] {
            assert_eq!(validate_segment_rewrite(&seg, &seg.clone()), Ok(()));
        }
    }

    #[test]
    fn validator_accepts_every_rewrite_the_pass_produces() {
        // Criterion 1 (segment level): whatever try_reallocate_segment emits
        // must validate. (The wiring itself enforces this — a reject would
        // surface as ValidatorRejected — so here we call the validator
        // directly on the pass output to make the property explicit.)
        for seg in [
            clamp_segment(),
            umull_segment(),
            loadstore_segment(),
            setcond_segment(),
            reshuffle_segment(),
            dead_def_segment(),
        ] {
            if let SegmentOutcome::Rewritten(new) = try_reallocate_segment(&seg, &VPOOL) {
                assert_eq!(
                    validate_segment_rewrite(&seg, &new),
                    Ok(()),
                    "pass output must validate for {seg:?} -> {new:?}"
                );
            }
        }
    }

    #[test]
    fn validator_rejects_length_mismatch() {
        let seg = reshuffle_segment();
        let mut shorter = seg.clone();
        shorter.pop();
        assert_eq!(
            validate_segment_rewrite(&seg, &shorter),
            Err(RewriteViolation::LengthMismatch {
                orig: 4,
                rewritten: 3
            })
        );
    }

    #[test]
    fn validator_rejects_shape_mismatch() {
        // Same opcode, different immediate — a renames-only rewrite cannot
        // change a constant.
        let seg = reshuffle_segment();
        let mut rew = seg.clone();
        rew[2].op = ArmOp::Movw {
            rd: Reg::R5,
            imm16: 4,
        };
        assert_eq!(
            validate_segment_rewrite(&seg, &rew),
            Err(RewriteViolation::ShapeMismatch { index: 2 })
        );
        // Different opcode entirely.
        let mut rew2 = seg.clone();
        rew2[0].op = ArmOp::Sub {
            rd: Reg::R5,
            rn: Reg::R0,
            op2: Operand2::Imm(1),
        };
        assert_eq!(
            validate_segment_rewrite(&seg, &rew2),
            Err(RewriteViolation::ShapeMismatch { index: 0 })
        );
    }

    #[test]
    fn validator_rejects_unmodeled_ops() {
        let seg = vec![ins(ArmOp::Bl {
            label: "f".to_string(),
        })];
        assert_eq!(
            validate_segment_rewrite(&seg, &seg.clone()),
            Err(RewriteViolation::Unmodeled { index: 0 })
        );
    }

    #[test]
    fn validator_rejects_swapped_input_use() {
        // Reading the input from the wrong register: r0+r1 vs r0+r2. The
        // equation (r1 ~ r2) survives to entry non-identity.
        let seg = vec![ins(ArmOp::Add {
            rd: Reg::R3,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        })];
        let rew = vec![ins(ArmOp::Add {
            rd: Reg::R3,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R2),
        })];
        assert_eq!(
            validate_segment_rewrite(&seg, &rew),
            Err(RewriteViolation::EntryNotIdentity {
                orig: Reg::R1,
                rewritten: Reg::R2
            })
        );
    }

    #[test]
    fn validator_rejects_redirected_live_def() {
        // The rewrite moves a def to r7 but a downstream use still reads the
        // original register: the def kills the (r3 ~ r3) equation under a
        // different pairing.
        let seg = setcond_segment();
        let mut rew = seg.clone();
        rew[0].op = ArmOp::Sub {
            rd: Reg::R7,
            rn: Reg::R0,
            op2: Operand2::Reg(Reg::R1),
        };
        assert_eq!(
            validate_segment_rewrite(&seg, &rew),
            Err(RewriteViolation::DefClobbersEquation {
                index: 0,
                orig: Reg::R3,
                rewritten: Reg::R3
            })
        );
    }

    #[test]
    fn validator_rejects_clobber_of_live_value() {
        // A def renamed ONTO a register that still carries a live value (#226
        // class, the alloc_temp-clobbers-vstack bug shape): r4's def lands on
        // r3 while r3's umull-high value is still live.
        let seg = umull_segment();
        let mut rew = seg.clone();
        // lsr r4,r3 → lsr r2,r3 BUT r2 (umull rdlo) is read by the final add.
        rew[3].op = ArmOp::Lsr {
            rd: Reg::R2,
            rn: Reg::R3,
            shift: 2,
        };
        // also point the add's rn at the new home so the simple rename is
        // "locally consistent" — the validator must still catch the clobber.
        rew[4].op = ArmOp::Add {
            rd: Reg::R0,
            rn: Reg::R2,
            op2: Operand2::RegShift {
                rm: Reg::R2,
                shift: crate::rules::ShiftType::LSR,
                amount: 31,
            },
        };
        assert!(validate_segment_rewrite(&seg, &rew).is_err());
    }

    #[test]
    fn validator_rejects_movt_split_from_its_movw() {
        // RMW: movt reads the low half its movw wrote. Renaming the movt's
        // register without the movw is a torn 32-bit constant.
        let seg = umull_segment();
        let mut rew = seg.clone();
        rew[1].op = ArmOp::Movt {
            rd: Reg::R5,
            imm16: 52428,
        };
        rew[2].op = ArmOp::Umull {
            rdlo: Reg::R2,
            rdhi: Reg::R3,
            rn: Reg::R0,
            rm: Reg::R5,
        };
        assert!(
            validate_segment_rewrite(&seg, &rew).is_err(),
            "torn movw/movt pair must be rejected"
        );
        // Even the CONSISTENT rename of the whole constant (movw+movt+use to
        // r5) is rejected here: r1 is in the original's last-written set, so
        // its exit pinning (r1 ~ r1) is seeded, and the rewritten movt no
        // longer establishes it — the exact live-out-pinning contract the
        // pass itself honours.
        let mut rew2 = seg.clone();
        rew2[0].op = ArmOp::Movw {
            rd: Reg::R5,
            imm16: 52429,
        };
        rew2[1].op = ArmOp::Movt {
            rd: Reg::R5,
            imm16: 52428,
        };
        rew2[2].op = ArmOp::Umull {
            rdlo: Reg::R2,
            rdhi: Reg::R3,
            rn: Reg::R0,
            rm: Reg::R5,
        };
        assert_eq!(
            validate_segment_rewrite(&seg, &rew2),
            Err(RewriteViolation::DefClobbersEquation {
                index: 1,
                orig: Reg::R1,
                rewritten: Reg::R1
            }),
            "renaming away a pinned live-out must be rejected"
        );
    }

    #[test]
    fn validator_rejects_selectmove_rm_rename() {
        // SelectMove's rm (the clamp bound) renamed to a register holding
        // something else.
        let seg = clamp_segment();
        let mut rew = seg.clone();
        rew[5].op = ArmOp::SelectMove {
            rd: Reg::R0,
            rm: Reg::R2,
            cond: Condition::LT,
        };
        assert!(
            validate_segment_rewrite(&seg, &rew).is_err(),
            "clamp lower bound read from the upper-bound register"
        );
    }

    #[test]
    fn validator_rejects_swapped_dsts() {
        let seg = loadstore_segment();
        let mut rew = seg.clone();
        // Swap the two load destinations without touching the consumers.
        rew[0].op = ArmOp::Ldr {
            rd: Reg::R4,
            addr: MemAddr {
                base: Reg::R11,
                offset: 0,
                offset_reg: Some(Reg::R1),
            },
        };
        rew[1].op = ArmOp::Ldr {
            rd: Reg::R3,
            addr: MemAddr::imm(Reg::R11, 8),
        };
        assert!(validate_segment_rewrite(&seg, &rew).is_err());
    }

    #[test]
    fn validator_accepts_dead_def_redirect_the_documented_v1_bound() {
        // HONEST BOUND (documented on validate_segment_rewrite): a
        // segment-internally DEAD def redirected to a register the original
        // never writes is accepted — the validated contract covers exactly
        // the original's last-written exit state (the pass's own pinning
        // contract). Closing this needs cross-segment liveness (step 5).
        let seg = dead_def_segment();
        let mut rew = seg.clone();
        rew[0].op = ArmOp::Movw {
            rd: Reg::R7,
            imm16: 1,
        }; // dead in both; r7 not in the original's written set
        assert_eq!(validate_segment_rewrite(&seg, &rew), Ok(()));
        // ... and a redirect that is dead in BOTH segments w.r.t. the
        // written-set contract (movw r0 overwritten by the add) is likewise
        // accepted — genuinely equivalent exit state, not a miss.
        let mut rew2 = seg.clone();
        rew2[0].op = ArmOp::Movw {
            rd: Reg::R0,
            imm16: 1,
        };
        assert_eq!(validate_segment_rewrite(&seg, &rew2), Ok(()));
        // ... but the SAME dead def redirected onto a LIVE input (r1, read by
        // the add) clobbers a value downstream code still needs → rejected.
        let mut rew3 = seg.clone();
        rew3[0].op = ArmOp::Movw {
            rd: Reg::R1,
            imm16: 1,
        };
        assert_eq!(
            validate_segment_rewrite(&seg, &rew3),
            Err(RewriteViolation::DefClobbersEquation {
                index: 0,
                orig: Reg::R1,
                rewritten: Reg::R1
            })
        );
    }

    #[test]
    fn validator_accepts_a_legitimate_internal_rename() {
        // Hand-built valid rewrite: the interior r5 range (born 0, dies 1) of
        // reshuffle_segment moved to r4; inputs (r0) and live-outs
        // (r1/r2/r5-final) untouched.
        let seg = reshuffle_segment();
        let mut rew = seg.clone();
        rew[0].op = ArmOp::Add {
            rd: Reg::R4,
            rn: Reg::R0,
            op2: Operand2::Imm(1),
        };
        rew[1].op = ArmOp::Mov {
            rd: Reg::R2,
            op2: Operand2::Reg(Reg::R4),
        };
        assert_eq!(validate_segment_rewrite(&seg, &rew), Ok(()));
    }

    // --- VCR-RA-003 criterion 2: seeded mutation campaign ----------------

    /// Deterministic splitmix64 — no rand dependency.
    struct MutRng(u64);
    impl MutRng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
            z ^ (z >> 31)
        }
        fn pick(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    /// Apply one random rename-class mutation to `rew`: swap one register
    /// occurrence's uses, redirect one def, or swap two instructions' dsts.
    /// Returns `None` when the drawn mutation is inapplicable (no candidates,
    /// RMW field disagreement, or a no-op draw) — the caller redraws.
    fn mutate_rewrite(rew: &[ArmInstruction], rng: &mut MutRng) -> Option<Vec<ArmInstruction>> {
        let mut out = rew.to_vec();
        match rng.pick(3) {
            // Swap one instruction's occurrences of a used register.
            0 => {
                let mut cands: Vec<(usize, Reg)> = Vec::new();
                for (i, instr) in rew.iter().enumerate() {
                    if let Some(e) = reg_effect(&instr.op) {
                        for u in e.uses {
                            if VPOOL.contains(&u) {
                                cands.push((i, u));
                            }
                        }
                    }
                }
                if cands.is_empty() {
                    return None;
                }
                let (i, from) = cands[rng.pick(cands.len())];
                let to = VPOOL[rng.pick(VPOOL.len())];
                if to == from {
                    return None;
                }
                let use_map = BTreeMap::from([(from, to)]);
                out[i].op = rewrite_op(&rew[i].op, &use_map, &BTreeMap::new())?;
            }
            // Redirect one instruction's def.
            1 => {
                let mut cands: Vec<(usize, Reg)> = Vec::new();
                for (i, instr) in rew.iter().enumerate() {
                    if let Some(e) = reg_effect(&instr.op) {
                        for d in e.defs {
                            if VPOOL.contains(&d) {
                                cands.push((i, d));
                            }
                        }
                    }
                }
                if cands.is_empty() {
                    return None;
                }
                let (i, from) = cands[rng.pick(cands.len())];
                let to = VPOOL[rng.pick(VPOOL.len())];
                if to == from {
                    return None;
                }
                let def_map = BTreeMap::from([(from, to)]);
                out[i].op = rewrite_op(&rew[i].op, &BTreeMap::new(), &def_map)?;
            }
            // Swap the destinations of two single-def instructions.
            _ => {
                let singles: Vec<(usize, Reg)> = rew
                    .iter()
                    .enumerate()
                    .filter_map(|(i, instr)| {
                        let e = reg_effect(&instr.op)?;
                        if e.defs.len() == 1 && VPOOL.contains(&e.defs[0]) {
                            Some((i, e.defs[0]))
                        } else {
                            None
                        }
                    })
                    .collect();
                if singles.len() < 2 {
                    return None;
                }
                let (i, di) = singles[rng.pick(singles.len())];
                let (j, dj) = singles[rng.pick(singles.len())];
                if i == j || di == dj {
                    return None;
                }
                out[i].op = rewrite_op(&rew[i].op, &BTreeMap::new(), &BTreeMap::from([(di, dj)]))?;
                out[j].op = rewrite_op(&rew[j].op, &BTreeMap::new(), &BTreeMap::from([(dj, di)]))?;
            }
        }
        if out == rew { None } else { Some(out) }
    }

    #[test]
    fn validator_mutation_campaign_kill_rate_at_least_95_percent() {
        // VCR-RA-003 criterion: >=95% mutant kill on a seeded corpus of bad
        // renames / def redirects / dst swaps applied to VALID (orig, rew)
        // pairs. Survivors are mutations equivalent UNDER THE VALIDATED
        // CONTRACT (e.g. redirecting a segment-dead def to an
        // original-unwritten register) — counted and bounded by the same 95%.
        let mut corpus: Vec<(Vec<ArmInstruction>, Vec<ArmInstruction>)> = Vec::new();
        for seg in [
            clamp_segment(),
            umull_segment(),
            loadstore_segment(),
            setcond_segment(),
            reshuffle_segment(),
            dead_def_segment(),
        ] {
            // The pass's own rewrite where it produces one, plus the identity
            // rewrite — both are valid pairs the mutations corrupt.
            if let SegmentOutcome::Rewritten(new) = try_reallocate_segment(&seg, &VPOOL) {
                corpus.push((seg.clone(), new));
            }
            corpus.push((seg.clone(), seg));
        }
        for (o, r) in &corpus {
            assert_eq!(
                validate_segment_rewrite(o, r),
                Ok(()),
                "corpus pair invalid"
            );
        }

        let mut rng = MutRng(0x5EED_0242_0003); // #242, VCR-RA-003
        let target = 200usize; // >= 40 per the rivet criterion; more = tighter
        let mut applied = 0usize;
        let mut killed = 0usize;
        let mut survivors: Vec<usize> = Vec::new();
        let mut draws = 0usize;
        while applied < target && draws < 100_000 {
            draws += 1;
            let (orig, rew) = &corpus[rng.pick(corpus.len())];
            let Some(mutant) = mutate_rewrite(rew, &mut rng) else {
                continue;
            };
            applied += 1;
            match validate_segment_rewrite(orig, &mutant) {
                Err(_) => killed += 1,
                Ok(()) => survivors.push(applied),
            }
        }
        assert_eq!(applied, target, "mutation engine starved (draws={draws})");
        println!(
            "VCR-RA-003 mutation campaign: {killed}/{applied} killed ({:.1}%), {} survivors",
            killed as f64 * 100.0 / applied as f64,
            survivors.len()
        );
        // killed/applied >= 95%  ⇔  killed*20 >= applied*19
        assert!(
            killed * 20 >= applied * 19,
            "VCR-RA-003 mutant kill rate {killed}/{applied} = {:.1}% is below \
             the 95% criterion; {} survivors (mutants the contract cannot \
             distinguish): {survivors:?}",
            killed as f64 * 100.0 / applied as f64,
            survivors.len(),
        );
    }

    // --- VCR-RA-003 criteria 1+3: real selector output from the fixtures --

    /// Backend `count_params` replica (arm_backend.rs): an index whose first
    /// access is a read is a parameter.
    fn fixture_count_params(ops: &[synth_core::wasm_op::WasmOp]) -> u32 {
        use synth_core::wasm_op::WasmOp;
        let mut first: BTreeMap<u32, bool> = BTreeMap::new();
        for op in ops {
            match op {
                WasmOp::LocalGet(i) => {
                    first.entry(*i).or_insert(true);
                }
                WasmOp::LocalSet(i) | WasmOp::LocalTee(i) => {
                    first.entry(*i).or_insert(false);
                }
                _ => {}
            }
        }
        first
            .iter()
            .filter_map(|(&i, &read)| if read { Some(i + 1) } else { None })
            .max()
            .unwrap_or(0)
    }

    #[test]
    fn synth_331_call_result_not_parked_on_live_param_home_slot() {
        // #331: gale's dissolved `k_mutex_unlock` (z_impl) parked a call result
        // on the live mutex-ptr arg's #204 param HOME slot — because when the
        // function has no i64 (`has_i64 == false`), `i64_spill_base` aliases the
        // appended `param_slots`, and `restore_caller_saved`'s `spill.alloc()`
        // handed out that aliased slot under R4–R8 pressure. The clobbered slot
        // was then reloaded as the mutex base, so `lock_count = 0` wrote to
        // `linmem[0+12]` → silicon deadlock. Fix: guard the result-park with
        // `area_reserved`, so the first pass returns the ladder-recoverable
        // exhaustion `Err` and the backend retry (spill_on_exhaustion →
        // force_spill_area) reserves the i64 pool, relocating the param home
        // slots ABOVE it so the park is non-aliasing and the function compiles
        // CORRECTLY (not skipped).
        use crate::instruction_selector::{BoundsCheckConfig, InstructionSelector};
        use crate::rules::RuleDatabase;
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../scripts/repro/synth-331/k_mutex_unlock.dissolved.wasm"
        );
        let bytes = std::fs::read(path).unwrap_or_else(|e| panic!("read #331 fixture: {e}"));
        let funcs = synth_core::wasm_decoder::decode_wasm_functions(&bytes).expect("decode #331");
        let f = funcs
            .iter()
            .find(|f| f.export_name.as_deref() == Some("z_impl_k_mutex_unlock"))
            .expect("z_impl_k_mutex_unlock present in fixture");
        let nparams = fixture_count_params(&f.ops);
        let mk = || {
            let db = RuleDatabase::with_standard_rules();
            let mut s = InstructionSelector::with_bounds_check(
                db.rules().to_vec(),
                BoundsCheckConfig::None,
            );
            s.set_relocatable(true);
            s.set_native_pointer_abi(true, 0x10000);
            s
        };
        // The load-bearing unit invariant: on the default (first) pass the #331
        // result-park can no longer obtain a non-aliasing slot without a reserved
        // spill area, so it returns the ladder-recoverable exhaustion `Err`
        // ("all allocatable registers are live on the stack") instead of
        // SILENTLY clobbering arg0's home slot. This is what flips the bug from a
        // silent miscompile to a fail-loud, retry-recoverable condition.
        //
        // Pre-fix this same call returned `Ok` (compiled, with the aliasing
        // miscompile); post-fix it must `Err` — that is the regression lock.
        // (End-to-end CORRECTNESS of the retry — param slots relocated above the
        // reserved i64 pool, the no-waiter `lock_count` store deriving its base
        // from the mutex pointer — is verified at the backend/CLI level on this
        // exact committed module: `--target cortex-m4f --native-pointer-abi
        // --relocatable` produces a 886 B body with no `str <call-result>` on the
        // mutex home slot; that path needs the full backend config
        // (func_arg_counts / native_pointer_stack / num_imports) this unit
        // harness deliberately does not replicate.)
        let first = mk().select_with_stack(&f.ops, nparams);
        assert!(
            first
                .as_ref()
                .err()
                .map(|e| e
                    .to_string()
                    .contains("all allocatable registers are live on the stack"))
                .unwrap_or(false),
            "first pass must hit the #331 area-reserved guard (ladder-recoverable Err); got {:?}",
            first.as_ref().map(|i| i.len())
        );
    }

    #[test]
    fn realloc_on_repro_fixture_streams_has_zero_validator_rejects() {
        // VCR-RA-003 criteria 1 + 3 on REAL selector output: run the wired
        // pass over every function of the three frozen repro fixtures.
        //   1. the validator accepts every rewrite the pass produces
        //      (reallocated > 0 proves the pass actually fired);
        //   3. validator-attributable declines == 0 — the roadmap
        //      kill-criterion allows up to ~5% of segments before the
        //      approach is re-evaluated, but 0 is the current truth, so 0 is
        //      what this test pins.
        use crate::instruction_selector::{BoundsCheckConfig, InstructionSelector};
        use crate::rules::RuleDatabase;

        let root = concat!(env!("CARGO_MANIFEST_DIR"), "/../../scripts/repro");
        let mut total = ReallocStats::default();
        let mut selected_fns = 0usize;
        // The full ARM frozen/differential suite (one form per program; the
        // _riscv harnesses and the sp_global/native-pointer-ABI fixtures —
        // native_pointer_*, mutex_pressure — are out of this selector config's
        // scope and excluded; the high_pressure_* fixtures intentionally
        // exhaust the first pass and `continue`-skip here). Broadening from the
        // original 3 streams turns the "0 validator-rejects" guarantee into a
        // whole-suite property (VCR-RA-003 criteria 1 + 3 on real codegen).
        for name in [
            "control_step.wasm",
            "div_const.wat",
            "flight_seam_flat.wasm",
            "flight_seam.wasm",
            "controller_step.wasm",
            "filter_axis.wasm",
            "signed_div_const.wasm",
            "u64_unpack.wat",
            "u64_unpack_inlined.wat",
            "reachable_helper.wasm",
        ] {
            let bytes = std::fs::read(format!("{root}/{name}"))
                .unwrap_or_else(|e| panic!("read fixture {name}: {e}"));
            let wasm = if name.ends_with(".wat") {
                wat::parse_bytes(&bytes).expect("wat parse").into_owned()
            } else {
                bytes
            };
            let funcs =
                synth_core::wasm_decoder::decode_wasm_functions(&wasm).expect("decode fixture");
            for f in &funcs {
                let db = RuleDatabase::with_standard_rules();
                let mut sel = InstructionSelector::with_bounds_check(
                    db.rules().to_vec(),
                    BoundsCheckConfig::None,
                );
                sel.set_relocatable(true); // the differential-fixture path (#197)
                let Ok(instrs) = sel.select_with_stack(&f.ops, fixture_count_params(&f.ops)) else {
                    continue; // out-of-scope function (not what this test pins)
                };
                selected_fns += 1;
                let (_, stats) = reallocate_function(&instrs, &VPOOL);
                total.segments += stats.segments;
                total.reallocated += stats.reallocated;
                total.declined += stats.declined;
                total.needs_spill += stats.needs_spill;
                total.validator_rejects += stats.validator_rejects;
            }
        }
        assert!(selected_fns > 0, "no fixture function selected");
        assert!(
            total.reallocated > 0,
            "the pass must actually fire on the fixtures (segments={})",
            total.segments
        );
        println!(
            "[VCR-RA-003 real-codegen completeness] {selected_fns} fns, \
             {} segments: {} reallocated, {} declined ({} validator-rejected), \
             {} need spill",
            total.segments,
            total.reallocated,
            total.declined,
            total.validator_rejects,
            total.needs_spill
        );
        // Criterion 1: the validator accepted real rewrites (the pass fired).
        // Criterion 3 (roadmap kill-criterion): validator-attributable declines
        // must stay below ~5% of segments before the approach is re-evaluated.
        // Enforce the criterion explicitly AND pin the current stronger truth
        // (0) — so a regression that merely stays under 5% is still caught.
        let pct = (total.validator_rejects as f64) / (total.segments as f64) * 100.0;
        assert!(
            pct < 5.0,
            "validator-attributable decline rate {pct:.1}% exceeds the VCR-RA-003 \
             5% kill-criterion ({} of {} segments) — validator completeness on \
             real selector output has regressed",
            total.validator_rejects,
            total.segments
        );
        assert_eq!(
            total.validator_rejects, 0,
            "validator-attributable declines on the full ARM frozen suite \
             (criterion: <5% of {} segments; current truth and the pinned \
             value: 0)",
            total.segments
        );
    }

    // ---- VCR-RA-001 spill re-choice spike (#242) ----------------------------

    fn sp_str(rd: Reg, off: i32) -> ArmInstruction {
        ins(ArmOp::Str {
            rd,
            addr: crate::rules::MemAddr {
                base: Reg::SP,
                offset: off,
                offset_reg: None,
            },
        })
    }
    fn sp_ldr(rd: Reg, off: i32) -> ArmInstruction {
        ins(ArmOp::Ldr {
            rd,
            addr: crate::rules::MemAddr {
                base: Reg::SP,
                offset: off,
                offset_reg: None,
            },
        })
    }
    fn movw(rd: Reg, imm16: u16) -> ArmInstruction {
        ins(ArmOp::Movw { rd, imm16 })
    }
    fn add3(rd: Reg, rn: Reg, rm: Reg) -> ArmInstruction {
        ins(ArmOp::Add {
            rd,
            rn,
            op2: Operand2::Reg(rm),
        })
    }
    fn mov_rr(rd: Reg, rm: Reg) -> ArmInstruction {
        ins(ArmOp::Mov {
            rd,
            op2: Operand2::Reg(rm),
        })
    }

    /// The target case forward_stack_reloads misses: the spill store's SOURCE
    /// is clobbered (genuine pressure spill), but reload #2 can forward from
    /// reload #1.
    #[test]
    fn spill_realloc_forwards_reload_to_reload_242() {
        let seq = vec![
            sp_str(Reg::R0, 8), // spill A
            movw(Reg::R0, 7),   // A's register clobbered → store-source dead
            sp_ldr(Reg::R1, 8), // reload #1 (stays: no holder survives)
            add3(Reg::R2, Reg::R1, Reg::R0),
            sp_ldr(Reg::R3, 8), // reload #2 → mov r3, r1
            add3(Reg::R4, Reg::R3, Reg::R2),
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 1, "exactly the second reload forwards");
        assert_eq!(out.len(), seq.len(), "1-for-1 replacement, no growth");
        assert_eq!(out[2].op, seq[2].op, "reload #1 must remain a load");
        assert_eq!(
            out[4].op,
            ArmOp::Mov {
                rd: Reg::R3,
                op2: Operand2::Reg(Reg::R1)
            },
            "reload #2 forwards from reload #1's register"
        );
    }

    /// A reload into a register that already holds the slot's value is deleted.
    #[test]
    fn spill_realloc_deletes_redundant_same_reg_reload_242() {
        let seq = vec![
            sp_str(Reg::R0, 4),
            movw(Reg::R0, 1), // clobber the store source
            sp_ldr(Reg::R1, 4),
            ins(ArmOp::Cmp {
                rn: Reg::R1,
                op2: Operand2::Imm(0),
            }),
            sp_ldr(Reg::R1, 4), // r1 still holds slot #4's value → delete
            add3(Reg::R2, Reg::R1, Reg::R0),
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 1);
        assert_eq!(out.len(), seq.len() - 1, "the redundant reload is deleted");
        assert!(
            !out.iter()
                .skip(3)
                .any(|i| matches!(&i.op, ArmOp::Ldr { addr, .. } if addr.base == Reg::SP)),
            "no second frame reload remains"
        );
    }

    /// Clobbering the only holder kills forwarding — the reload must stay.
    #[test]
    fn spill_realloc_holder_clobber_blocks_forwarding_242() {
        let seq = vec![
            sp_str(Reg::R0, 4),
            movw(Reg::R0, 1),
            sp_ldr(Reg::R1, 4),
            movw(Reg::R1, 2), // holder clobbered
            sp_ldr(Reg::R2, 4),
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 0, "no provable holder at reload #2");
        assert_eq!(out, seq, "stream unchanged");
    }

    /// Push/Pop moves SP and touches stack memory — every slot name dies.
    #[test]
    fn spill_realloc_push_pop_clears_slot_tracking_242() {
        let seq = vec![
            sp_str(Reg::R0, 4),
            ins(ArmOp::Push {
                regs: vec![Reg::R4],
            }),
            sp_ldr(Reg::R1, 4), // #4 no longer names the same slot
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 0);
        assert_eq!(out, seq);
    }

    /// A reg-reg move propagates value identity: the copy becomes a holder.
    #[test]
    fn spill_realloc_mov_propagates_holder_242() {
        let seq = vec![
            sp_str(Reg::R0, 0),
            mov_rr(Reg::R3, Reg::R0), // r3 := A (copy)
            movw(Reg::R0, 9),         // original holder clobbered
            sp_ldr(Reg::R1, 0),       // → mov r1, r3
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 1);
        assert_eq!(
            out[3].op,
            ArmOp::Mov {
                rd: Reg::R1,
                op2: Operand2::Reg(Reg::R3)
            }
        );
    }

    /// A slot overwrite retargets forwarding to the NEW value's holder.
    #[test]
    fn spill_realloc_slot_overwrite_retargets_242() {
        let seq = vec![
            sp_str(Reg::R0, 4),
            movw(Reg::R0, 1),
            sp_str(Reg::R5, 4), // slot now holds r5's value
            sp_ldr(Reg::R2, 4), // → mov r2, r5 (NOT r0)
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 1);
        assert_eq!(
            out[3].op,
            ArmOp::Mov {
                rd: Reg::R2,
                op2: Operand2::Reg(Reg::R5)
            }
        );
    }

    /// Pressure gate (c): the forwarding `mov` extends the holder's live range;
    /// if that pushes the segment's peak value pressure past the pool AND past
    /// the pre-transform peak, the whole segment is declined. Identical stream
    /// minus the extra long-lived value commits (post ≤ pool headroom rule).
    #[test]
    fn spill_realloc_pressure_gate_declines_when_saturated_242() {
        // Common skeleton: A := r1 (from a load); spill A; A's last real use;
        // 8 long-lived values fill r0,r2..r8; then a reload of A that forwards
        // from r1, extending A across the fat window.
        let build = |with_extra: bool| {
            let mut s = vec![
                ins(ArmOp::Ldr {
                    rd: Reg::R1,
                    addr: crate::rules::MemAddr {
                        base: Reg::R11,
                        offset: 0,
                        offset_reg: None,
                    },
                }),
                sp_str(Reg::R1, 0), // holders = {r1}
                ins(ArmOp::Cmp {
                    rn: Reg::R1,
                    op2: Operand2::Imm(0),
                }), // A's last pre-transform use
            ];
            if with_extra {
                // Two more values live across the window (homed OUTSIDE the
                // pool, in R9/R10 — value pressure counts every register, so
                // these saturate the window without freeing a pool reg).
                s.push(movw(Reg::R9, 98));
                s.push(movw(Reg::R10, 99));
            }
            for (k, rd) in [Reg::R3, Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8]
                .iter()
                .enumerate()
            {
                s.push(movw(*rd, k as u16));
            }
            s.push(movw(Reg::R0, 40)); // v0, last use just before the reload
            s.push(ins(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }));
            s.push(sp_ldr(Reg::R0, 0)); // reload A → mov r0, r1 (candidate)
            // Keep SP's value live past the reload (real segments always have
            // later frame traffic), so the forwarding genuinely ADDS pressure.
            s.push(sp_str(Reg::R4, 20));
            let mut used = vec![
                Reg::R0,
                Reg::R3,
                Reg::R4,
                Reg::R5,
                Reg::R6,
                Reg::R7,
                Reg::R8,
            ];
            if with_extra {
                used.push(Reg::R9);
                used.push(Reg::R10);
            }
            s.push(ins(ArmOp::Push { regs: used }));
            s
        };

        // Without the extra value: post-transform peak fits the pool → commit.
        let lean = build(false);
        let (out, n) = apply_spill_realloc(&lean);
        assert_eq!(
            n, 1,
            "lean segment: forwarding commits within pool headroom"
        );
        assert!(
            out.iter().any(|i| i.op
                == ArmOp::Mov {
                    rd: Reg::R0,
                    op2: Operand2::Reg(Reg::R1)
                }),
            "the reload became a mov"
        );

        // With them: post > pre AND post > pool → the segment is declined whole.
        let fat = build(true);
        let pre = straight_line_peak_pressure(&fat).unwrap();
        let (out, n) = apply_spill_realloc(&fat);
        assert_eq!(
            n, 0,
            "saturated segment (pre-peak {pre}) must be declined by the pressure gate"
        );
        assert_eq!(out, fat, "declined segment keeps its original bytes");
    }

    // ---- VCR-RA-001 stage 2: Belady spill-plan re-choice (#242) -------------

    /// The flat_flight shape stage 1 cannot touch: the greedy lowering re-used
    /// the HOLDING register for an unrelated constant while a provably-dead
    /// register existed. Stage 2 renames the clobbering def (and its use) onto
    /// the dead register and deletes the reload outright.
    #[test]
    fn spill_rechoice_renames_clobberer_and_deletes_reload_242() {
        let seq = vec![
            sp_str(Reg::R2, 8), // v (segment input in r2) spilled
            movw(Reg::R2, 20),  // kill-def: holder re-used for a constant
            ins(ArmOp::Mul {
                rd: Reg::R3,
                rn: Reg::R3,
                rm: Reg::R2,
            }), // the constant's only use
            sp_ldr(Reg::R2, 8), // reload of v — no surviving holder
            add3(Reg::R0, Reg::R2, Reg::R3), // v used; also r0's pure def
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 1, "the reload dissolves via re-choice");
        assert_eq!(out.len(), seq.len() - 1, "reload deleted, renames 1-for-1");
        assert_eq!(
            out[1].op,
            ArmOp::Movw {
                rd: Reg::R0,
                imm16: 20
            },
            "the clobbering def is renamed onto the dead register (r0: first \
             touch after its range is r0's pure def at the tail add)"
        );
        assert_eq!(
            out[2].op,
            ArmOp::Mul {
                rd: Reg::R3,
                rn: Reg::R3,
                rm: Reg::R0,
            },
            "the renamed def's use follows it"
        );
        assert!(
            !out.iter()
                .any(|i| matches!(&i.op, ArmOp::Ldr { addr, .. } if addr.base == Reg::SP)),
            "no frame reload remains"
        );
    }

    /// No provably-dead register across the clobber window ⇒ the re-choice
    /// declines (every candidate's first touch after the window is a READ).
    #[test]
    fn spill_rechoice_declines_when_no_register_is_dead_242() {
        let mut seq = vec![
            sp_str(Reg::R0, 0),
            movw(Reg::R0, 7), // kill-def
            ins(ArmOp::Mul {
                rd: Reg::R1,
                rn: Reg::R1,
                rm: Reg::R0,
            }), // use (r1 touched inside the window too)
            sp_ldr(Reg::R0, 0),
        ];
        // Every remaining pool candidate is read first after the window.
        for t in [
            Reg::R2,
            Reg::R3,
            Reg::R4,
            Reg::R5,
            Reg::R6,
            Reg::R7,
            Reg::R8,
        ] {
            seq.push(add3(t, t, Reg::R0));
        }
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 0, "no dead register → the pair must decline");
        assert_eq!(out, seq, "declined segment keeps its original bytes");
    }

    /// Guard (d): a sub-word frame access disqualifies the whole segment
    /// (the #483-class conservatism — slot identity is word-granular).
    #[test]
    fn spill_rechoice_declines_subword_frame_access_242() {
        let seq = vec![
            sp_str(Reg::R2, 8),
            movw(Reg::R2, 20),
            ins(ArmOp::Mul {
                rd: Reg::R3,
                rn: Reg::R3,
                rm: Reg::R2,
            }),
            ins(ArmOp::Ldrb {
                rd: Reg::R5,
                addr: crate::rules::MemAddr {
                    base: Reg::SP,
                    offset: 16,
                    offset_reg: None,
                },
            }), // sub-word [sp] access
            sp_ldr(Reg::R2, 8),
            add3(Reg::R0, Reg::R2, Reg::R3),
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 0, "sub-word frame access must disqualify the segment");
        assert_eq!(out, seq);
    }

    /// A single-field RMW clobberer (`movt` writes AND reads rd) cannot be
    /// renamed — `rewrite_op` declines the disagreeing def/use maps.
    #[test]
    fn spill_rechoice_declines_rmw_clobberer_242() {
        let seq = vec![
            sp_str(Reg::R2, 0),
            ins(ArmOp::Movt {
                rd: Reg::R2,
                imm16: 5,
            }), // kill-def that also READS r2
            sp_ldr(Reg::R2, 0),
            add3(Reg::R0, Reg::R2, Reg::R2),
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 0, "an RMW clobberer cannot be renamed away");
        assert_eq!(out, seq);
    }

    /// The clobbering def's value may be live-out (no later def of the holder
    /// in the segment) — renaming would change exit state ⇒ decline.
    #[test]
    fn spill_rechoice_declines_liveout_clobberer_242() {
        let seq = vec![
            sp_str(Reg::R0, 0),
            movw(Reg::R0, 7), // kill-def; r0 never redefined in the segment
            sp_ldr(Reg::R1, 0),
            add3(Reg::R2, Reg::R1, Reg::R0),
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 0, "possibly-live-out clobberer must decline");
        assert_eq!(out, seq);
    }

    /// Guard (b): a reload folded to `mov rd,holder` (rd ≠ holder) nets zero
    /// instructions — a segment that does not strictly shrink is discarded.
    #[test]
    fn spill_rechoice_discards_count_neutral_mov_fold_242() {
        let seq = vec![
            sp_str(Reg::R2, 0),
            movw(Reg::R2, 9),
            add3(Reg::R3, Reg::R2, Reg::R2),
            sp_ldr(Reg::R5, 0), // rd ≠ holder → would fold to mov r5,r2
            add3(Reg::R0, Reg::R5, Reg::R5),
        ];
        let (out, n) = apply_spill_realloc(&seq);
        assert_eq!(n, 0, "count-neutral rewrite must be discarded (guard b)");
        assert_eq!(out, seq);
    }

    /// Belady report: the double-reload trace needs ZERO frame traffic with the
    /// full pool — the emitted 1 store + 2 reloads are all recoverable headroom.
    #[test]
    fn spill_report_belady_beats_greedy_on_double_reload_242() {
        let seq = vec![
            movw(Reg::R0, 5), // A
            sp_str(Reg::R0, 8),
            movw(Reg::R0, 7), // B clobbers A's register
            sp_ldr(Reg::R1, 8),
            add3(Reg::R2, Reg::R1, Reg::R0),
            sp_ldr(Reg::R3, 8),
            add3(Reg::R4, Reg::R3, Reg::R2),
        ];
        let report = spill_choice_report(&seq, 9);
        assert_eq!(report.len(), 1);
        let s = &report[0];
        assert_eq!((s.actual_reloads, s.actual_spill_stores), (2, 1));
        assert_eq!(
            (s.belady_reloads, s.belady_spill_stores),
            (0, 0),
            "≤9 concurrent values → the ideal allocation needs no frame traffic"
        );
        assert!(s.peak_pressure <= 9);
    }

    /// Belady mechanics under an artificially tiny pool (k=2): one eviction
    /// (store) of the farthest-next-use value and one reload when it returns.
    #[test]
    fn spill_report_belady_counts_eviction_and_reload_k2_242() {
        let seq = vec![
            movw(Reg::R0, 1),                // A
            movw(Reg::R1, 2),                // B
            add3(Reg::R2, Reg::R0, Reg::R1), // C := A+B; k=2 → evict B (farther)
            ins(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }), // use A (near)
            ins(ArmOp::Cmp {
                rn: Reg::R1,
                op2: Operand2::Imm(0),
            }), // use B (far) → reload
        ];
        let report = spill_choice_report(&seq, 2);
        assert_eq!(report.len(), 1);
        let s = &report[0];
        assert_eq!((s.actual_reloads, s.actual_spill_stores), (0, 0));
        assert_eq!(
            (s.belady_reloads, s.belady_spill_stores),
            (1, 1),
            "farthest-first evicts B once (1 store) and reloads it once"
        );
    }

    /// A reload from a slot written OUTSIDE the segment is unavoidable: it is
    /// charged to Belady too (no phantom headroom).
    #[test]
    fn spill_report_unknown_slot_reload_charged_to_belady_242() {
        let seq = vec![
            sp_ldr(Reg::R0, 12), // slot written before the segment
            ins(ArmOp::Cmp {
                rn: Reg::R0,
                op2: Operand2::Imm(0),
            }),
        ];
        let report = spill_choice_report(&seq, 9);
        assert_eq!(report.len(), 1);
        let s = &report[0];
        assert_eq!(s.actual_reloads, 1);
        assert_eq!(
            s.belady_reloads, 1,
            "an out-of-segment slot value must be loaded in the ideal world too"
        );
    }
}
