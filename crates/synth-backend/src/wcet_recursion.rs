//! #778 phase 4 (#49) — sound static bound for a SINGLE-SELF-CALL recursion whose
//! controlling value is ENTRY-INDEPENDENTLY bounded, plus the `--wcet-hints`
//! `recursion_depth` sound-checker seam. Converts the `recursion` decline for
//! exactly the shape synth can prove; every other recursion still LOUD-DECLINES.
//!
//! Phase 3 declined EVERY call-graph cycle. This module upgrades the ONE shape it
//! can PROVE bounded and keeps declining the rest:
//!
//! - **Single-self-call chain**: the function contains EXACTLY ONE direct call to
//!   its own `func_<idx>` label, executed at most once per frame (loop multiplier
//!   1). More than one self-call, or a self-call inside a proven loop
//!   (multiplier > 1), makes the call TREE branch — `depth × per-frame` would
//!   under-count by an exponential factor (the fib trap) — so it declines.
//! - **Entry-independent controlling value**: the base guard and the recursive
//!   argument are formed from the SAME masked quantity `m = (param & mask)`, which
//!   lies in `[0, mask]` for ANY runtime input. The recursive argument is
//!   `m - step` (const step); the base guard fires at `m == base` on the path that
//!   does NOT reach the self-call. Because `m ∈ [0, mask]` and decreases by `step`
//!   each frame, the maximum recursion DEPTH is `exit_index(init = mask, step,
//!   base_pred)` — an entry-independent ceiling DERIVED by synth (never the raw
//!   hint), reusing the loop analyzer's wrap/divisibility-safe trip math.
//!
//! ## Why `depth × per-frame` is a sound upper bound here (and only here)
//!
//! 1. **Chain (not tree)**: exactly one self-call per frame, multiplier 1 ⇒ the
//!    call graph unrolled from an entry is a simple PATH of length ≤ depth; the
//!    total machine work is `Σ_{k=0..depth} frame_cost_k ≤ (depth+1) × max_frame_cost`.
//!    The `+1` counts the BASE frame (which runs `own_cycles` but no self-call);
//!    omitting it would undercount by one frame → unsound.
//! 2. **Entry-independent depth**: `m = param & mask ∈ [0, mask]` regardless of the
//!    runtime `param`; a strict decrease by `step` toward the base guard bounds the
//!    number of recursive frames by `exit_index(mask, step, ·)`. Seeding the trip
//!    math with `init = mask` is the WORST case over all inputs (real `m ≤ mask`,
//!    and `(m - step) & mask ≤ m - step`, so real depth ≤ derived) — the mask buys
//!    an entry-independent upper bound on an otherwise-runtime counter.
//! 3. **Control-dependence**: the self-call is proven UNREACHABLE when the base
//!    guard holds (the guard's taken target is a base block with no self-call; the
//!    self-call sits on the guarded fall-through), so `m == base` never passes the
//!    dangerous `base - step` into a re-mask (`(-1) & mask = mask` would diverge).
//!    This is the linear-body analog of the loop analyzer's branch discipline.
//! 4. **Hint discipline (the scry seam)**: the depth is DERIVED; a `--wcet-hints`
//!    `recursion_depth` entry only GATES consumption (a bound this consequential is
//!    opt-in, mirroring the equality-exit loop-hint gate). `hint < derived` →
//!    `hint-below-derived-depth`; a structure synth cannot prove → any offered hint
//!    is `hint-unverifiable-recursion`. The emitted depth is always synth's derived
//!    ceiling.
//!
//! Anything the matcher does not precisely model → NO certificate → the function
//! keeps the phase-3 `recursion` decline (the decline is MOVED, never deleted).

use synth_core::wcet::{WcetHintReject, WcetHintRejection, WcetRecursionCert};
use synth_synthesis::{ArmInstruction, ArmOp, Condition, Operand2, Reg};

use crate::wcet_loops::{Pred, Rel, exit_index};

/// Outcome of the self-recursion analysis over one function's final stream.
pub(crate) enum RecursionAnalysis {
    /// The function is not self-recursive (no `BL self_label`) — the caller
    /// proceeds with the normal (non-recursion) intermediate.
    NotRecursive,
    /// The function self-recurses but synth could not prove a bounded chain, OR no
    /// depth hint was offered — it keeps the `recursion` decline. Any offered hint
    /// is recorded as rejected.
    Unprovable {
        hint_rejections: Vec<WcetHintRejection>,
    },
    /// A proven, hint-gated bounded self-recursion: the certificate + any rejected
    /// hints. The caller attaches the certificate to the composable intermediate.
    Certified {
        cert: WcetRecursionCert,
        hint_rejections: Vec<WcetHintRejection>,
    },
}

/// Symbolic value the linear-body walk tracks. Deliberately tiny: only the shapes
/// the canonical masked-recursion chain is built from; everything else is `Top`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sym {
    Top,
    /// A compile-time constant.
    Const(i32),
    /// The raw incoming param value (whichever AAPCS register / spill slot it lives
    /// in). All four in-arg registers alias the same logical "param" only if the
    /// function has ONE controlling param — we track a single param identity keyed
    /// by its origin register, so `Param(r)` means "the entry value of register r".
    Param(Reg),
    /// `(param_of(base) & mask)` — the masked controlling quantity, `∈ [0, mask]`.
    Masked {
        base: Reg,
        mask: i32,
    },
    /// `(param_of(base) & mask) + add` — the masked quantity shifted by a const
    /// (the recursive-argument shape `m - step`).
    MaskedStep {
        base: Reg,
        mask: i32,
        add: i64,
    },
}

/// Per-instruction walk state: symbolic registers + word SP slots + last compare.
struct Walk {
    regs: [Sym; 16],
    /// SP-relative word slot → symbolic content (param spills; nothing else needed).
    slots: std::collections::BTreeMap<i64, Sym>,
    /// Operands of the last precisely-known compare (for the base guard predicate).
    flags: Option<(Sym, Sym)>,
}

impl Walk {
    /// Seed r0..r3 as their own entry-`Param` identities (the AAPCS integer args);
    /// everything else is unknown.
    fn entry() -> Self {
        let mut regs = [Sym::Top; 16];
        regs[Reg::R0 as usize] = Sym::Param(Reg::R0);
        regs[Reg::R1 as usize] = Sym::Param(Reg::R1);
        regs[Reg::R2 as usize] = Sym::Param(Reg::R2);
        regs[Reg::R3 as usize] = Sym::Param(Reg::R3);
        Walk {
            regs,
            slots: std::collections::BTreeMap::new(),
            flags: None,
        }
    }

    fn reg(&self, r: Reg) -> Sym {
        self.regs[r as usize]
    }
    fn set(&mut self, r: Reg, v: Sym) {
        self.regs[r as usize] = v;
    }
    fn op2(&self, o: &Operand2) -> Sym {
        match o {
            Operand2::Imm(c) => Sym::Const(*c),
            Operand2::Reg(r) => self.reg(*r),
            Operand2::RegShift { .. } => Sym::Top,
        }
    }
}

/// The base-guard predicate over the masked controlling value, resolved to the
/// (base, mask) identity it reads.
#[derive(Debug, Clone, Copy)]
struct GuardPred {
    base: Reg,
    mask: i32,
    /// `(m + add) REL rhs` where `m = param & mask`.
    add: i64,
    rel: Rel,
    rhs: i32,
}

/// Analyze `instrs` for a bounded self-recursion. `self_label` is this function's
/// own `func_<idx>` label; `mult_at(i)` gives instruction `i`'s proven loop
/// execution-count multiplier (1 outside any proven loop). `hint` is the untrusted
/// `recursion_depth` claim, if any.
pub(crate) fn analyze_recursion(
    instrs: &[ArmInstruction],
    self_label: Option<&str>,
    mult_at: &dyn Fn(usize) -> u128,
    hint: Option<u64>,
) -> RecursionAnalysis {
    let Some(self_label) = self_label else {
        return RecursionAnalysis::NotRecursive;
    };

    // ---- locate the self-call site(s) ----
    let self_calls: Vec<usize> = instrs
        .iter()
        .enumerate()
        .filter_map(|(i, ins)| match &ins.op {
            ArmOp::Bl { label } if label == self_label => Some(i),
            _ => None,
        })
        .collect();
    if self_calls.is_empty() {
        return RecursionAnalysis::NotRecursive;
    }

    // From here the function IS self-recursive: without a proof it declines
    // `recursion`; any offered hint is rejected.
    let reject = |reason: WcetHintReject| -> RecursionAnalysis {
        let hint_rejections = hint
            .map(|h| {
                let note = reason.note().to_string();
                vec![WcetHintRejection {
                    loop_index: 0,
                    head_offset: None,
                    hint: h,
                    reason,
                    note,
                }]
            })
            .unwrap_or_default();
        RecursionAnalysis::Unprovable { hint_rejections }
    };

    // Gate 1: EXACTLY ONE self-call, executed once per frame (multiplier 1).
    // Two self-calls (tree recursion, e.g. fib) or a self-call inside a proven
    // loop would make `depth × per-frame` an exponential under-count.
    if self_calls.len() != 1 {
        return reject(WcetHintReject::HintUnverifiableRecursion);
    }
    let self_idx = self_calls[0];
    if mult_at(self_idx) != 1 {
        return reject(WcetHintReject::HintUnverifiableRecursion);
    }

    // Gate 2: the whole function must be free of OTHER backward branches (loops
    // around the recursion) — analyze_loops already handles proven loops, but the
    // control-dependence proof below assumes a linear body with only forward
    // guards. A proven counted loop wrapping the self-call is out of scope
    // (multiplier would be >1 and already rejected above); an UNPROVEN loop would
    // have declined `loop` before we run. So here we only need to reject any
    // backward branch defensively.
    let byte = match byte_positions(instrs) {
        Some(b) => b,
        None => return reject(WcetHintReject::HintUnverifiableRecursion),
    };

    // Gate 3: prove the masked-chain structure + control dependence, derive depth.
    let Some((base_pred, step)) = prove_masked_chain(instrs, self_idx, &byte) else {
        return reject(WcetHintReject::HintUnverifiableRecursion);
    };

    // Derive max depth via the loop trip machinery. The controlling value at the
    // first frame is `m ∈ [0, mask]` (any runtime input, by the mask); the recursion
    // continues while the base guard is FALSE and stops when it holds. `exit_index`
    // returns the number of steps until the base predicate first HOLDS for a GIVEN
    // init, so the true worst-case depth is the MAX over the valid init domain
    // `[0, mask]`. For a monotone counter that max is at an ENDPOINT (0 or mask)
    // depending on step direction — but rather than reason about which, we evaluate
    // BOTH endpoints and require BOTH terminate, taking the max. (Seeding only `mask`
    // would UNDER-estimate a count-up whose worst case is init 0.) If either
    // endpoint fails to terminate (step walks away, or a wrap), the chain is not
    // guaranteed-terminating for all inputs → decline.
    let p = Pred {
        off: 0, // synthetic — exit_index reads only add/rel/rhs
        add: base_pred.add,
        rel: base_pred.rel,
        rhs: base_pred.rhs,
        masked_ceiling: None, // recursion derives its own depth via exit_index directly
    };
    // Endpoint reasoning is sound only when `exit_index` is MONOTONE in init over
    // `[0, mask]`. For a threshold predicate (<, <=, >, >=) it is. For an
    // equality/inequality base guard, an INTERIOR init can diverge (miss the target
    // residue class) even when both endpoints land — so restrict Eq/Ne base guards
    // to step magnitude 1, where EVERY init in `[0, mask]` reaches the target and
    // monotonicity holds. (A larger step with an Eq guard is exactly the
    // divisibility-divergence trap; refusing it keeps the endpoint bound sound.)
    if matches!(base_pred.rel, Rel::Eq | Rel::Ne) && step.abs() != 1 {
        return reject(WcetHintReject::HintUnverifiableRecursion);
    }
    let (Some((d_hi, _)), Some((d_lo, _))) = (
        exit_index(base_pred.mask, step, &p),
        exit_index(0, step, &p),
    ) else {
        // An endpoint does not terminate (step does not divide the distance, walks
        // away, or wraps) → not a bounded chain for all inputs.
        return reject(WcetHintReject::HintUnverifiableRecursion);
    };
    let derived_depth = d_hi.max(d_lo);

    // Gate 4 (the scry seam): a bound this consequential is HINT-GATED. No hint ⇒
    // keep the `recursion` decline (nothing rejected — none was offered).
    let Some(h) = hint else {
        return RecursionAnalysis::Unprovable {
            hint_rejections: Vec::new(),
        };
    };
    // Cross-check: a hint BELOW the derived ceiling is a wrong oracle claim.
    if h < derived_depth {
        return RecursionAnalysis::Unprovable {
            hint_rejections: vec![WcetHintRejection {
                loop_index: 0,
                head_offset: None,
                hint: h,
                reason: WcetHintReject::HintBelowDerivedDepth,
                note: WcetHintReject::HintBelowDerivedDepth.note().to_string(),
            }],
        };
    }
    // Accept: emit synth's DERIVED depth (never the raw hint).
    RecursionAnalysis::Certified {
        cert: WcetRecursionCert {
            self_label: self_label.to_string(),
            max_depth: derived_depth,
            hint: h,
        },
        hint_rejections: Vec::new(),
    }
}

/// Byte offset of each instruction from the REAL encoder (same source of truth the
/// branch displacements were resolved against — the estimator is not exact).
fn byte_positions(instrs: &[ArmInstruction]) -> Option<Vec<i64>> {
    let encoder = crate::arm_encoder::ArmEncoder::new_thumb2();
    let mut pos = Vec::with_capacity(instrs.len());
    let mut p: i64 = 0;
    for ins in instrs {
        pos.push(p);
        let bytes = encoder.encode(&ins.op).ok()?;
        p += bytes.len() as i64;
    }
    Some(pos)
}

/// Prove the canonical masked-recursion chain around the single self-call at
/// `self_idx`, returning `(base_guard_predicate, step)` on success.
///
/// Requirements (all load-bearing — see the module soundness argument):
/// - a base guard `Cmp (param & mask), #rhs` + conditional branch whose TAKEN
///   target is a block that does NOT contain the self-call, and whose FALL-THROUGH
///   reaches the self-call (control dependence: self-call unreachable when guard
///   holds);
/// - the self-call argument in `R0` is `(param & mask) - step` reading the SAME
///   (base, mask) the guard reads (identical masked quantity);
/// - no other backward branch anywhere (a linear guarded body).
fn prove_masked_chain(
    instrs: &[ArmInstruction],
    self_idx: usize,
    byte: &[i64],
) -> Option<(GuardPred, i64)> {
    // Target byte of a Thumb-2 forward/backward branch at index `i`.
    let target_byte = |i: usize, offset: i32| byte[i] + 4 + (offset as i64) * 2;
    let idx_at = |b: i64| -> Option<usize> { byte.iter().position(|&p| p == b) };

    // No backward branch may exist (a loop) — those are the loop analyzer's job and
    // would already have been proven or declined; a residual one here breaks the
    // linear-body control-dependence reasoning.
    for (i, ins) in instrs.iter().enumerate() {
        let off = match &ins.op {
            ArmOp::BOffset { offset } => *offset,
            ArmOp::BCondOffset { offset, .. } => *offset,
            _ => continue,
        };
        if target_byte(i, off) <= byte[i] {
            return None;
        }
    }

    // Walk the linear body ONCE, tracking the masked quantity, the (single) base
    // guard with its index + taken target, and R0 as it feeds the self-call.
    let mut st = Walk::entry();
    // (predicate, guard_instr_index, taken_target_index)
    let mut guard: Option<(GuardPred, usize, usize)> = None;
    // R0's symbolic value captured at the instant just before the self-call.
    let mut arg_at_call: Option<Sym> = None;
    for (i, ins) in instrs.iter().enumerate() {
        if i == self_idx {
            arg_at_call = Some(st.reg(Reg::R0));
        }
        match &ins.op {
            ArmOp::BCondOffset { cond, offset } => {
                if let Some(p) = eval_guard(*cond, &st.flags) {
                    let tgt = target_byte(i, *offset);
                    let ti = idx_at(tgt)?;
                    // Only ONE base guard is modeled; a second distinct guard is a
                    // non-canonical shape → decline.
                    if guard.is_some() {
                        return None;
                    }
                    guard = Some((p, i, ti));
                }
                // A conditional branch that is NOT a recognized masked base guard
                // is fine as long as control-dependence still holds (checked below
                // via the recorded guard); it does not update regs/flags.
            }
            op => step_sym(op, &mut st),
        }
    }
    let (gpred, guard_idx, taken_idx) = guard?;
    let arg = arg_at_call?;

    // Control-dependence: the self-call must sit strictly AFTER the guard and
    // strictly BEFORE the guard's taken target (the base block), so it is provably
    // unreachable when the guard fires (base case). This is what stops the
    // dangerous `base - step` from ever re-entering the mask.
    if !(guard_idx < self_idx && self_idx < taken_idx) {
        return None;
    }

    // STRAIGHT-LINE + SINGLE-ENTRY region `(guard_idx, self_idx]`. The linear walk
    // applied the arg computation (the decrement) UNCONDITIONALLY; that is only a
    // valid model if the region between the guard and the self-call has NO control
    // flow — otherwise a runtime path could SKIP the decrement (passing `m`
    // unchanged) and recurse unbounded while the walk still saw `m - step`. Two
    // hard checks, the linear-body analog of the loop analyzer's branch discipline:
    //   (a) no branch instruction sits inside the region (unconditional body), and
    //   (b) no branch ANYWHERE targets a byte strictly inside the region (single
    //       entry — control cannot jump PAST the decrement into the self-call).
    if instrs[(guard_idx + 1)..=self_idx]
        .iter()
        .any(|ins| matches!(&ins.op, ArmOp::BOffset { .. } | ArmOp::BCondOffset { .. }))
    {
        return None; // (a) conditional/unconditional flow inside the region
    }
    let region_lo = byte[guard_idx + 1];
    let region_hi = byte[self_idx]; // byte of the self-call BL
    for (i, ins) in instrs.iter().enumerate() {
        let off = match &ins.op {
            ArmOp::BOffset { offset } => *offset,
            ArmOp::BCondOffset { offset, .. } => *offset,
            _ => continue,
        };
        let tgt = target_byte(i, off);
        // A target strictly INSIDE the region (after its first instruction, at or
        // before the self-call) is a second entry that could bypass the decrement.
        if tgt > region_lo && tgt <= region_hi {
            return None; // (b) mid-region entry — not single-entry
        }
    }

    // The self-call argument in R0 must be the SAME masked quantity minus a const
    // step (range containment: identical (base, mask) as the guard).
    let (abase, amask, aadd) = match arg {
        Sym::MaskedStep { base, mask, add } => (base, mask, add),
        _ => return None, // no const shift on the masked value → not a chain
    };
    if abase != gpred.base || amask != gpred.mask {
        return None; // different masked quantity — range containment broken
    }
    let step = aadd; // counter moves by `aadd` each frame (negative = countdown)
    if step == 0 {
        return None;
    }
    Some((gpred, step))
}

/// One symbolic step for a non-branch op. Models exactly the masked-chain ops;
/// everything else conservatively kills its destination (→ Top).
fn step_sym(op: &ArmOp, st: &mut Walk) {
    use ArmOp::*;
    match op {
        Mov { rd, op2 } => {
            let v = st.op2(op2);
            st.set(*rd, v);
            st.flags = None;
        }
        And { rd, rn, op2 } => {
            // The masking op: (param & const) → Masked. Only a param source with a
            // const mask is modeled.
            let v = match (st.reg(*rn), st.op2(op2)) {
                (Sym::Param(base), Sym::Const(mask)) => Sym::Masked { base, mask },
                _ => Sym::Top,
            };
            st.set(*rd, v);
            st.flags = None;
        }
        Add { rd, rn, op2 } | Adds { rd, rn, op2 } => {
            let v = masked_shift(st.reg(*rn), st.op2(op2), 1);
            st.set(*rd, v);
            st.flags = None;
        }
        Sub { rd, rn, op2 } | Subs { rd, rn, op2 } => {
            let v = masked_shift(st.reg(*rn), st.op2(op2), -1);
            st.set(*rd, v);
            st.flags = None;
        }
        Str { rd, addr } => {
            if addr.base == Reg::SP && addr.offset_reg.is_none() {
                st.slots.insert(addr.offset as i64, st.reg(*rd));
            }
        }
        Ldr { rd, addr } => {
            let v = if addr.base == Reg::SP && addr.offset_reg.is_none() {
                st.slots
                    .get(&(addr.offset as i64))
                    .copied()
                    .unwrap_or(Sym::Top)
            } else {
                Sym::Top
            };
            st.set(*rd, v);
        }
        Cmp { rn, op2 } => {
            st.flags = Some((st.reg(*rn), st.op2(op2)));
        }
        SetCond { rd, .. } => {
            // A cmp→setcond→cmp #0 chain: the guard predicate is recovered from the
            // ORIGINAL compare when the SetCond's boolean is later compared to 0.
            // We keep the flags (the first compare) so eval_guard can read them —
            // but SetCond writes a boolean into rd, so track that specially.
            st.set(*rd, Sym::Top);
            // NB: flags preserved (SetCond does not clobber the recorded compare in
            // our model) so the subsequent `Cmp rd,#0` can be tied back. However our
            // eval_guard reads the LAST compare; see eval_guard for the shape it
            // accepts.
        }
        Label { .. } | Nop => {}
        // Any other op: kill its destination register(s) conservatively.
        _ => {
            if let Some(rd) = dest_reg(op) {
                st.set(rd, Sym::Top);
            }
            st.flags = None;
        }
    }
}

/// `a + sign*b` restricted to the MaskedStep affine domain.
fn masked_shift(a: Sym, b: Sym, sign: i64) -> Sym {
    match (a, b) {
        (Sym::Const(x), Sym::Const(y)) => {
            i32::try_from(x as i64 + sign * y as i64).map_or(Sym::Top, Sym::Const)
        }
        (Sym::Masked { base, mask }, Sym::Const(y)) => {
            let add = sign * y as i64;
            if add.abs() <= 1 << 20 {
                Sym::MaskedStep { base, mask, add }
            } else {
                Sym::Top
            }
        }
        (Sym::MaskedStep { base, mask, add }, Sym::Const(y)) => {
            match add.checked_add(sign * y as i64) {
                Some(na) if na.abs() <= 1 << 20 => Sym::MaskedStep {
                    base,
                    mask,
                    add: na,
                },
                _ => Sym::Top,
            }
        }
        _ => Sym::Top,
    }
}

/// Recover the base-guard predicate over a masked quantity from the last compare.
///
/// The lowering shape (from the real stream) is
/// `Cmp (param&mask), #0 ; SetCond <cc> Rb ; Cmp Rb, #0 ; BCond EQ`.
/// But synth also emits the DIRECT `Cmp (param&mask), #rhs ; BCond <cc>` shape.
/// We accept the DIRECT masked compare (Masked vs Const) — the SetCond-boolean
/// indirection collapses to it because the WASM `eqz`/`if` lowering ultimately
/// branches on the masked value's relation to a constant.
fn eval_guard(cond: Condition, flags: &Option<(Sym, Sym)>) -> Option<GuardPred> {
    let (a, b) = flags.as_ref()?;
    match (a, b) {
        (Sym::Masked { base, mask }, Sym::Const(c)) => Some(GuardPred {
            base: *base,
            mask: *mask,
            add: 0,
            rel: Rel::of(cond),
            rhs: *c,
        }),
        (Sym::MaskedStep { base, mask, add }, Sym::Const(c)) => Some(GuardPred {
            base: *base,
            mask: *mask,
            add: *add,
            rel: Rel::of(cond),
            rhs: *c,
        }),
        _ => None,
    }
}

/// Best-effort destination register of an op (for conservative kills).
fn dest_reg(op: &ArmOp) -> Option<Reg> {
    use ArmOp::*;
    match op {
        Add { rd, .. }
        | Sub { rd, .. }
        | Adds { rd, .. }
        | Subs { rd, .. }
        | And { rd, .. }
        | Orr { rd, .. }
        | Eor { rd, .. }
        | Mov { rd, .. }
        | Movw { rd, .. }
        | Movt { rd, .. }
        | Lsl { rd, .. }
        | Lsr { rd, .. }
        | Asr { rd, .. }
        | Ror { rd, .. }
        | Mul { rd, .. }
        | Rsb { rd, .. }
        | Mvn { rd, .. }
        | Clz { rd, .. }
        | Uxtb { rd, .. }
        | Uxth { rd, .. }
        | Sxtb { rd, .. }
        | Sxth { rd, .. }
        | SetCond { rd, .. } => Some(*rd),
        _ => None,
    }
}
