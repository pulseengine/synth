//! #778 phase 2 (v0.47) — statically-evident loop trip counts + the `--wcet-hints`
//! sound-checker seam, over the FINAL Thumb-2 instruction stream.
//!
//! Phase 1 declined EVERY backward branch. This module upgrades exactly the
//! shapes it can PROVE and keeps declining everything else:
//!
//! - A **loop region** is `[head..=closer]` where `closer` is a backward
//!   `BOffset`/`BCondOffset` targeting `head`. Regions must nest properly.
//! - A region is **proven** when a tiny symbolic walk over its body shows the
//!   canonical counted-loop induction: a counter living in an SP-relative word
//!   slot, written EXACTLY once per iteration with `old + step` (const step),
//!   and an exit comparison against a CONST bound that provably fires once the
//!   counter reaches it (head-test `cmp; b<cond> → resume` or bottom-test
//!   conditional backward branch). The counter's INIT must be a const store
//!   found on the straight-line path into the head (function prologue for a
//!   top-level loop, the parent body for a nested one).
//! - Every instruction's worst-case cycle cost is then multiplied by its proven
//!   worst-case execution count: `K+1` for a head-test region (the head check
//!   runs once more than the body), `K` for a bottom-test region, multiplied
//!   through nesting. Anything unproven → the function keeps the loud `loop`
//!   decline.
//!
//! ## Soundness argument (why the multiplier is an upper bound)
//!
//! For a proven region entered with counter slot value `v`:
//!
//! 1. **Single entry**: the global branch discipline (below) guarantees control
//!    enters the region only at `head` — every other branch in the function is
//!    either a region closer (targeting its own head) or a region exit
//!    (targeting exactly its innermost region's fall-through resume point).
//! 2. **Monotone counter**: the walk proves the ONLY write to the counter slot
//!    on the straight-line body is `old + step`, and no sub-word/dynamic store
//!    can alias it (any such store taints the slot and fails the proof). SP
//!    itself cannot move inside a region (`push`/`pop`/SP-writes decline), and
//!    non-SP-based stores cannot alias the SP frame: WASM has no address-of-
//!    local, so synth-generated non-SP stores address the linear-memory/global
//!    image, which is layout-disjoint from the native stack frame (a sandbox-
//!    respecting execution — the same precondition the bound already carries).
//! 3. **Guaranteed exit**: the proven exit predicate `(v + a) REL bound` fires
//!    by the K-th head evaluation, where `K` is computed from (init, step,
//!    bound) in exact i64/u64 arithmetic WITH static no-overflow checks over
//!    the whole counter walk (a wrap would break monotonicity, so any possible
//!    wrap fails the proof). Early exits (extra conditional exits, traps) only
//!    REDUCE iteration counts, so ignoring their predicates is conservative.
//! 4. Anything the walk does not precisely model kills the affected symbolic
//!    state (registers → Top, flags → unknown, slots → tainted), which can only
//!    cause a DECLINE, never a smaller bound.
//!
//! **Equality exits are hint-gated**: a `(v + a) == bound` exit is the one shape
//! where an off-by-one (step not dividing the distance) flips terminating into
//! infinite. synth derives the trip count and verifies divisibility, but only
//! CONSUMES it when an explicit `--wcet-hints` entry asserts a bound the derived
//! count respects (`derived ≤ hint`) — the scry-oracle seam: the untrusted hint
//! asserts intent, synth's checker re-derives and cross-checks, and the emitted
//! trip count is always synth's own derived value, never the raw hint. A hint
//! below the derived count, or on a loop whose induction synth cannot verify
//! (data-dependent bound, non-canonical shape), is REJECTED with a machine
//! reason and never trusted into a bound.

use std::collections::BTreeMap;

use synth_core::wcet::{
    WcetFunctionHints, WcetHintReject, WcetHintRejection, WcetLoopBound, WcetLoopBoundSource,
};
use synth_synthesis::{ArmInstruction, ArmOp, Condition, Operand2, Reg};

/// Result of the loop analysis over one function's final instruction stream.
pub(crate) enum LoopAnalysis {
    /// No backward branches — the plain loop-free sum applies (multiplier 1).
    NoLoops {
        hint_rejections: Vec<WcetHintRejection>,
    },
    /// EVERY loop region proved a trip count: per-instruction execution-count
    /// multipliers (product of enclosing region factors, u128 to survive
    /// nesting) plus the per-loop bound records for the sidecar.
    Proven {
        multipliers: Vec<u128>,
        loops: Vec<WcetLoopBound>,
        hint_rejections: Vec<WcetHintRejection>,
    },
    /// At least one region could not be proven — the function keeps the loud
    /// `loop` decline; any offered hints that were rejected are recorded.
    Unproven {
        hint_rejections: Vec<WcetHintRejection>,
    },
}

// ---------------------------------------------------------------------------
// Symbolic domain
// ---------------------------------------------------------------------------

/// Comparison relation of a predicate over the counter, by signedness.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Rel {
    Eq,
    Ne,
    LtS,
    LeS,
    GtS,
    GeS,
    LoU,
    LsU,
    HiU,
    HsU,
}

impl Rel {
    pub(crate) fn of(cond: Condition) -> Rel {
        match cond {
            Condition::EQ => Rel::Eq,
            Condition::NE => Rel::Ne,
            Condition::LT => Rel::LtS,
            Condition::LE => Rel::LeS,
            Condition::GT => Rel::GtS,
            Condition::GE => Rel::GeS,
            Condition::LO => Rel::LoU,
            Condition::LS => Rel::LsU,
            Condition::HI => Rel::HiU,
            Condition::HS => Rel::HsU,
        }
    }

    /// Logical negation over the same operands.
    pub(crate) fn negate(self) -> Rel {
        match self {
            Rel::Eq => Rel::Ne,
            Rel::Ne => Rel::Eq,
            Rel::LtS => Rel::GeS,
            Rel::GeS => Rel::LtS,
            Rel::LeS => Rel::GtS,
            Rel::GtS => Rel::LeS,
            Rel::LoU => Rel::HsU,
            Rel::HsU => Rel::LoU,
            Rel::LsU => Rel::HiU,
            Rel::HiU => Rel::LsU,
        }
    }
}

/// A boolean predicate over the counter slot's REGION-ENTRY value `v`:
/// `(v + add) REL rhs`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Pred {
    /// SP-relative byte offset of the counter slot this predicate reads.
    pub(crate) off: i64,
    /// Constant added to the entry value before the comparison.
    pub(crate) add: i64,
    pub(crate) rel: Rel,
    pub(crate) rhs: i32,
    /// (#778 phase 5) The DATA-DEPENDENT masked bound: when the compare RHS is a
    /// masked value `x & K` (`K = masked_ceiling ≥ 0`), the real per-iteration
    /// bound lies in `[0, K]` for ANY runtime input (`x & K ∈ [0,K]`). `rhs` is
    /// then the ceiling `K` (the entry-independent worst case). The trip count is
    /// derived as the MAX over both endpoints of the bound domain (`rhs = K` and
    /// `rhs = 0`) — a single endpoint is unsound for count-DOWN shapes — and the
    /// result is always HINT-GATED (opt-in, mirroring the equality-exit gate).
    /// `None` for a normal const bound (unchanged phase-2 behavior).
    pub(crate) masked_ceiling: Option<i32>,
}

impl Pred {
    pub(crate) fn negate(self) -> Pred {
        Pred {
            rel: self.rel.negate(),
            ..self
        }
    }
}

/// Symbolic register/slot value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Sym {
    /// Unknown.
    Top,
    /// A compile-time constant (i32 bit pattern).
    Const(i32),
    /// `(value of [sp,#off] at region entry) + add`.
    Slot { off: i64, add: i64 },
    /// A 0/1 boolean holding `pred`.
    Bool(Pred),
    /// (#778 phase 5) A masked value `x & K` (`mask = K ≥ 0`), for ANY `x`. The
    /// value is entry-independently bounded to `[0, K]` — the base identity is
    /// irrelevant (`x & K ≤ K` regardless of what `x` holds), unlike the
    /// recursion module's masked chain which needs the base identity for the
    /// decrement. Used ONLY as a data-dependent loop-bound ceiling (the compare
    /// RHS); the trip count it yields is always hint-gated.
    Masked { mask: i32 },
}

/// Walk state: symbolic registers, slot writes since walk start, tainted slots
/// (unreliable after a sub-word/unaligned store), and the last compare.
#[derive(Clone)]
struct WalkState {
    regs: [Sym; 16],
    /// Word-aligned SP-relative offsets written during THIS walk.
    written: BTreeMap<i64, Sym>,
    /// Offsets whose content is unreliable (sub-word overlap). A later full
    /// word store un-taints (it fully replaces the slot).
    tainted: std::collections::BTreeSet<i64>,
    /// Operands of the last flag-setting compare, when precisely known.
    flags: Option<(Sym, Sym)>,
}

impl WalkState {
    fn fresh() -> Self {
        WalkState {
            regs: [Sym::Top; 16],
            written: BTreeMap::new(),
            tainted: std::collections::BTreeSet::new(),
            flags: None,
        }
    }

    fn reg(&self, r: Reg) -> Sym {
        self.regs[r as usize]
    }

    fn set_reg(&mut self, r: Reg, v: Sym) {
        self.regs[r as usize] = v;
    }

    fn kill_all_regs(&mut self) {
        self.regs = [Sym::Top; 16];
    }

    fn op2(&self, op2: &Operand2) -> Sym {
        match op2 {
            Operand2::Imm(c) => Sym::Const(*c),
            Operand2::Reg(r) => self.reg(*r),
            Operand2::RegShift { .. } => Sym::Top,
        }
    }

    /// Read a word slot `[sp,#off]`: the value written during this walk, else
    /// the symbolic entry value `Slot{off,0}`.
    fn read_slot(&self, off: i64) -> Sym {
        if off % 4 != 0 || self.tainted.contains(&off) {
            return Sym::Top;
        }
        self.written
            .get(&off)
            .copied()
            .unwrap_or(Sym::Slot { off, add: 0 })
    }

    fn write_slot_word(&mut self, off: i64, v: Sym) {
        if off % 4 == 0 {
            // A full word store replaces the slot entirely — un-taint.
            self.tainted.remove(&off);
            self.written.insert(off, v);
        } else {
            // Unaligned word store touches two words: taint both.
            self.taint_range(off, 4);
        }
    }

    /// Mark every word overlapping `[off, off+width)` unreliable.
    fn taint_range(&mut self, off: i64, width: i64) {
        let first = off & !3;
        let last = (off + width - 1) & !3;
        let mut w = first;
        while w <= last {
            self.written.remove(&w);
            self.tainted.insert(w);
            w += 4;
        }
    }
}

/// Evaluate the predicate a condition computes over the last compare.
fn eval_pred(cond: Condition, flags: &Option<(Sym, Sym)>) -> Option<Pred> {
    let (a, b) = flags.as_ref()?;
    match (a, b) {
        (Sym::Slot { off, add }, Sym::Const(c)) => Some(Pred {
            off: *off,
            add: *add,
            rel: Rel::of(cond),
            rhs: *c,
            masked_ceiling: None,
        }),
        // (#778 phase 5) `cmp <counter slot>, <masked value>` — the counter is
        // compared against a DATA-DEPENDENT masked bound `x & K ∈ [0, K]`. The
        // ceiling `K` is the entry-independent worst case (`rhs = K`); the trip
        // this yields is derived at BOTH endpoints of `[0, K]` and hint-gated.
        (Sym::Slot { off, add }, Sym::Masked { mask }) => Some(Pred {
            off: *off,
            add: *add,
            rel: Rel::of(cond),
            rhs: *mask,
            masked_ceiling: Some(*mask),
        }),
        // `cmp <bool>, #0` — the eqz / br_if lowering shape. The bool carries the
        // ORIGINAL predicate (including any masked_ceiling), so a masked bound
        // survives the SetCond→cmp#0 indirection.
        (Sym::Bool(p), Sym::Const(0)) => match cond {
            Condition::EQ => Some(p.negate()),
            Condition::NE => Some(*p),
            _ => None,
        },
        _ => None,
    }
}

// ---------------------------------------------------------------------------
// Regions
// ---------------------------------------------------------------------------

/// The exit shape a region's trip count is derived from.
#[derive(Debug, Clone, Copy)]
enum ExitShape {
    /// Head-test: unconditional backward closer; `pred` (on some forward exit
    /// branch) is TRUE ⇒ control leaves the region. Factor = K + 1.
    HeadTest(Pred),
    /// Bottom-test: conditional backward closer; `pred` TRUE ⇒ another
    /// iteration. Factor = K.
    BottomTest(Pred),
}

struct Region {
    /// Instruction index of the loop head (backward-branch target).
    head: usize,
    /// Instruction index of the closing backward branch.
    closer: usize,
    /// `Some(cond)` when the closer is a conditional (bottom-test) branch.
    closer_cond: Option<Condition>,
    /// Immediate children (indices into the region vec), ascending head.
    children: Vec<usize>,
    /// Whether some other region directly contains this one.
    has_parent: bool,
    // --- proof results ---
    /// Counter slot offset, step, and exit shape (from the structure walk).
    proof: Option<(i64, i64, ExitShape)>,
    /// Constant initial counter value (resolved by the enclosing walk).
    init: Option<i32>,
    /// Proven trip count (body executions) + whether it is hint-gated.
    trip: Option<(u64, bool)>,
    /// (#778 phase 5) True when the exit bound is a DATA-DEPENDENT masked ceiling
    /// (`x & K`) rather than a literal const — the accepted bound then carries
    /// the `MaskCeiling` source so the sidecar states the extra assumption.
    masked_bound: bool,
    /// Per-iteration execution-count factor for instructions in this region.
    factor: u128,
}

/// Analyze the loop structure of `instrs`. `hints` is the (already
/// name-matched) UNTRUSTED per-function hint entry, if any.
pub(crate) fn analyze_loops(
    instrs: &[ArmInstruction],
    hints: Option<&WcetFunctionHints>,
) -> LoopAnalysis {
    // Byte positions from the REAL encoder — the SAME source of truth
    // `resolve_label_branches` computed the `BOffset`/`BCondOffset` halfword
    // displacements against. (The `estimate_arm_byte_size` estimator is NOT
    // exact for every op — e.g. a high-register `SetCond` widens its IT-block
    // MOVs to 10 bytes where the estimate is 6 — and a drifted layout would
    // reconstruct branch targets off-by-N, so the estimator must not be used
    // here.) Any op the encoder refuses → conservatively unproven.
    let n = instrs.len();
    let encoder = crate::arm_encoder::ArmEncoder::new_thumb2();
    let mut sizes: Vec<i64> = Vec::with_capacity(n);
    for instr in instrs {
        match encoder.encode(&instr.op) {
            Ok(bytes) => sizes.push(bytes.len() as i64),
            Err(_) => return unproven(hints, &[]),
        }
    }
    let mut positions = Vec::with_capacity(n);
    let mut pos: i64 = 0;
    for &sz in &sizes {
        positions.push(pos);
        pos += sz;
    }
    // Byte offset → FIRST instruction index at that offset (labels are 0-size).
    let mut idx_at: BTreeMap<i64, usize> = BTreeMap::new();
    for (i, &p) in positions.iter().enumerate() {
        idx_at.entry(p).or_insert(i);
    }
    let target_byte = |i: usize, offset: i32| positions[i] + 4 + (offset as i64) * 2;

    // ---- collect regions from backward branches ----
    let mut regions: Vec<Region> = Vec::new();
    for (i, instr) in instrs.iter().enumerate() {
        let (offset, cond) = match &instr.op {
            ArmOp::BOffset { offset } => (*offset, None),
            ArmOp::BCondOffset { cond, offset } => (*offset, Some(*cond)),
            _ => continue,
        };
        let tgt = target_byte(i, offset);
        if tgt > positions[i] {
            continue; // forward — validated by the branch discipline below
        }
        let Some(&head) = idx_at.get(&tgt) else {
            return unproven(hints, &[]); // target not at an instruction start
        };
        if head > i {
            return unproven(hints, &[]);
        }
        regions.push(Region {
            head,
            closer: i,
            closer_cond: cond,
            children: Vec::new(),
            has_parent: false,
            proof: None,
            init: None,
            trip: None,
            masked_bound: false,
            factor: 1,
        });
    }
    if regions.is_empty() {
        // Loop-free: any hints offered for this function address nonexistent
        // loops — reject them loudly rather than silently ignoring them.
        return LoopAnalysis::NoLoops {
            hint_rejections: reject_extra_hints(hints, 0, &[]),
        };
    }

    // Loop order for hint indexing + the sidecar: ascending head byte offset.
    regions.sort_by_key(|r| (positions[r.head], r.closer));
    let head_offsets: Vec<i64> = regions.iter().map(|r| positions[r.head]).collect();

    // ---- structural sanity: distinct heads, proper nesting ----
    for w in regions.windows(2) {
        if w[0].head == w[1].head {
            return unproven(hints, &head_offsets);
        }
    }
    for a in 0..regions.len() {
        for b in 0..regions.len() {
            if a == b {
                continue;
            }
            let (ra, rb) = (&regions[a], &regions[b]);
            let disjoint = ra.closer < rb.head || rb.closer < ra.head;
            let a_in_b = rb.head < ra.head && ra.closer < rb.closer;
            let b_in_a = ra.head < rb.head && rb.closer < ra.closer;
            if !(disjoint || a_in_b || b_in_a) {
                return unproven(hints, &head_offsets);
            }
        }
    }
    // Parent/child links (immediate containment).
    for a in 0..regions.len() {
        let mut parent: Option<usize> = None;
        for b in 0..regions.len() {
            if b == a {
                continue;
            }
            if regions[b].head < regions[a].head && regions[a].closer < regions[b].closer {
                // b contains a; keep the tightest.
                if parent.is_none_or(|p| {
                    regions[b].closer - regions[b].head < regions[p].closer - regions[p].head
                }) {
                    parent = Some(b);
                }
            }
        }
        if let Some(p) = parent {
            regions[a].has_parent = true;
            regions[p].children.push(a);
        }
    }
    for r in &mut regions {
        r.children.sort_by_key(|&c| c); // regions vec is head-sorted already
    }

    // ---- global branch discipline ----
    // Every branch must be (a) a region closer, or (b) a forward conditional
    // branch inside a region targeting EXACTLY its innermost region's resume
    // point (the byte after the closer). Anything else → unproven.
    let innermost_of = |i: usize| -> Option<usize> {
        regions
            .iter()
            .enumerate()
            .filter(|(_, r)| r.head <= i && i <= r.closer)
            .min_by_key(|(_, r)| r.closer - r.head)
            .map(|(k, _)| k)
    };
    for (i, instr) in instrs.iter().enumerate() {
        let (offset, is_cond) = match &instr.op {
            ArmOp::BOffset { offset } => (*offset, false),
            ArmOp::BCondOffset { offset, .. } => (*offset, true),
            _ => continue,
        };
        if regions.iter().any(|r| r.closer == i) {
            continue; // a closer — backward to its own head by construction
        }
        let tgt = target_byte(i, offset);
        if tgt <= positions[i] {
            return unproven(hints, &head_offsets); // backward non-closer (unreachable)
        }
        if !is_cond {
            return unproven(hints, &head_offsets); // forward unconditional (if/else) — non-canonical
        }
        let Some(rid) = innermost_of(i) else {
            return unproven(hints, &head_offsets); // conditional CF outside any loop
        };
        let resume = positions[regions[rid].closer] + sizes[regions[rid].closer];
        if tgt != resume {
            return unproven(hints, &head_offsets); // mid-region or multi-level exit
        }
    }

    // ---- per-region hard checks: nothing may move SP inside a region ----
    for r in &regions {
        for instr in &instrs[r.head..=r.closer] {
            match &instr.op {
                ArmOp::Push { .. } | ArmOp::Pop { .. } | ArmOp::Bx { .. } => {
                    return unproven(hints, &head_offsets);
                }
                op => {
                    if writes_sp(op) {
                        return unproven(hints, &head_offsets);
                    }
                    // A dynamic or non-word-offset SP store inside a region is
                    // handled by the walk (it taints), but a dynamic SP STORE
                    // could alias ANY slot — refuse outright.
                    if let ArmOp::Str { addr, .. }
                    | ArmOp::Strb { addr, .. }
                    | ArmOp::Strh { addr, .. } = op
                        && addr.base == Reg::SP
                        && addr.offset_reg.is_some()
                    {
                        return unproven(hints, &head_offsets);
                    }
                }
            }
        }
    }

    // ---- structure walks, innermost first ----
    let mut order: Vec<usize> = (0..regions.len()).collect();
    order.sort_by_key(|&k| regions[k].closer - regions[k].head);
    for k in order {
        if !prove_region_structure(&mut regions, k, instrs) {
            return unproven(hints, &head_offsets);
        }
    }

    // ---- function-level walk: resolve top-level regions' inits ----
    if !resolve_toplevel_inits(&mut regions, instrs) {
        return unproven(hints, &head_offsets);
    }

    // ---- trip counts ----
    for r in &mut regions {
        let (Some((_, step, shape)), Some(init)) = (r.proof, r.init) else {
            r.trip = None;
            continue;
        };
        r.masked_bound = match shape {
            ExitShape::HeadTest(p) | ExitShape::BottomTest(p) => p.masked_ceiling.is_some(),
        };
        r.trip = match shape {
            ExitShape::HeadTest(p) => masked_exit_index(init, step, &p),
            ExitShape::BottomTest(p) => {
                // Body n (n ≥ 1) enters with v = init + (n−1)·step and repeats
                // while `pred` holds. K = 1 + (first m ≥ 0 where ¬pred fires).
                masked_exit_index(init, step, &p.negate())
                    .and_then(|(m, h)| m.checked_add(1).map(|k| (k, h)))
            }
        };
    }

    // ---- hints: verify / reject (the scry seam) ----
    let mut rejections: Vec<WcetHintRejection> = Vec::new();
    let empty = Vec::new();
    let hint_list: &Vec<Option<u64>> = hints.map_or(&empty, |h| &h.loop_bounds);
    let mut loops_out: Vec<WcetLoopBound> = Vec::new();
    let mut all_proven = true;
    for (idx, r) in regions.iter_mut().enumerate() {
        let hint = hint_list.get(idx).copied().flatten();
        let head_off = positions[r.head] as u64;
        let (accepted, source): (Option<u64>, WcetLoopBoundSource) = match (r.trip, hint) {
            // Fully static proof; no hint offered.
            (Some((k, false)), None) => (Some(k), WcetLoopBoundSource::Static),
            // Static proof + hint: the hint is cross-checked. A hint BELOW the
            // derived trip is a wrong oracle claim — reject it loudly (the
            // static bound stands on synth's own proof).
            (Some((k, false)), Some(h)) => {
                if h < k {
                    rejections.push(rejection(
                        idx,
                        Some(head_off),
                        h,
                        WcetHintReject::HintBelowDerivedTrip,
                    ));
                }
                (Some(k), WcetLoopBoundSource::Static)
            }
            // Hint-gated shape (equality-exit OR data-dependent masked ceiling,
            // #778 phase 5): unhinted → keep the `loop` decline. A bound resting
            // on either assumption is opt-in.
            (Some((_, true)), None) => (None, WcetLoopBoundSource::Static),
            // Hint-gated shape WITH a hint: consume ONLY if derived ≤ hint. The
            // accepted source distinguishes a masked ceiling from an equality
            // exit so the sidecar states which assumption the bound rests on. The
            // emitted trip is always synth's DERIVED value, never the raw hint.
            (Some((k, true)), Some(h)) => {
                if k <= h {
                    let source = if r.masked_bound {
                        WcetLoopBoundSource::MaskCeiling
                    } else {
                        WcetLoopBoundSource::HintVerified
                    };
                    (Some(k), source)
                } else {
                    rejections.push(rejection(
                        idx,
                        Some(head_off),
                        h,
                        WcetHintReject::HintBelowDerivedTrip,
                    ));
                    (None, WcetLoopBoundSource::Static)
                }
            }
            // Unproven induction: any hint is unverifiable — never trusted.
            (None, Some(h)) => {
                rejections.push(rejection(
                    idx,
                    Some(head_off),
                    h,
                    WcetHintReject::HintUnverifiableInduction,
                ));
                (None, WcetLoopBoundSource::Static)
            }
            (None, None) => (None, WcetLoopBoundSource::Static),
        };
        match accepted {
            Some(k) => {
                r.factor = match r.closer_cond {
                    // Head-test: the head check runs K+1 times.
                    None => k as u128 + 1,
                    // Bottom-test: every region instruction runs exactly K times.
                    Some(_) => (k as u128).max(1),
                };
                loops_out.push(WcetLoopBound {
                    head_offset: head_off,
                    trip_count: k,
                    region_instr_count: r.closer - r.head + 1,
                    source,
                    hint: match source {
                        WcetLoopBoundSource::HintVerified | WcetLoopBoundSource::MaskCeiling => {
                            hint
                        }
                        WcetLoopBoundSource::Static => None,
                    },
                });
            }
            None => all_proven = false,
        }
    }
    rejections.extend(reject_extra_hints(hints, regions.len(), &head_offsets));

    if !all_proven {
        return LoopAnalysis::Unproven {
            hint_rejections: rejections,
        };
    }

    // ---- per-instruction multipliers ----
    let mut multipliers = vec![1u128; n];
    for r in &regions {
        for m in multipliers.iter_mut().take(r.closer + 1).skip(r.head) {
            *m = m.saturating_mul(r.factor);
        }
    }
    LoopAnalysis::Proven {
        multipliers,
        loops: loops_out,
        hint_rejections: rejections,
    }
}

fn rejection(
    loop_index: usize,
    head_offset: Option<u64>,
    hint: u64,
    reason: WcetHintReject,
) -> WcetHintRejection {
    let note = reason.note().to_string();
    WcetHintRejection {
        loop_index,
        head_offset,
        hint,
        reason,
        note,
    }
}

/// Reject hint entries beyond the function's real loop count.
fn reject_extra_hints(
    hints: Option<&WcetFunctionHints>,
    loop_count: usize,
    _head_offsets: &[i64],
) -> Vec<WcetHintRejection> {
    let Some(h) = hints else {
        return Vec::new();
    };
    h.loop_bounds
        .iter()
        .enumerate()
        .skip(loop_count)
        .filter_map(|(i, b)| b.map(|v| rejection(i, None, v, WcetHintReject::HintUnknownLoop)))
        .collect()
}

/// Unproven WITHOUT any structure info: every offered hint is unverifiable.
fn unproven(hints: Option<&WcetFunctionHints>, head_offsets: &[i64]) -> LoopAnalysis {
    let rejections = hints
        .map(|h| {
            h.loop_bounds
                .iter()
                .enumerate()
                .filter_map(|(i, b)| {
                    b.map(|v| {
                        rejection(
                            i,
                            head_offsets.get(i).map(|&o| o as u64),
                            v,
                            WcetHintReject::HintUnverifiableInduction,
                        )
                    })
                })
                .collect()
        })
        .unwrap_or_default();
    LoopAnalysis::Unproven {
        hint_rejections: rejections,
    }
}

// ---------------------------------------------------------------------------
// Structure walk
// ---------------------------------------------------------------------------

/// Prove region `k`'s induction structure: counter slot, const step, exit
/// predicate. Children must already be proven (innermost-first order); their
/// inits are resolved here (a child's init store lives in THIS region's body).
fn prove_region_structure(regions: &mut [Region], k: usize, instrs: &[ArmInstruction]) -> bool {
    let (head, closer) = (regions[k].head, regions[k].closer);
    let mut st = WalkState::fresh();
    // (off, sym, order) of every word SP store on the region's own body.
    let mut store_events: Vec<(i64, Sym)> = Vec::new();
    // Exit predicates from forward conditional exits (branch TAKEN ⇒ leave).
    let mut exits: Vec<Option<Pred>> = Vec::new();

    let mut i = head;
    while i <= closer {
        // Child region: resolve its init from the current state, then skip it.
        if let Some(&c) = regions[k].children.iter().find(|&&c| regions[c].head == i) {
            let c_off = match regions[c].proof {
                Some((off, _, _)) => off,
                None => return false, // child unproven → parent unprovable
            };
            match st.read_slot(c_off) {
                Sym::Const(init) => {
                    // The same const init is stored on the straight-line path
                    // before the child head on EVERY parent iteration.
                    regions[c].init = Some(init);
                }
                _ => return false,
            }
            // Kill everything the child may change: registers (its body uses
            // scratch freely), flags, and every slot it stores to.
            st.kill_all_regs();
            st.flags = None;
            for instr in &instrs[regions[c].head..=regions[c].closer] {
                match &instr.op {
                    ArmOp::Str { addr, .. } if addr.base == Reg::SP => {
                        st.taint_range(addr.offset as i64, 4);
                    }
                    ArmOp::Strb { addr, .. } if addr.base == Reg::SP => {
                        st.taint_range(addr.offset as i64, 1);
                    }
                    ArmOp::Strh { addr, .. } if addr.base == Reg::SP => {
                        st.taint_range(addr.offset as i64, 2);
                    }
                    _ => {}
                }
            }
            i = regions[c].closer + 1;
            continue;
        }

        let instr = &instrs[i];
        match &instr.op {
            ArmOp::BOffset { .. } if i == closer => break, // head-test closer
            ArmOp::BCondOffset { cond, .. } if i == closer => {
                // Bottom-test closer: TAKEN ⇒ another iteration.
                let Some(p) = eval_pred(*cond, &st.flags) else {
                    return false;
                };
                let Some((off, step, _)) = counter_candidate(&st, &store_events, &[Some(p)]) else {
                    return false;
                };
                if p.off != off {
                    return false;
                }
                regions[k].proof = Some((off, step, ExitShape::BottomTest(p)));
                return true;
            }
            ArmOp::BCondOffset { cond, .. } => {
                // Forward exit (global discipline verified the target). TAKEN ⇒
                // leave the region; fall through otherwise. Unknown predicates
                // are early exits — sound to ignore.
                exits.push(eval_pred(*cond, &st.flags));
            }
            ArmOp::BOffset { .. } => return false, // forward BOffset inside region
            op => sym_step(op, &mut st, &mut store_events),
        }
        i += 1;
    }

    // Head-test: pick the counter/exit pair.
    let Some((off, step, pred)) = counter_candidate(&st, &store_events, &exits) else {
        return false;
    };
    regions[k].proof = Some((off, step, ExitShape::HeadTest(pred)));
    true
}

/// Find the counter slot: a word slot written EXACTLY once on the body with
/// `entry + step` (step ≠ 0), still holding that value at the end of the walk
/// (no child kill, no taint), that some usable exit predicate reads.
fn counter_candidate(
    st: &WalkState,
    store_events: &[(i64, Sym)],
    exits: &[Option<Pred>],
) -> Option<(i64, i64, Pred)> {
    for p in exits.iter().flatten() {
        let off = p.off;
        if st.tainted.contains(&off) {
            continue;
        }
        let events: Vec<&Sym> = store_events
            .iter()
            .filter(|(o, _)| *o == off)
            .map(|(_, s)| s)
            .collect();
        if events.len() != 1 {
            continue;
        }
        let Sym::Slot { off: so, add: step } = *events[0] else {
            continue;
        };
        if so != off || step == 0 {
            continue;
        }
        // The final state must still show the increment (nothing killed it).
        if st.written.get(&off) != Some(&Sym::Slot { off, add: step }) {
            continue;
        }
        return Some((off, step, *p));
    }
    None
}

/// One symbolic step for a non-control op. Precisely models the ops the
/// canonical counted-loop chain is built from; everything else conservatively
/// kills exactly what it can define (or all registers for multi-instruction
/// encoder expansions with scratch clobbers).
fn sym_step(op: &ArmOp, st: &mut WalkState, store_events: &mut Vec<(i64, Sym)>) {
    use ArmOp::*;
    match op {
        Mov { rd, op2 } => {
            let v = st.op2(op2);
            st.set_reg(*rd, v);
            st.flags = None; // 16-bit MOVS immediate sets flags
        }
        Movw { rd, imm16 } => {
            st.set_reg(*rd, Sym::Const(*imm16 as i32));
            st.flags = None;
        }
        Add { rd, rn, op2 } | Adds { rd, rn, op2 } => {
            let v = sym_add(st.reg(*rn), st.op2(op2), 1);
            st.set_reg(*rd, v);
            st.flags = None; // ADDS sets flags; we don't model add-flags
        }
        Sub { rd, rn, op2 } | Subs { rd, rn, op2 } => {
            let v = sym_add(st.reg(*rn), st.op2(op2), -1);
            st.set_reg(*rd, v);
            st.flags = None;
        }
        Ldr { rd, addr } => {
            let v = if addr.base == Reg::SP && addr.offset_reg.is_none() {
                st.read_slot(addr.offset as i64)
            } else {
                Sym::Top
            };
            st.set_reg(*rd, v);
            // Loads never set flags.
        }
        Ldrb { rd, addr } | Ldrh { rd, addr } | Ldrsb { rd, addr } | Ldrsh { rd, addr } => {
            let _ = addr;
            st.set_reg(*rd, Sym::Top);
        }
        LdrSym { rd, .. } => st.set_reg(*rd, Sym::Top),
        Str { rd, addr } => {
            if addr.base == Reg::SP {
                if addr.offset_reg.is_none() {
                    let off = addr.offset as i64;
                    let v = st.reg(*rd);
                    st.write_slot_word(off, v);
                    if off % 4 == 0 {
                        store_events.push((off, v));
                    }
                } else {
                    // Dynamic SP store (pre-declined inside regions; harden
                    // anyway): could alias anything.
                    let offs: Vec<i64> = st.written.keys().copied().collect();
                    for o in offs {
                        st.taint_range(o, 4);
                    }
                }
            }
            // Non-SP stores address the linear-memory/global image — layout-
            // disjoint from the SP frame (see module doc, soundness point 2).
        }
        Strb { rd: _, addr } => {
            if addr.base == Reg::SP && addr.offset_reg.is_none() {
                st.taint_range(addr.offset as i64, 1);
            }
        }
        Strh { rd: _, addr } => {
            if addr.base == Reg::SP && addr.offset_reg.is_none() {
                st.taint_range(addr.offset as i64, 2);
            }
        }
        Cmp { rn, op2 } => {
            st.flags = Some((st.reg(*rn), st.op2(op2)));
        }
        Cmn { .. } => st.flags = None,
        SetCond { rd, cond } => {
            // IT + MOV + MOV: writes rd, PRESERVES the compare's flags.
            let v = eval_pred(*cond, &st.flags).map_or(Sym::Top, Sym::Bool);
            st.set_reg(*rd, v);
        }
        SelectMove { rd, .. } => {
            st.set_reg(*rd, Sym::Top); // conditional write — value unknown
        }
        Label { .. } | Nop => {}
        Udf { .. } => {
            // Execution faults and never continues — over-approximating as a
            // state kill is sound.
            st.kill_all_regs();
            st.flags = None;
        }
        // (#778 phase 5) `And rd, _, #K` with a NON-NEGATIVE const mask yields a
        // value in `[0, K]` for ANY input (`x & K ≤ K`, and `≥ 0` because K's
        // sign bit is clear). A masked value with K's sign bit SET (`K < 0`,
        // e.g. 0xFFFFFFFF) can be negative — the ceiling reasoning collapses —
        // so only a non-negative mask is tracked; everything else kills rd.
        And { rd, op2, .. } => {
            let v = match st.op2(op2) {
                Sym::Const(mask) if mask >= 0 => Sym::Masked { mask },
                _ => Sym::Top,
            };
            st.set_reg(*rd, v);
            st.flags = None;
        }
        // Single-register-destination ALU ops: kill exactly rd.
        Orr { rd, .. }
        | Eor { rd, .. }
        | Rsb { rd, .. }
        | Mvn { rd, .. }
        | Adc { rd, .. }
        | Sbc { rd, .. }
        | Movt { rd, .. }
        | MovwSym { rd, .. }
        | MovtSym { rd, .. }
        | Clz { rd, .. }
        | Rbit { rd, .. }
        | Sxtb { rd, .. }
        | Sxth { rd, .. }
        | Uxtb { rd, .. }
        | Uxth { rd, .. }
        | Lsl { rd, .. }
        | Lsr { rd, .. }
        | Asr { rd, .. }
        | Ror { rd, .. }
        | LslReg { rd, .. }
        | LsrReg { rd, .. }
        | AsrReg { rd, .. }
        | RorReg { rd, .. }
        | Mul { rd, .. }
        | Mla { rd, .. }
        | Mls { rd, .. }
        | Sdiv { rd, .. }
        | Udiv { rd, .. } => {
            st.set_reg(*rd, Sym::Top);
            st.flags = None;
        }
        Umull { rdlo, rdhi, .. } => {
            st.set_reg(*rdlo, Sym::Top);
            st.set_reg(*rdhi, Sym::Top);
            st.flags = None;
        }
        // Everything else (multi-instruction encoder expansions clobber scratch
        // registers not named in the op; off-path pseudos never reach here):
        // kill all registers and flags. Slots survive — only Str*/Push write
        // the SP frame, and Push/Pop are pre-declined inside regions.
        _ => {
            st.kill_all_regs();
            st.flags = None;
        }
    }
}

/// Symbolic add/sub: `a + sign·b` when it stays exactly representable.
fn sym_add(a: Sym, b: Sym, sign: i64) -> Sym {
    match (a, b) {
        (Sym::Const(x), Sym::Const(y)) => {
            let r = x as i64 + sign * y as i64;
            i32::try_from(r).map_or(Sym::Top, Sym::Const)
        }
        (Sym::Slot { off, add }, Sym::Const(y)) => {
            match add.checked_add(sign * y as i64) {
                // Keep the affine offset well inside i64 so later trip math in
                // i128 cannot overflow.
                Some(na) if na.abs() <= 1 << 33 => Sym::Slot { off, add: na },
                _ => Sym::Top,
            }
        }
        (Sym::Const(x), Sym::Slot { off, add }) if sign == 1 => match add.checked_add(x as i64) {
            Some(na) if na.abs() <= 1 << 33 => Sym::Slot { off, add: na },
            _ => Sym::Top,
        },
        _ => Sym::Top,
    }
}

/// `writes_sp` — does this op define SP? (Loop regions refuse any SP motion;
/// the function-level walk re-bases on the immediate push/pop/add/sub forms and
/// gives up on anything else.) Exhaustive over every `rd`-carrying op the
/// priced instruction set can contain; multi-instruction encoder expansions
/// never target SP (audited: arithmetic scratch only, I64Popcnt's push/pop is
/// SP-net-zero and it is a whole-function `LoopedExpansion` decline anyway).
fn writes_sp(op: &ArmOp) -> bool {
    use ArmOp::*;
    match op {
        Add { rd, .. }
        | Sub { rd, .. }
        | Adds { rd, .. }
        | Subs { rd, .. }
        | Adc { rd, .. }
        | Sbc { rd, .. }
        | Mov { rd, .. }
        | Mvn { rd, .. }
        | Movw { rd, .. }
        | Movt { rd, .. }
        | MovwSym { rd, .. }
        | MovtSym { rd, .. }
        | And { rd, .. }
        | Orr { rd, .. }
        | Eor { rd, .. }
        | Rsb { rd, .. }
        | Clz { rd, .. }
        | Rbit { rd, .. }
        | Sxtb { rd, .. }
        | Sxth { rd, .. }
        | Uxtb { rd, .. }
        | Uxth { rd, .. }
        | Lsl { rd, .. }
        | Lsr { rd, .. }
        | Asr { rd, .. }
        | Ror { rd, .. }
        | LslReg { rd, .. }
        | LsrReg { rd, .. }
        | AsrReg { rd, .. }
        | RorReg { rd, .. }
        | Mul { rd, .. }
        | Mla { rd, .. }
        | Mls { rd, .. }
        | Sdiv { rd, .. }
        | Udiv { rd, .. }
        | Popcnt { rd, .. }
        | Ldr { rd, .. }
        | Ldrb { rd, .. }
        | Ldrh { rd, .. }
        | Ldrsb { rd, .. }
        | Ldrsh { rd, .. }
        | LdrSym { rd, .. }
        | SetCond { rd, .. }
        | SelectMove { rd, .. } => *rd == Reg::SP,
        Umull { rdlo, rdhi, .. } => *rdlo == Reg::SP || *rdhi == Reg::SP,
        Push { .. } | Pop { .. } => true,
        _ => false,
    }
}

// ---------------------------------------------------------------------------
// Function-level walk (init resolution for top-level regions)
// ---------------------------------------------------------------------------

/// Walk the function linearly from index 0, tracking const stores into the SP
/// frame, to resolve each TOP-LEVEL region's counter init; regions are skipped
/// opaquely (their effects killed). SP motion outside regions (prologue
/// push/sub) re-bases the tracked offsets. Returns false when an init cannot
/// be proven const.
fn resolve_toplevel_inits(regions: &mut [Region], instrs: &[ArmInstruction]) -> bool {
    let mut st = WalkState::fresh();
    let mut events: Vec<(i64, Sym)> = Vec::new();
    let mut i = 0usize;
    while i < instrs.len() {
        // Top-level region head?
        if let Some(k) =
            (0..regions.len()).find(|&k| !regions[k].has_parent && regions[k].head == i)
        {
            let off = match regions[k].proof {
                Some((off, _, _)) => off,
                None => return false,
            };
            match st.read_slot(off) {
                Sym::Const(init) => regions[k].init = Some(init),
                _ => return false,
            }
            // Skip the region opaquely.
            st.kill_all_regs();
            st.flags = None;
            for instr in &instrs[regions[k].head..=regions[k].closer] {
                match &instr.op {
                    ArmOp::Str { addr, .. } if addr.base == Reg::SP => {
                        st.taint_range(addr.offset as i64, 4);
                    }
                    ArmOp::Strb { addr, .. } if addr.base == Reg::SP => {
                        st.taint_range(addr.offset as i64, 1);
                    }
                    ArmOp::Strh { addr, .. } if addr.base == Reg::SP => {
                        st.taint_range(addr.offset as i64, 2);
                    }
                    _ => {}
                }
            }
            i = regions[k].closer + 1;
            continue;
        }

        let instr = &instrs[i];
        match &instr.op {
            // SP motion outside regions: re-base tracked slot offsets. After
            // `sub sp,#k` an address SP_old+off is SP_new+(off+k).
            ArmOp::Push { regs } => shift_slots(&mut st, 4 * regs.len() as i64),
            ArmOp::Pop { regs } => shift_slots(&mut st, -4 * (regs.len() as i64)),
            ArmOp::Sub { rd, rn, op2 } | ArmOp::Subs { rd, rn, op2 }
                if *rd == Reg::SP && *rn == Reg::SP =>
            {
                match op2 {
                    Operand2::Imm(k) => shift_slots(&mut st, *k as i64),
                    _ => return false, // dynamic SP adjust — give up
                }
            }
            ArmOp::Add { rd, rn, op2 } | ArmOp::Adds { rd, rn, op2 }
                if *rd == Reg::SP && *rn == Reg::SP =>
            {
                match op2 {
                    Operand2::Imm(k) => shift_slots(&mut st, -(*k as i64)),
                    _ => return false,
                }
            }
            op if writes_sp(op) => return false, // any other SP write — give up
            ArmOp::Bx { .. } => {
                // A return: nothing after it can be reached by fallthrough, and
                // all remaining region heads (if any) would be unreachable —
                // their init can't be resolved.
                if (0..regions.len()).any(|k| !regions[k].has_parent && regions[k].head > i) {
                    return false;
                }
                break;
            }
            // Branches outside regions were rejected by the global discipline;
            // region closers/exits are inside regions (skipped above).
            op => sym_step(op, &mut st, &mut events),
        }
        i += 1;
    }
    true
}

/// Re-base every tracked slot offset by `delta` (SP moved down by `delta`).
fn shift_slots(st: &mut WalkState, delta: i64) {
    if delta == 0 {
        return;
    }
    st.written = st
        .written
        .iter()
        .map(|(&off, &v)| (off + delta, v))
        .collect();
    st.tainted = st.tainted.iter().map(|&off| off + delta).collect();
    // Symbolic Slot{off} identities in registers refer to pre-shift offsets —
    // drop them (registers holding loaded values stay valid as Const/Top, but a
    // Slot identity is offset-relative).
    for r in st.regs.iter_mut() {
        if matches!(r, Sym::Slot { .. } | Sym::Bool(_)) {
            *r = Sym::Top;
        }
    }
    st.flags = None;
}

// ---------------------------------------------------------------------------
// Trip-count arithmetic
// ---------------------------------------------------------------------------

/// Smallest `n ≥ 0` such that `(init + n·step + p.add) p.rel p.rhs` holds —
/// i.e. the head evaluation index at which the exit predicate first fires —
/// with STATIC no-overflow checks over the whole counter walk in the
/// predicate's signedness domain. Returns `(n, requires_hint)`; equality exits
/// set `requires_hint` (consumed only under a verified `--wcet-hints` entry).
/// (#778 phase 5) Trip count for an exit predicate that may carry a
/// DATA-DEPENDENT masked bound. For a normal const bound (`masked_ceiling ==
/// None`) this is exactly [`exit_index`]. For a masked bound `x & K ∈ [0, K]`
/// the real per-iteration bound is somewhere in `[0, K]` for ANY runtime input,
/// so the sound trip is the MAXIMUM over the whole bound domain:
///
/// - A single endpoint is UNSOUND. For a count-UP loop (`i < bound`) the worst
///   case is the LARGEST bound (`K`); for a count-DOWN loop (`i > bound`) the
///   worst case is the SMALLEST bound (`0`). Seeding only `rhs = K` would emit a
///   bound BELOW a real count-down execution — the fatal class.
/// - We evaluate `exit_index` at BOTH endpoints (`rhs = K` and `rhs = 0`),
///   require BOTH to terminate (else the loop is not guaranteed-terminating for
///   every masked value), and take the MAX trip. Because the trip is monotone in
///   the bound for a threshold relation, the max over the two endpoints bounds
///   the max over the whole `[0, K]` interval (and per-iteration-varying bounds,
///   each `m_j ≤ K`, are covered too: a count-up exits by `counter = K`, a
///   count-down's worst case is the `rhs = 0` endpoint).
/// - For an Eq/Ne exit, an interior bound value can be MISSED by a step that does
///   not divide the distance (the divisibility-divergence trap), so endpoint
///   reasoning holds only when EVERY value in `[0, K]` is reachable — i.e.
///   `|step| == 1`. A larger step with an Eq/Ne masked bound is declined.
///
/// The masked trip is ALWAYS hint-gated (the returned bool is forced true): a
/// bound resting on a data-dependent ceiling is opt-in, mirroring the
/// equality-exit gate. `None` propagates (unproven) whenever either endpoint
/// fails to terminate or wraps.
fn masked_exit_index(init: i32, step: i64, p: &Pred) -> Option<(u64, bool)> {
    let Some(ceiling) = p.masked_ceiling else {
        return exit_index(init, step, p);
    };
    debug_assert!(ceiling >= 0);
    // Eq/Ne masked bound: only |step| == 1 keeps every interior value reachable.
    if matches!(p.rel, Rel::Eq | Rel::Ne) && step.abs() != 1 {
        return None;
    }
    let at = |rhs: i32| -> Option<u64> {
        let pr = Pred {
            rhs,
            masked_ceiling: None,
            ..*p
        };
        exit_index(init, step, &pr).map(|(k, _)| k)
    };
    let (hi, lo) = (at(ceiling)?, at(0)?);
    // Force hint-gated: a data-dependent ceiling is only ever consumed under a
    // verified --wcet-hints entry.
    Some((hi.max(lo), true))
}

/// `None` = exit not statically guaranteed (or a possible wrap) → unproven.
pub(crate) fn exit_index(init: i32, step: i64, p: &Pred) -> Option<(u64, bool)> {
    let s = step;
    debug_assert!(s != 0);
    let signed = matches!(
        p.rel,
        Rel::LtS | Rel::LeS | Rel::GtS | Rel::GeS | Rel::Eq | Rel::Ne
    );
    // Counter values in the comparison domain.
    let (v0, lo, hi): (i128, i128, i128) = if signed {
        (init as i128, i32::MIN as i128, i32::MAX as i128)
    } else {
        (init as u32 as i128, 0, u32::MAX as i128)
    };
    let (rhs, add) = if signed {
        (p.rhs as i128, p.add as i128)
    } else {
        (p.rhs as u32 as i128, p.add as i128)
    };
    let s = s as i128;

    // Exit threshold as "counter value C where (C + add) rel rhs first holds
    // along the walk direction", normalized to v ≥ T (for s > 0) or v ≤ T
    // (for s < 0); equality handled separately.
    let k: i128 = match p.rel {
        Rel::Eq | Rel::Ne => {
            let target = rhs - add;
            if p.rel == Rel::Ne {
                // Exit when v ≠ target: fires at n=0 unless v0 == target, in
                // which case n=1 (one step moves off the target; no-wrap is
                // checked below).
                let n = if v0 == target { 1 } else { 0 };
                return finish(n, v0, s, add, lo, hi, false);
            }
            // Exit when v == target: reachable iff the walk lands exactly on it.
            let d = target - v0;
            if d % s != 0 || d / s < 0 {
                return None; // steps over or walks away — may never terminate
            }
            return finish(d / s, v0, s, add, lo, hi, true);
        }
        Rel::GeS | Rel::HsU => rhs - add,     // exit when v ≥ T
        Rel::GtS | Rel::HiU => rhs - add + 1, // exit when v > T-  ⇔ v ≥ T+1
        Rel::LeS | Rel::LsU => rhs - add,     // exit when v ≤ T
        Rel::LtS | Rel::LoU => rhs - add - 1, // exit when v < T  ⇔ v ≤ T-1
    };
    let upward_exit = matches!(p.rel, Rel::GeS | Rel::GtS | Rel::HsU | Rel::HiU);
    if upward_exit {
        if v0 >= k {
            return finish(0, v0, s, add, lo, hi, false);
        }
        if s <= 0 {
            return None; // walking away from the exit threshold
        }
        let n = ceil_div_pos(k - v0, s);
        finish(n, v0, s, add, lo, hi, false)
    } else {
        if v0 <= k {
            return finish(0, v0, s, add, lo, hi, false);
        }
        if s >= 0 {
            return None;
        }
        let n = ceil_div_pos(v0 - k, -s);
        finish(n, v0, s, add, lo, hi, false)
    }
}

/// `ceil(num / den)` for `num ≥ 0`, `den > 0` (i128 `div_ceil` is unstable).
fn ceil_div_pos(num: i128, den: i128) -> i128 {
    debug_assert!(num >= 0 && den > 0);
    (num + den - 1) / den
}

/// Final static checks for exit index `n`: every counter value touched on the
/// walk (`v0 .. v0+n·s`, monotone) and every compared value (`+add`) must stay
/// exactly representable in the comparison domain — otherwise the hardware
/// would wrap and the affine model would diverge from the machine.
fn finish(
    n: i128,
    v0: i128,
    s: i128,
    add: i128,
    lo: i128,
    hi: i128,
    requires_hint: bool,
) -> Option<(u64, bool)> {
    if n < 0 {
        return None;
    }
    let vn = v0.checked_add(n.checked_mul(s)?)?;
    for v in [v0, vn, v0 + add, vn + add] {
        if v < lo || v > hi {
            return None;
        }
    }
    Some((u64::try_from(n).ok()?, requires_hint))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn pred(rel: Rel, rhs: i32, add: i64) -> Pred {
        Pred {
            off: 0,
            add,
            rel,
            rhs,
            masked_ceiling: None,
        }
    }

    #[test]
    fn head_test_up_count() {
        // for v in 0..10 step 1, exit when v >= 10 → 10 full iterations.
        assert_eq!(exit_index(0, 1, &pred(Rel::GeS, 10, 0)), Some((10, false)));
        // init 3, step 2, exit when v >= 10 → v: 3,5,7,9,11 → n=4.
        assert_eq!(exit_index(3, 2, &pred(Rel::GeS, 10, 0)), Some((4, false)));
        // already at/above the bound → 0 iterations.
        assert_eq!(exit_index(10, 1, &pred(Rel::GeS, 10, 0)), Some((0, false)));
        // compared value is v+1 (bottom-test increment-then-compare shape).
        assert_eq!(exit_index(0, 1, &pred(Rel::GeS, 10, 1)), Some((9, false)));
    }

    #[test]
    fn down_count_and_unsigned() {
        // v from 10 down to 0, exit when v <= 0 → n = 10.
        assert_eq!(exit_index(10, -1, &pred(Rel::LeS, 0, 0)), Some((10, false)));
        // unsigned: exit when v >=u 8, from 0 step 1 → 8.
        assert_eq!(exit_index(0, 1, &pred(Rel::HsU, 8, 0)), Some((8, false)));
        // step walks AWAY from the exit → not guaranteed.
        assert_eq!(exit_index(0, -1, &pred(Rel::GeS, 10, 0)), None);
    }

    #[test]
    fn equality_exit_is_hint_gated() {
        // exact landing: 0,1,..,8 → n=8, requires_hint.
        assert_eq!(exit_index(0, 1, &pred(Rel::Eq, 8, 0)), Some((8, true)));
        // step 2 over an odd distance NEVER lands → None (may not terminate).
        assert_eq!(exit_index(0, 2, &pred(Rel::Eq, 9, 0)), None);
    }

    #[test]
    fn overflow_wraps_decline() {
        // init MAX−1, step 2, exit when v ≥ MAX: the walk goes MAX−1 → MAX+1,
        // i.e. the hardware would wrap past the threshold → None.
        assert_eq!(
            exit_index(i32::MAX - 1, 2, &pred(Rel::GeS, i32::MAX, 0)),
            None
        );
        // Same shape one step earlier lands exactly on MAX → proven, 1 trip.
        assert_eq!(
            exit_index(i32::MAX - 2, 1, &pred(Rel::GeS, i32::MAX, 0)),
            Some((2, false))
        );
    }
}
