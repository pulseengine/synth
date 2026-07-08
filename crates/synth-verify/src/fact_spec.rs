//! Proof-carrying specialization — VCR-PERF-002 / #494 **Phase 2**: the
//! single-elision prototype (value-range facts ⇒ dead conditional-branch
//! elision, the `gust_mix` clamp shape).
//!
//! Design source of truth: `docs/design/proof-carrying-specialization.md`
//! ("How synth consumes facts: the per-elision proof obligation"). loom is the
//! PROVER (its validator discharged the `wsc.facts` invariants upstream);
//! synth is a CONDITIONAL optimizer: it never re-derives a fact — it proves
//! the correctness of its OWN transformation *given* the fact, per elision
//! site, BEFORE emission, through the ordeal-backed [`BvSolver`]
//! (certificate-checked pure-Rust QF_BV; every `Unsat` verdict carries an
//! LRAT proof validated by the trusted `ordeal-lrat` checker before it is
//! reported).
//!
//! # The transformation
//!
//! Working on the decoded [`WasmOp`] stream (backend-agnostic — the rewritten
//! stream feeds whichever selector the driver picks), the pass walks the
//! function top-level with a symbolic state (stack + locals as QF_BV terms via
//! the existing [`WasmSemantics`] encoder) and, at every no-`else`
//! `if … end`, discharges the obligation
//!
//! ```text
//! premise    P   (every value-range fact reached so far, asserted as a hypothesis)
//! obligation UNSAT( P ∧ cond ≠ 0 )
//! ```
//!
//! `UNSAT(P ∧ cond ≠ 0)` implies the design doc's
//! `UNSAT(P ∧ general_lowering(x) ≠ specialized_lowering(x))`: a no-`else`
//! `if` whose condition is 0 on every P-admissible input never executes its
//! body, and wasm validation forces a no-`else` `if` blocktype to have
//! identical param/result types, so the not-taken path is the identity — the
//! general and specialized lowerings agree on every input P admits. The
//! stronger query is deliberately used because it is decided in the pure
//! QF_BV fragment with no control-flow encoding.
//!
//! - **UNSAT (certificate-checked)** → the elision is ADMITTED: the
//!   condition-producing op slice (proven pure and contiguous) plus the whole
//!   `if … end` region are deleted; the certificate line is logged per
//!   function (the evidence trail).
//! - **Sat / Unknown / conflict-budget exceeded / any shape outside the
//!   tracked fragment** → **DECLINE LOUDLY**: the general lowering is
//!   emitted. There is no silent wrong-code path; the conservative fallback
//!   is today's codegen.
//!
//! # Soundness of the symbolic tracking (over-approximation discipline)
//!
//! * Values produced by ops outside the tracked i32 fragment never enter the
//!   state: the walk STOPS at the first untracked op (no further elisions in
//!   the function; everything already admitted was justified independently).
//! * Locals are seeded as fresh unconstrained variables (a superset of both
//!   parameter values and the zero-init of non-param locals — sound).
//! * A DECLINED `if` region may or may not execute: every local it assigns
//!   (at any nesting depth) is havocked to a fresh variable, and its block
//!   results are pushed as fresh variables.
//! * An ADMITTED `if` region provably never executes, so state is unchanged.
//! * `div`/`rem` (i32 AND i64) are tracked since Phase 2b (#494
//!   divisor-nonzero), but NEVER deleted: they can trap, and a deleted
//!   condition slice must be effect-free under ALL inputs, not just
//!   P-admissible ones — so a div result always carries `start = None`
//!   (non-erasable) and its value is havocked to a fresh variable. What
//!   Phase 2b adds is per-site TRAP-GUARD elision marks consumed by the
//!   direct selector (see "The div/rem guard obligations" below).
//!
//! # The div/rem guard obligations (Phase 2b, #494 divisor-nonzero)
//!
//! A `div`/`rem` lowering carries up to TWO trap guards, and they fall to two
//! INDEPENDENT obligations — this is the #633/#634 two-guard distinction:
//!
//! ```text
//! divide-by-zero guard (div_u/div_s/rem_u/rem_s, i32+i64):
//!     UNSAT( P ∧ divisor == 0 )
//! INT_MIN/-1 overflow guard (div_s ONLY; rem_s(INT_MIN,-1)==0 never traps):
//!     UNSAT( P ∧ dividend == INT_MIN ∧ divisor == -1 )
//! ```
//!
//! A divisor-nonzero fact (kind 3) discharges the first but NOT the second —
//! `divisor ≠ 0` does not exclude `divisor == -1`, so the overflow guard is
//! RETAINED unless the premises independently prove the second obligation
//! (e.g. a value-range fact `divisor ∈ [1, N]` proves both). Each discharged
//! obligation becomes a per-site elision mark ([`FactSpecResult::elide_div_zero`]
//! / [`FactSpecResult::elide_div_ovf`], indices into the RETURNED stream);
//! the driver threads them to the direct selector, which omits exactly that
//! guard. Sat / Unknown / no-premise ⇒ loud decline, the guard is emitted.
//!
//! # Flag gating
//!
//! The driver only invokes this pass when `SYNTH_FACT_SPEC` is set (default
//! OFF) AND the module carried a parseable `wsc.facts` section. Frozen
//! fixtures carry no facts section, so every frozen anchor is bit-identical
//! trivially; with the flag off the pass does not run at all.

use crate::solver::{CheckOutcome, new_solver};
use crate::term::{BV, Bool};
use crate::wasm_semantics::WasmSemantics;
use std::collections::{HashMap, HashSet};
use synth_core::WasmOp;
use synth_core::wsc_facts::{FactKind, WscFact};

/// Outcome of specializing one function. `ops`/`block_arity`/`kept` are only
/// meaningful when [`changed`](Self::changed) — otherwise they echo the input.
#[derive(Debug)]
pub struct FactSpecResult {
    /// The (possibly rewritten) op stream.
    pub ops: Vec<WasmOp>,
    /// The blocktype-arity side-table matching `ops` (one entry per
    /// `Block`/`Loop`/`If` in op order — entries of deleted openers removed).
    pub block_arity: Vec<(u8, u8)>,
    /// Indices into the ORIGINAL op stream that were kept, in order. Lets the
    /// driver filter parallel side-tables (e.g. `op_offsets` for DWARF).
    pub kept: Vec<usize>,
    /// One certificate line per ADMITTED elision (logged per function).
    pub admitted: Vec<String>,
    /// One line per LOUD DECLINE (the general lowering is emitted for these).
    pub declined: Vec<String>,
    /// #494 phase 2b: indices (into the RETURNED `ops` stream) of div/rem
    /// ops whose divide-by-zero trap guard was certificate-elided
    /// (`UNSAT(P ∧ divisor == 0)` discharged per site).
    pub elide_div_zero: Vec<usize>,
    /// #494 phase 2b: indices (into the RETURNED `ops` stream) of `div_s`
    /// ops whose `INT_MIN / -1` overflow guard was certificate-elided — a
    /// SEPARATE obligation (`UNSAT(P ∧ dividend == INT_MIN ∧ divisor == -1)`);
    /// a divisor-nonzero fact alone never lands here (#633/#634).
    pub elide_div_ovf: Vec<usize>,
    /// True when `ops` differs from the input (at least one region deletion).
    stream_changed: bool,
}

impl FactSpecResult {
    /// True when the op STREAM was rewritten (region deletions). Guard-elision
    /// marks do not rewrite the stream — check
    /// [`elide_div_zero`](Self::elide_div_zero) /
    /// [`elide_div_ovf`](Self::elide_div_ovf) separately.
    pub fn changed(&self) -> bool {
        self.stream_changed
    }
}

/// A symbolic operand-stack slot.
#[derive(Clone)]
struct Val {
    bv: BV,
    /// Start of the contiguous, side-effect-free op range that produced this
    /// value — `None` when the producing slice is impure (`local.tee`) or not
    /// provably contiguous. Only a `Some` slice may be deleted.
    start: Option<usize>,
    /// Index of the op that (last) produced this value.
    created: usize,
}

/// Specialize one function's op stream against its `wsc.facts` premises.
///
/// `block_arity` is the decoder's ordinal side-table (one `(params, results)`
/// entry per `Block`/`Loop`/`If` in op order); `facts` is the per-function
/// slice (`CompileConfig::current_func_facts`); `params_i64` is the declared
/// param-width table (`CompileConfig::current_func_params_i64` — `true` ⇒
/// param `k` is 64-bit), which fixes the symbolic width of a param
/// `local.get` (Phase 2b tracks i64 divisors). Total: every input yields a
/// result — inapplicable shapes surface as loud declines, never errors.
pub fn specialize_function(
    func_name: &str,
    ops: &[WasmOp],
    block_arity: &[(u8, u8)],
    facts: &[WscFact],
    params_i64: &[bool],
) -> FactSpecResult {
    let mut pass = Pass::new(func_name, ops, block_arity, facts, params_i64);
    pass.walk();
    pass.finish()
}

/// #494 phase 2b RED-TEAM lever (debug builds ONLY): treat a Sat verdict on
/// the divide-by-zero guard obligation as an admit anyway. Exists so the
/// differential oracle can DEMONSTRATE the divergence an unsound admit would
/// cause (wasmtime traps at divisor == 0, the forced build does not) and then
/// show the Sat-decline restoring the guard byte-identically. Compiled out of
/// release builds; every forced admit screams in its certificate line.
#[cfg(debug_assertions)]
fn force_admit_unsound() -> bool {
    std::env::var("SYNTH_FACT_SPEC_FORCE_ADMIT").is_ok_and(|v| v != "0")
}

#[cfg(not(debug_assertions))]
fn force_admit_unsound() -> bool {
    false
}

struct Pass<'a> {
    func: &'a str,
    ops: &'a [WasmOp],
    block_arity: &'a [(u8, u8)],
    /// op index → ordinal into `block_arity` (for `Block`/`Loop`/`If` ops).
    opener_ordinal: HashMap<usize, usize>,
    /// op index → signed range fact attached to that op's result (raw s64
    /// bounds; clamped to the value's width at attach time).
    range_facts: HashMap<usize, (i64, i64)>,
    /// op indices carrying a divisor-nonzero fact (kind 3): `value ≠ 0`.
    nonzero_facts: HashSet<usize>,
    /// Declared param widths (`true` ⇒ 64-bit) — fixes `local.get` widths.
    params_i64: &'a [bool],
    sem: WasmSemantics,
    stack: Vec<Val>,
    locals: HashMap<u32, BV>,
    /// Every fresh variable created (name order), for Sat counterexamples.
    vars: Vec<BV>,
    fresh: u32,
    premises: Vec<Bool>,
    premise_desc: Vec<String>,
    /// Inclusive op-index ranges to delete (disjoint, ascending).
    deletions: Vec<(usize, usize)>,
    admitted: Vec<String>,
    declined: Vec<String>,
    /// #494 phase 2b: ORIGINAL op indices marked for zero-guard elision.
    zero_marks: Vec<usize>,
    /// #494 phase 2b: ORIGINAL op indices marked for overflow-guard elision.
    ovf_marks: Vec<usize>,
}

impl<'a> Pass<'a> {
    fn new(
        func: &'a str,
        ops: &'a [WasmOp],
        block_arity: &'a [(u8, u8)],
        facts: &'a [WscFact],
        params_i64: &'a [bool],
    ) -> Self {
        let mut opener_ordinal = HashMap::new();
        let mut ord = 0usize;
        for (i, op) in ops.iter().enumerate() {
            if matches!(op, WasmOp::Block | WasmOp::Loop | WasmOp::If) {
                opener_ordinal.insert(i, ord);
                ord += 1;
            }
        }
        let mut range_facts = HashMap::new();
        let mut nonzero_facts = HashSet::new();
        for f in facts {
            // Out-of-range value_id is vacuous (encoding doc's rule).
            if (f.value_id as usize) >= ops.len() {
                continue;
            }
            match f.kind {
                FactKind::ValueRange { lo, hi } => {
                    // Raw s64 bounds; clamped to the value's width when the
                    // walk attaches the premise. An inverted bound is vacuous.
                    if lo <= hi {
                        range_facts.insert(f.value_id as usize, (lo, hi));
                    }
                }
                // #494 phase 2b: divisor-nonzero (kind 3) — `value ≠ 0`.
                FactKind::DivisorNonZero => {
                    nonzero_facts.insert(f.value_id as usize);
                }
                _ => {}
            }
        }
        Self {
            func,
            ops,
            block_arity,
            opener_ordinal,
            range_facts,
            nonzero_facts,
            params_i64,
            // No memory model needed: memory ops are outside the tracked
            // fragment (the walk stops there).
            sem: WasmSemantics::new_with_memory(Vec::new()),
            stack: Vec::new(),
            locals: HashMap::new(),
            vars: Vec::new(),
            fresh: 0,
            premises: Vec::new(),
            premise_desc: Vec::new(),
            deletions: Vec::new(),
            admitted: Vec::new(),
            declined: Vec::new(),
            zero_marks: Vec::new(),
            ovf_marks: Vec::new(),
        }
    }

    fn fresh_var(&mut self, name: String) -> BV {
        let v = BV::new_const(name, 32);
        self.vars.push(v.clone());
        v
    }

    fn local_bv(&mut self, idx: u32) -> BV {
        if let Some(bv) = self.locals.get(&idx) {
            return bv.clone();
        }
        // A not-yet-seen local's width comes from the declared param table
        // (#494 phase 2b tracks i64 divisors); non-param locals default to
        // 32 bits — an i64 op reading one fails the width check and declines.
        let width = if self.params_i64.get(idx as usize).copied().unwrap_or(false) {
            64
        } else {
            32
        };
        let v = BV::new_const(format!("fs_l{idx}"), width);
        self.vars.push(v.clone());
        self.locals.insert(idx, v.clone());
        v
    }

    /// Attach the premises of every fact naming op `i`'s result, at the
    /// value's own width.
    fn attach_fact(&mut self, i: usize, bv: &BV) {
        let width = bv.get_size();
        if let Some(&(lo, hi)) = self.range_facts.get(&i) {
            // Clamp the s64 bound to the value's width (the phase-2 rule for
            // 32-bit values; 64-bit values take the bound verbatim). A bound
            // that inverts after clamping is impossible for a genuine value
            // of this width — fact validity is loom's obligation (trust
            // split), so we keep the phase-2 clamp semantics unchanged.
            let (lo, hi) = if width == 32 {
                (
                    lo.clamp(i64::from(i32::MIN), i64::from(i32::MAX)),
                    hi.clamp(i64::from(i32::MIN), i64::from(i32::MAX)),
                )
            } else {
                (lo, hi)
            };
            let lo_bv = BV::from_i64(lo, width);
            let hi_bv = BV::from_i64(hi, width);
            let p = Bool::and(&[&bv.bvsge(&lo_bv), &bv.bvsle(&hi_bv)]);
            self.premises.push(p);
            self.premise_desc
                .push(format!("value(op#{i}) ∈ [{lo}, {hi}] (signed, i{width})"));
        }
        if self.nonzero_facts.contains(&i) {
            // #494 phase 2b: divisor-nonzero (kind 3).
            let p = bv.ne(BV::from_i64(0, width));
            self.premises.push(p);
            self.premise_desc
                .push(format!("value(op#{i}) ≠ 0 (i{width})"));
        }
    }

    fn push(&mut self, bv: BV, start: Option<usize>, created: usize) {
        self.stack.push(Val { bv, start, created });
    }

    /// Find the matching `End` for the opener at `i`; also reports whether a
    /// top-level `Else` occurs. `None` = malformed nesting (stop the walk).
    fn matching_end(&self, i: usize) -> Option<(usize, bool)> {
        let mut depth = 0usize;
        let mut has_else = false;
        for (j, op) in self.ops.iter().enumerate().skip(i + 1) {
            match op {
                WasmOp::Block | WasmOp::Loop | WasmOp::If => depth += 1,
                WasmOp::Else if depth == 0 => has_else = true,
                WasmOp::End => {
                    if depth == 0 {
                        return Some((j, has_else));
                    }
                    depth -= 1;
                }
                _ => {}
            }
        }
        None
    }

    /// Continuation after a DECLINED `if` region `[i..=end]`: the body may or
    /// may not run, so havoc every local it assigns (any depth) and model its
    /// block results as fresh variables.
    fn havoc_region(&mut self, i: usize, end: usize, arity: (u8, u8)) {
        let ops = self.ops;
        for op in &ops[i + 1..end] {
            if let WasmOp::LocalSet(idx) | WasmOp::LocalTee(idx) = op {
                let n = self.fresh;
                self.fresh += 1;
                let v = self.fresh_var(format!("fs_h{n}"));
                self.locals.insert(*idx, v);
            }
        }
        for _ in 0..arity.0 {
            self.stack.pop();
        }
        for k in 0..arity.1 {
            let n = self.fresh;
            self.fresh += 1;
            let v = self.fresh_var(format!("fs_r{n}_{k}"));
            self.push(v, None, end);
        }
    }

    fn decline(&mut self, msg: String) {
        self.declined
            .push(format!("{}: {} — general lowering emitted", self.func, msg));
    }

    /// #494 phase 2b: discharge the per-site div/rem trap-guard obligations
    /// for the op at `i` (`op_name`, operand width `width`, dividend `a`,
    /// divisor `b`), recording elision marks for the lowering. TWO independent
    /// obligations (the #633/#634 two-guard distinction):
    ///
    /// - zero guard (every div/rem): `UNSAT(P ∧ divisor == 0)`;
    /// - overflow guard (`div_s` only): `UNSAT(P ∧ dividend == INT_MIN ∧
    ///   divisor == -1)` — divisor-nonzero alone NEVER discharges this.
    ///
    /// Sat / Unknown / no-premise ⇒ loud decline; the guard is emitted.
    fn try_elide_div_guards(&mut self, i: usize, op_name: &str, is_div_s: bool, a: &Val, b: &Val) {
        let width = b.bv.get_size();
        if self.premises.is_empty() {
            self.decline(format!(
                "op#{i} {op_name} — no premise reaches this site; both trap guards retained"
            ));
            return;
        }
        // Obligation 1: the divide-by-zero guard.
        let mut solver = new_solver();
        for p in &self.premises {
            solver.assert(p);
        }
        solver.assert(&b.bv.eq(BV::from_i64(0, width)));
        match solver.check() {
            CheckOutcome::Unsat => {
                self.zero_marks.push(i);
                self.admitted.push(format!(
                    "{}: op#{i} {op_name} — divide-by-zero guard elided:                      UNSAT(P ∧ divisor == 0) via {} (certificate-checked QF_BV;                      every Unsat carries an LRAT proof validated by ordeal-lrat);                      P = {{{}}}; divisor = {}",
                    self.func,
                    solver.name(),
                    self.premise_desc.join(" ∧ "),
                    b.bv,
                ));
            }
            CheckOutcome::Sat => {
                let cex = self.counterexample(solver.as_ref());
                if force_admit_unsound() {
                    // RED-TEAM lever (debug builds only): admit the Sat site
                    // anyway so the differential oracle can demonstrate the
                    // divergence. Screams, and still logs the model.
                    self.zero_marks.push(i);
                    self.admitted.push(format!(
                        "{}: op#{i} {op_name} — divide-by-zero guard elided by                          UNSOUND FORCED ADMIT (SYNTH_FACT_SPEC_FORCE_ADMIT,                          red-team oracle lever, debug builds only) — obligation                          was Sat (counterexample: {cex}); NEVER use in production",
                        self.func,
                    ));
                } else {
                    self.decline(format!(
                        "op#{i} {op_name} — zero-guard obligation Sat (divisor can                          be 0 under P; counterexample: {cex}); guard retained"
                    ));
                }
            }
            CheckOutcome::Unknown(reason) => {
                self.decline(format!(
                    "op#{i} {op_name} — zero-guard obligation Unknown ({reason});                      conservative decline, guard retained"
                ));
            }
        }
        // Obligation 2: the INT_MIN/-1 overflow guard — div_s only, and a
        // SEPARATE proof (#633/#634): divisor ≠ 0 does not exclude -1.
        if !is_div_s {
            return;
        }
        let int_min = if width == 64 {
            i64::MIN
        } else {
            i64::from(i32::MIN)
        };
        let mut solver = new_solver();
        for p in &self.premises {
            solver.assert(p);
        }
        solver.assert(&a.bv.eq(BV::from_i64(int_min, width)));
        solver.assert(&b.bv.eq(BV::from_i64(-1, width)));
        match solver.check() {
            CheckOutcome::Unsat => {
                self.ovf_marks.push(i);
                self.admitted.push(format!(
                    "{}: op#{i} {op_name} — INT{width}_MIN/-1 overflow guard elided:                      UNSAT(P ∧ dividend == INT{width}_MIN ∧ divisor == -1) via {}                      (certificate-checked QF_BV; every Unsat carries an LRAT proof                      validated by ordeal-lrat); P = {{{}}}",
                    self.func,
                    solver.name(),
                    self.premise_desc.join(" ∧ "),
                ));
            }
            CheckOutcome::Sat => {
                let cex = self.counterexample(solver.as_ref());
                self.decline(format!(
                    "op#{i} {op_name} — overflow-guard obligation Sat (dividend ==                      INT{width}_MIN with divisor == -1 is possible under P;                      counterexample: {cex}); the #633 overflow guard is RETAINED —                      a divisor-nonzero premise alone never elides it"
                ));
            }
            CheckOutcome::Unknown(reason) => {
                self.decline(format!(
                    "op#{i} {op_name} — overflow-guard obligation Unknown ({reason});                      conservative decline, the #633 overflow guard is RETAINED"
                ));
            }
        }
    }

    /// Read the model back for an actionable counterexample string.
    fn counterexample(&self, solver: &dyn crate::solver::BvSolver) -> String {
        let cex: Vec<String> = self
            .vars
            .iter()
            .filter_map(|v| {
                let name = format!("{v}");
                solver.value(v).map(|x| {
                    if v.get_size() == 64 {
                        format!("{name}={}", x as u64 as i64)
                    } else {
                        format!("{name}={}", x as u32 as i32)
                    }
                })
            })
            .collect();
        if cex.is_empty() {
            "<no model>".to_string()
        } else {
            cex.join(", ")
        }
    }

    /// Discharge the per-elision obligation for the no-`else` `if` at `i`
    /// (matching `End` at `end`, condition `cond`). Returns true iff admitted.
    fn try_elide(&mut self, i: usize, end: usize, cond: &Val) -> bool {
        if self.premises.is_empty() {
            self.decline(format!(
                "op#{i} `if` — no premise reaches this site (no usable value-range fact)"
            ));
            return false;
        }
        let mut solver = new_solver();
        for p in &self.premises {
            solver.assert(p);
        }
        let taken = cond.bv.ne(BV::from_i64(0, 32));
        solver.assert(&taken);
        match solver.check() {
            CheckOutcome::Unsat => {
                let Some(start) = cond.start else {
                    // Proven dead, but the condition slice has a side effect
                    // (`local.tee`) or is not provably contiguous — deleting
                    // it could drop live work. Conservative: keep everything.
                    self.decline(format!(
                        "op#{i} `if` proven dead (UNSAT) but its condition slice is not \
                         erasable (impure or non-contiguous producer)"
                    ));
                    return false;
                };
                self.deletions.push((start, end));
                self.admitted.push(format!(
                    "{}: op#{i} `if` (+condition slice) — ops [{start}..={end}] elided \
                     ({} ops): UNSAT(P ∧ cond ≠ 0) via {} (certificate-checked QF_BV; \
                     every Unsat carries an LRAT proof validated by ordeal-lrat); \
                     P = {{{}}}; cond = {}",
                    self.func,
                    end - start + 1,
                    solver.name(),
                    self.premise_desc.join(" ∧ "),
                    cond.bv,
                ));
                true
            }
            CheckOutcome::Sat => {
                // Read the model back for an actionable counterexample.
                let cex: Vec<String> = self
                    .vars
                    .iter()
                    .filter_map(|v| {
                        let name = format!("{v}");
                        solver
                            .value(v)
                            .map(|x| format!("{name}={}", x as u32 as i32))
                    })
                    .collect();
                self.decline(format!(
                    "op#{i} `if` — obligation Sat (branch reachable under P; \
                     counterexample: {})",
                    if cex.is_empty() {
                        "<no model>".to_string()
                    } else {
                        cex.join(", ")
                    }
                ));
                false
            }
            CheckOutcome::Unknown(reason) => {
                self.decline(format!(
                    "op#{i} `if` — obligation Unknown ({reason}); conservative decline"
                ));
                false
            }
        }
    }

    fn walk(&mut self) {
        if self.range_facts.is_empty() && self.nonzero_facts.is_empty() {
            self.decline(
                "no usable value-range or divisor-nonzero fact targets this function".to_string(),
            );
            return;
        }
        let ops = self.ops;
        let mut i = 0usize;
        while i < ops.len() {
            let op = &ops[i];
            match op {
                WasmOp::Nop => {}
                WasmOp::I32Const(v) => {
                    let bv = self.sem.encode_op(&WasmOp::I32Const(*v), &[]);
                    self.attach_fact(i, &bv);
                    self.push(bv, Some(i), i);
                }
                // #494 phase 2b: tracked so an i64 divisor term can be built
                // (the i64 fragment is const/local/div-rem only — anything
                // else stops the walk as before).
                WasmOp::I64Const(v) => {
                    let bv = self.sem.encode_op(&WasmOp::I64Const(*v), &[]);
                    self.attach_fact(i, &bv);
                    self.push(bv, Some(i), i);
                }
                WasmOp::LocalGet(idx) => {
                    let bv = self.local_bv(*idx);
                    self.attach_fact(i, &bv);
                    self.push(bv, Some(i), i);
                }
                WasmOp::LocalSet(idx) => {
                    let Some(v) = self.stack.pop() else {
                        self.decline(format!("op#{i} local.set on empty symbolic stack"));
                        return;
                    };
                    self.locals.insert(*idx, v.bv);
                }
                WasmOp::LocalTee(idx) => {
                    let Some(top) = self.stack.last_mut() else {
                        self.decline(format!("op#{i} local.tee on empty symbolic stack"));
                        return;
                    };
                    // The tee is a side effect: its slice must never be
                    // deleted as a "pure condition producer".
                    top.start = None;
                    top.created = i;
                    let bv = top.bv.clone();
                    self.locals.insert(*idx, bv.clone());
                    self.attach_fact(i, &bv);
                }
                WasmOp::Drop => {
                    if self.stack.pop().is_none() {
                        self.decline(format!("op#{i} drop on empty symbolic stack"));
                        return;
                    }
                }
                WasmOp::I32Eqz => {
                    let Some(a) = self.stack.pop() else {
                        self.decline(format!("op#{i} unary op on empty symbolic stack"));
                        return;
                    };
                    if a.bv.get_size() != 32 {
                        self.decline(format!("op#{i} i32.eqz on a non-32-bit operand"));
                        return;
                    }
                    let bv = self.sem.encode_op(op, &[a.bv]);
                    self.attach_fact(i, &bv);
                    let start = a.start.filter(|_| a.created + 1 == i);
                    self.push(bv, start, i);
                }
                // Tracked, trap-free i32 binops (div/rem excluded on purpose:
                // they can trap, and a deleted slice must be effect-free).
                WasmOp::I32Add
                | WasmOp::I32Sub
                | WasmOp::I32Mul
                | WasmOp::I32And
                | WasmOp::I32Or
                | WasmOp::I32Xor
                | WasmOp::I32Shl
                | WasmOp::I32ShrS
                | WasmOp::I32ShrU
                | WasmOp::I32Rotl
                | WasmOp::I32Rotr
                | WasmOp::I32Eq
                | WasmOp::I32Ne
                | WasmOp::I32LtS
                | WasmOp::I32LtU
                | WasmOp::I32LeS
                | WasmOp::I32LeU
                | WasmOp::I32GtS
                | WasmOp::I32GtU
                | WasmOp::I32GeS
                | WasmOp::I32GeU => {
                    let (Some(b), Some(a)) = (self.stack.pop(), self.stack.pop()) else {
                        self.decline(format!("op#{i} binop on underflowing symbolic stack"));
                        return;
                    };
                    if a.bv.get_size() != 32 || b.bv.get_size() != 32 {
                        self.decline(format!("op#{i} i32 binop on a non-32-bit operand"));
                        return;
                    }
                    let bv = self.sem.encode_op(op, &[a.bv, b.bv]);
                    self.attach_fact(i, &bv);
                    // Contiguity proof for the combined producer slice:
                    // a's slice, immediately followed by b's, immediately
                    // followed by this op. Anything else ⇒ not erasable.
                    let start = match (a.start, b.start) {
                        (Some(sa), Some(sb)) if a.created + 1 == sb && b.created + 1 == i => {
                            Some(sa)
                        }
                        _ => None,
                    };
                    self.push(bv, start, i);
                }
                // #494 phase 2b: i32/i64 div/rem — TRACKED (upgrading the
                // phase-2 hard stop), never DELETED. The op can trap, so its
                // result carries `start = None` (it can never sit inside an
                // erasable condition slice); the walk instead discharges the
                // per-site guard obligations (see the module docs' two-guard
                // distinction) and marks the op for the lowering. Downstream
                // soundness: if the op traps, nothing after it executes (any
                // later admitted elision is vacuous on that path); if it does
                // not, its result is havocked to a fresh variable.
                WasmOp::I32DivU
                | WasmOp::I32DivS
                | WasmOp::I32RemU
                | WasmOp::I32RemS
                | WasmOp::I64DivU
                | WasmOp::I64DivS
                | WasmOp::I64RemU
                | WasmOp::I64RemS => {
                    let (Some(b), Some(a)) = (self.stack.pop(), self.stack.pop()) else {
                        self.decline(format!("op#{i} div/rem on underflowing symbolic stack"));
                        return;
                    };
                    let (op_name, expect, is_div_s) = match op {
                        WasmOp::I32DivU => ("i32.div_u", 32, false),
                        WasmOp::I32DivS => ("i32.div_s", 32, true),
                        WasmOp::I32RemU => ("i32.rem_u", 32, false),
                        WasmOp::I32RemS => ("i32.rem_s", 32, false),
                        WasmOp::I64DivU => ("i64.div_u", 64, false),
                        WasmOp::I64DivS => ("i64.div_s", 64, true),
                        WasmOp::I64RemU => ("i64.rem_u", 64, false),
                        _ => ("i64.rem_s", 64, false),
                    };
                    if a.bv.get_size() != expect || b.bv.get_size() != expect {
                        self.decline(format!(
                            "op#{i} {op_name} on operands of unexpected width                              (symbolic widths {}/{}, expected {expect})",
                            a.bv.get_size(),
                            b.bv.get_size()
                        ));
                        return;
                    }
                    self.try_elide_div_guards(i, op_name, is_div_s, &a, &b);
                    // Havoc the result; `start = None` keeps a possibly-
                    // trapping op out of every erasable condition slice.
                    let n = self.fresh;
                    self.fresh += 1;
                    let v = self.fresh_var(format!("fs_d{n}"));
                    self.attach_fact(i, &v);
                    self.push(v, None, i);
                }
                WasmOp::If => {
                    let Some(cond) = self.stack.pop() else {
                        self.decline(format!("op#{i} `if` on empty symbolic stack"));
                        return;
                    };
                    if cond.bv.get_size() != 32 {
                        self.decline(format!("op#{i} `if` condition is not 32-bit"));
                        return;
                    }
                    let Some((end, has_else)) = self.matching_end(i) else {
                        self.decline(format!("op#{i} `if` without matching `end`"));
                        return;
                    };
                    let Some(&ord) = self.opener_ordinal.get(&i) else {
                        self.decline(format!("op#{i} `if` missing from the opener ordinal map"));
                        return;
                    };
                    let Some(&arity) = self.block_arity.get(ord) else {
                        self.decline(format!(
                            "op#{i} `if` has no block_arity entry (side-table desync)"
                        ));
                        return;
                    };
                    if has_else {
                        self.decline(format!(
                            "op#{i} `if`/`else` — only no-else `if` is in Phase-2 scope"
                        ));
                        self.havoc_region(i, end, arity);
                    } else if self.try_elide(i, end, &cond) {
                        // Region provably never executes: state unchanged
                        // (params-as-results pass-through is the identity for
                        // a no-else `if`, whose blocktype has equal
                        // param/result types by wasm validation).
                    } else {
                        self.havoc_region(i, end, arity);
                    }
                    i = end + 1;
                    continue;
                }
                // Function-final `End` (top-level): done.
                WasmOp::End => break,
                WasmOp::Return => break,
                other => {
                    // First op outside the tracked fragment: stop. Everything
                    // already admitted was justified independently of what
                    // follows; declining the REST loudly keeps honesty.
                    self.decline(format!(
                        "op#{i} {other:?} is outside the tracked i32 fragment — \
                         fact tracking stops here (no further elisions in this function)"
                    ));
                    return;
                }
            }
            i += 1;
        }
    }

    fn finish(self) -> FactSpecResult {
        let Pass {
            ops,
            block_arity,
            deletions,
            admitted,
            declined,
            zero_marks,
            ovf_marks,
            ..
        } = self;
        if deletions.is_empty() {
            return FactSpecResult {
                ops: ops.to_vec(),
                block_arity: block_arity.to_vec(),
                kept: (0..ops.len()).collect(),
                admitted,
                declined,
                // No rewrite ⇒ original indices ARE the output indices.
                elide_div_zero: zero_marks,
                elide_div_ovf: ovf_marks,
                stream_changed: false,
            };
        }
        let deleted = |i: usize| deletions.iter().any(|&(s, e)| i >= s && i <= e);
        let mut out_ops = Vec::with_capacity(ops.len());
        let mut out_arity = Vec::with_capacity(block_arity.len());
        let mut kept = Vec::with_capacity(ops.len());
        let mut ord = 0usize;
        for (i, op) in ops.iter().enumerate() {
            let is_opener = matches!(op, WasmOp::Block | WasmOp::Loop | WasmOp::If);
            if !deleted(i) {
                out_ops.push(op.clone());
                kept.push(i);
                if is_opener && let Some(&a) = block_arity.get(ord) {
                    out_arity.push(a);
                }
            }
            if is_opener {
                ord += 1;
            }
        }
        // Remap the guard-elision marks into the REWRITTEN index space. A
        // marked div/rem can never sit inside a deleted range (deleted ranges
        // are contiguous PURE condition slices plus proven-dead `if` regions
        // the walk skipped over; a div result's `start = None` bars it from
        // any erasable slice) — the filter below is defense in depth.
        let remap = |marks: Vec<usize>| -> Vec<usize> {
            marks
                .into_iter()
                .filter_map(|m| {
                    debug_assert!(!deleted(m), "guard mark op#{m} inside a deleted range");
                    kept.binary_search(&m).ok()
                })
                .collect()
        };
        FactSpecResult {
            ops: out_ops,
            block_arity: out_arity,
            elide_div_zero: remap(zero_marks),
            elide_div_ovf: remap(ovf_marks),
            kept,
            admitted,
            declined,
            stream_changed: true,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use WasmOp::*;

    fn fact(value_id: u32, lo: i64, hi: i64) -> WscFact {
        WscFact {
            func_index: 0,
            value_id,
            kind: FactKind::ValueRange { lo, hi },
        }
    }

    /// The gust_mix clamp shape: clamp(ch + 476, 1000, 2000) via two
    /// no-else `if`s over a local.
    fn clamp_ops() -> Vec<WasmOp> {
        vec![
            LocalGet(0),    // 0   ch          ← fact target
            I32Const(476),  // 1
            I32Add,         // 2   v = ch+476
            LocalSet(1),    // 3
            LocalGet(1),    // 4
            I32Const(1000), // 5
            I32LtS,         // 6
            If,             // 7
            I32Const(1000), // 8
            LocalSet(1),    // 9
            End,            // 10
            LocalGet(1),    // 11
            I32Const(2000), // 12
            I32GtS,         // 13
            If,             // 14
            I32Const(2000), // 15
            LocalSet(1),    // 16
            End,            // 17
            LocalGet(1),    // 18
            End,            // 19
        ]
    }

    const CLAMP_ARITY: &[(u8, u8)] = &[(0, 0), (0, 0)];

    #[test]
    fn clamp_shape_elides_both_branches_under_the_proven_bound_494() {
        let ops = clamp_ops();
        let r = specialize_function("gust_mix", &ops, CLAMP_ARITY, &[fact(0, 524, 1524)], &[]);
        assert_eq!(r.admitted.len(), 2, "declines: {:?}", r.declined);
        assert!(r.changed());
        assert_eq!(
            r.ops,
            vec![
                LocalGet(0),
                I32Const(476),
                I32Add,
                LocalSet(1),
                LocalGet(1),
                End
            ],
            "both clamp comparisons + branches + bodies must be gone"
        );
        assert_eq!(r.block_arity, vec![], "both If arity entries removed");
        assert_eq!(r.kept, vec![0, 1, 2, 3, 18, 19]);
        // The certificate evidence trail names the engine and the premise.
        for line in &r.admitted {
            assert!(line.contains("UNSAT"), "{line}");
            assert!(line.contains("certificate-checked"), "{line}");
            assert!(line.contains("[524, 1524]"), "{line}");
        }
    }

    #[test]
    fn wrong_wide_bound_is_sat_and_declines_loudly_494() {
        // ch ∈ [0, 4000] does NOT make the clamp dead (ch=0 → v=476 < 1000):
        // the obligation is Sat and BOTH sites decline with a counterexample.
        let ops = clamp_ops();
        let r = specialize_function("gust_mix", &ops, CLAMP_ARITY, &[fact(0, 0, 4000)], &[]);
        assert_eq!(r.admitted.len(), 0);
        assert!(!r.changed());
        assert_eq!(r.ops, ops, "declined ⇒ byte-identical op stream");
        assert_eq!(r.block_arity, CLAMP_ARITY.to_vec());
        assert!(
            r.declined
                .iter()
                .any(|d| d.contains("Sat") && d.contains("counterexample")),
            "declines must be loud and carry a model: {:?}",
            r.declined
        );
    }

    #[test]
    fn partially_dead_bound_elides_only_the_proven_branch_494() {
        // ch ∈ [524, 4000]: v ≥ 1000 so the LOW clamp is dead, but v can
        // exceed 2000 so the HIGH clamp must survive.
        let ops = clamp_ops();
        let r = specialize_function("gust_mix", &ops, CLAMP_ARITY, &[fact(0, 524, 4000)], &[]);
        assert_eq!(r.admitted.len(), 1, "declines: {:?}", r.declined);
        assert_eq!(r.declined.len(), 1);
        assert_eq!(
            r.ops,
            vec![
                LocalGet(0),
                I32Const(476),
                I32Add,
                LocalSet(1),
                LocalGet(1),
                I32Const(2000),
                I32GtS,
                If,
                I32Const(2000),
                LocalSet(1),
                End,
                LocalGet(1),
                End,
            ]
        );
        assert_eq!(r.block_arity, vec![(0, 0)], "one If survives");
    }

    #[test]
    fn no_facts_changes_nothing_494() {
        let ops = clamp_ops();
        let r = specialize_function("gust_mix", &ops, CLAMP_ARITY, &[], &[]);
        assert!(!r.changed());
        assert_eq!(r.ops, ops);
        assert!(!r.declined.is_empty(), "the no-fact case is a loud decline");
    }

    #[test]
    fn declined_if_havocs_its_locals_no_false_admit_downstream_494() {
        // The FIRST if is undecidable (condition on an unconstrained local),
        // and its body rewrites local 1 — so the SECOND if (which would be
        // dead under the fact alone) must NOT be admitted: local 1 is
        // havocked by the declined region.
        let ops = vec![
            LocalGet(0),    // 0  ← fact ch ∈ [524, 1524]
            I32Const(476),  // 1
            I32Add,         // 2
            LocalSet(1),    // 3
            LocalGet(2),    // 4  unconstrained
            If,             // 5
            I32Const(-9),   // 6
            LocalSet(1),    // 7  havocs local 1
            End,            // 8
            LocalGet(1),    // 9
            I32Const(2000), // 10
            I32GtS,         // 11
            If,             // 12
            I32Const(2000), // 13
            LocalSet(1),    // 14
            End,            // 15
            LocalGet(1),    // 16
            End,            // 17
        ];
        let r = specialize_function("f", &ops, CLAMP_ARITY, &[fact(0, 524, 1524)], &[]);
        assert_eq!(
            r.admitted.len(),
            0,
            "havocked local must block the downstream elision: {:?}",
            r.admitted
        );
        assert_eq!(r.ops, ops);
    }

    #[test]
    fn if_with_else_declines_494() {
        let ops = vec![
            LocalGet(0), // 0 ← fact forces cond = 0
            If,          // 1
            I32Const(1), // 2
            LocalSet(1), // 3
            Else,        // 4
            I32Const(2), // 5
            LocalSet(1), // 6
            End,         // 7
            LocalGet(1), // 8
            End,         // 9
        ];
        let r = specialize_function("f", &ops, &[(0, 0)], &[fact(0, 0, 0)], &[]);
        assert_eq!(r.admitted.len(), 0);
        assert!(
            r.declined.iter().any(|d| d.contains("else")),
            "{:?}",
            r.declined
        );
        assert_eq!(r.ops, ops);
    }

    #[test]
    fn nested_opener_inside_elided_body_fixes_block_arity_ordinals_494() {
        // A dead outer if contains a nested if: BOTH arity entries vanish and
        // the SURVIVING later block keeps its (translated) entry.
        let ops = vec![
            LocalGet(0), // 0 ← fact [5,5] ⇒ eqz = 0
            I32Eqz,      // 1
            If,          // 2   (ordinal 0)
            LocalGet(0), // 3
            If,          // 4   (ordinal 1, nested)
            I32Const(7), // 5
            LocalSet(1), // 6
            End,         // 7
            End,         // 8
            Block,       // 9   (ordinal 2, survives)
            End,         // 10
            End,         // 11
        ];
        let arity = &[(0, 0), (0, 0), (0, 1)];
        let r = specialize_function("f", &ops, arity, &[fact(0, 5, 5)], &[]);
        assert_eq!(r.admitted.len(), 1, "declines: {:?}", r.declined);
        // The condition slice starts at op 0 (LocalGet feeds the eqz), so the
        // whole deleted range is [0..=8]; only the trailing block survives.
        assert_eq!(r.ops, vec![Block, End, End]);
        assert_eq!(r.kept, vec![9, 10, 11]);
        assert_eq!(
            r.block_arity,
            vec![(0, 1)],
            "only the surviving Block's entry"
        );
    }

    #[test]
    fn tee_condition_slice_is_not_erasable_494() {
        // cond built through local.tee: proven dead, but deleting the slice
        // would lose the local write ⇒ decline (loud), stream unchanged.
        let ops = vec![
            LocalGet(0), // 0 ← fact [1,1]
            LocalTee(1), // 1  side effect in the slice
            I32Eqz,      // 2  = 0 under the fact
            If,          // 3
            I32Const(9), // 4
            LocalSet(2), // 5
            End,         // 6
            End,         // 7
        ];
        let r = specialize_function("f", &ops, &[(0, 0)], &[fact(0, 1, 1)], &[]);
        assert_eq!(r.admitted.len(), 0);
        assert!(
            r.declined
                .iter()
                .any(|d| d.contains("not") && d.contains("erasable")),
            "{:?}",
            r.declined
        );
        assert_eq!(r.ops, ops);
    }

    #[test]
    fn untracked_op_stops_tracking_loudly_494() {
        let ops = vec![
            LocalGet(0),   // 0 ← fact
            I64ExtendI32S, // 1  untracked ⇒ stop
            Drop,          // 2
            End,           // 3
        ];
        let r = specialize_function("f", &ops, &[], &[fact(0, 1, 2)], &[]);
        assert!(!r.changed());
        assert!(
            r.declined.iter().any(|d| d.contains("outside the tracked")),
            "{:?}",
            r.declined
        );
    }

    fn nonzero_fact(value_id: u32) -> WscFact {
        WscFact {
            func_index: 0,
            value_id,
            kind: FactKind::DivisorNonZero,
        }
    }

    // ================= #494 phase 2b: div/rem trap-guard elision =================

    #[test]
    fn divisor_range_excluding_zero_elides_zero_guard_all_rem_div_494() {
        // div_u, rem_u, rem_s by a param divisor proven ∈ [1, 100]: every
        // zero guard falls to UNSAT(P ∧ divisor == 0); the stream itself is
        // untouched (marks only).
        let ops = vec![
            LocalGet(0), // 0  n
            LocalGet(1), // 1  d  ← fact [1,100]
            I32DivU,     // 2  → zero mark
            Drop,        // 3
            LocalGet(0), // 4
            LocalGet(1), // 5  ← fact [1,100]
            I32RemU,     // 6  → zero mark
            Drop,        // 7
            LocalGet(0), // 8
            LocalGet(1), // 9  ← fact [1,100]
            I32RemS,     // 10 → zero mark
            End,         // 11
        ];
        let facts = [fact(1, 1, 100), fact(5, 1, 100), fact(9, 1, 100)];
        let r = specialize_function("f", &ops, &[], &facts, &[]);
        assert_eq!(
            r.elide_div_zero,
            vec![2, 6, 10],
            "declines: {:?}",
            r.declined
        );
        assert_eq!(
            r.elide_div_ovf,
            Vec::<usize>::new(),
            "no div_s in the stream"
        );
        assert!(!r.changed(), "guard marks never rewrite the op stream");
        assert_eq!(r.ops, ops);
        assert_eq!(r.admitted.len(), 3);
        for line in &r.admitted {
            assert!(line.contains("divide-by-zero guard elided"), "{line}");
            assert!(line.contains("UNSAT(P ∧ divisor == 0)"), "{line}");
            assert!(line.contains("certificate-checked"), "{line}");
        }
    }

    #[test]
    fn nonzero_fact_elides_zero_guard_but_retains_div_s_overflow_guard_494() {
        // THE TWO-GUARD DISTINCTION (#633/#634): a divisor-nonzero fact (kind
        // 3) discharges UNSAT(P ∧ divisor == 0) but NOT the overflow
        // obligation — divisor ≠ 0 still admits divisor == -1 with dividend
        // == INT_MIN, so the overflow guard is RETAINED with a loud decline.
        let ops = vec![
            LocalGet(0), // 0
            LocalGet(1), // 1 ← divisor-nonzero fact
            I32DivS,     // 2
            End,         // 3
        ];
        let r = specialize_function("f", &ops, &[], &[nonzero_fact(1)], &[]);
        assert_eq!(r.elide_div_zero, vec![2], "declines: {:?}", r.declined);
        assert_eq!(
            r.elide_div_ovf,
            Vec::<usize>::new(),
            "divisor ≠ 0 must NOT elide the INT_MIN/-1 overflow guard"
        );
        assert!(
            r.declined
                .iter()
                .any(|d| d.contains("overflow-guard obligation Sat") && d.contains("RETAINED")),
            "{:?}",
            r.declined
        );
    }

    #[test]
    fn positive_range_discharges_both_div_s_obligations_494() {
        // divisor ∈ [1, 100] excludes BOTH 0 and -1 — the two obligations
        // are discharged independently and both guards fall.
        let ops = vec![LocalGet(0), LocalGet(1), I32DivS, End];
        let r = specialize_function("f", &ops, &[], &[fact(1, 1, 100)], &[]);
        assert_eq!(r.elide_div_zero, vec![2], "declines: {:?}", r.declined);
        assert_eq!(r.elide_div_ovf, vec![2]);
        assert_eq!(r.admitted.len(), 2, "one certificate line per obligation");
        assert!(
            r.admitted
                .iter()
                .any(|a| a.contains("overflow guard elided")
                    && a.contains("dividend == INT32_MIN ∧ divisor == -1")),
            "{:?}",
            r.admitted
        );
    }

    #[test]
    fn range_including_zero_is_sat_and_declines_the_zero_guard_494() {
        // divisor ∈ [0, 100]: divisor == 0 is P-admissible — the obligation
        // is Sat, the decline is loud and carries a model, no mark is set.
        let ops = vec![LocalGet(0), LocalGet(1), I32DivU, End];
        let r = specialize_function("f", &ops, &[], &[fact(1, 0, 100)], &[]);
        assert_eq!(r.elide_div_zero, Vec::<usize>::new());
        assert!(
            r.declined
                .iter()
                .any(|d| d.contains("zero-guard obligation Sat") && d.contains("counterexample")),
            "{:?}",
            r.declined
        );
    }

    #[test]
    fn i64_div_s_nonzero_fact_zero_guard_only_overflow_retained_494() {
        // Oracle 5 at the pass level: i64.div_s with an i64 param divisor
        // carrying a divisor-nonzero fact — the zero guard is proven dead,
        // the INT64_MIN/-1 overflow guard (#633/#634) is RETAINED.
        let ops = vec![LocalGet(0), LocalGet(1), I64DivS, End];
        let r = specialize_function("f", &ops, &[], &[nonzero_fact(1)], &[true, true]);
        assert_eq!(r.elide_div_zero, vec![2], "declines: {:?}", r.declined);
        assert_eq!(
            r.elide_div_ovf,
            Vec::<usize>::new(),
            "i64 overflow guard retained"
        );
        assert!(
            r.declined.iter().any(|d| d.contains("RETAINED")),
            "{:?}",
            r.declined
        );
    }

    #[test]
    fn i64_div_s_positive_range_discharges_both_obligations_494() {
        let ops = vec![LocalGet(0), LocalGet(1), I64DivS, End];
        let r = specialize_function("f", &ops, &[], &[fact(1, 1, 1000)], &[true, true]);
        assert_eq!(r.elide_div_zero, vec![2], "declines: {:?}", r.declined);
        assert_eq!(r.elide_div_ovf, vec![2]);
    }

    #[test]
    fn i64_div_on_undeclared_width_declines_no_marks_494() {
        // Without the params_i64 table the divisor local is symbolically
        // 32-bit — the width check declines rather than building a
        // wrong-width obligation.
        let ops = vec![LocalGet(0), LocalGet(1), I64DivU, End];
        let r = specialize_function("f", &ops, &[], &[nonzero_fact(1)], &[]);
        assert_eq!(r.elide_div_zero, Vec::<usize>::new());
        assert!(
            r.declined.iter().any(|d| d.contains("unexpected width")),
            "{:?}",
            r.declined
        );
    }

    #[test]
    fn div_with_no_premise_declines_loudly_494() {
        // The function carries a fact, but no premise reaches the divisor —
        // the obligation cannot even be posed; both guards stay.
        let ops = vec![
            LocalGet(0), // 0 ← fact on the DIVIDEND, not the divisor
            LocalGet(1), // 1 unconstrained divisor
            I32DivU,     // 2
            End,         // 3
        ];
        // A fact on op 0 (the dividend): premises exist but do not constrain
        // the divisor — Sat, decline.
        let r = specialize_function("f", &ops, &[], &[fact(0, 1, 5)], &[]);
        assert_eq!(r.elide_div_zero, Vec::<usize>::new());
        assert!(
            r.declined
                .iter()
                .any(|d| d.contains("zero-guard obligation Sat")),
            "{:?}",
            r.declined
        );
    }

    #[test]
    fn guard_marks_are_remapped_through_a_clamp_elision_494() {
        // A clamp elision rewrites the stream; a downstream div's mark must
        // land on the REWRITTEN index (the driver feeds the rewritten stream
        // to the selector, which keys guards by its own op index).
        let ops = vec![
            LocalGet(0),    // 0  ← fact [524, 1524]
            I32Const(476),  // 1
            I32Add,         // 2
            LocalSet(1),    // 3
            LocalGet(1),    // 4  -+ low clamp (elided 4..=10)
            I32Const(1000), // 5   |
            I32LtS,         // 6   |
            If,             // 7   |
            I32Const(1000), // 8   |
            LocalSet(1),    // 9   |
            End,            // 10 -+
            LocalGet(1),    // 11
            LocalGet(0),    // 12  divisor = ch ∈ [524, 1524] ⇒ nonzero
            I32DivU,        // 13  → zero mark (rewritten index 6)
            End,            // 14
        ];
        let r = specialize_function("f", &ops, &[(0, 0)], &[fact(0, 524, 1524)], &[]);
        assert!(r.changed(), "declines: {:?}", r.declined);
        assert_eq!(r.kept, vec![0, 1, 2, 3, 11, 12, 13, 14]);
        assert_eq!(
            r.ops,
            vec![
                LocalGet(0),
                I32Const(476),
                I32Add,
                LocalSet(1),
                LocalGet(1),
                LocalGet(0),
                I32DivU,
                End
            ]
        );
        assert_eq!(
            r.elide_div_zero,
            vec![6],
            "mark remapped from original op#13 to rewritten op#6"
        );
    }

    #[test]
    fn out_of_range_value_id_is_vacuous_494() {
        let ops = clamp_ops();
        let r = specialize_function("f", &ops, CLAMP_ARITY, &[fact(999, 524, 1524)], &[]);
        assert!(!r.changed());
        assert_eq!(r.ops, ops);
    }
}
