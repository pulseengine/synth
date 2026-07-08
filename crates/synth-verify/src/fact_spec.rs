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
//! * `i32.div*`/`i32.rem*` are deliberately NOT tracked: they can trap, and a
//!   deleted condition slice must be effect-free under ALL inputs, not just
//!   P-admissible ones (the premise only justifies the branch-direction, not
//!   trap removal — trap-guard elision is the separate divisor-nonzero fact,
//!   out of Phase-2 scope).
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
use std::collections::HashMap;
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
}

impl FactSpecResult {
    /// True when at least one elision was admitted (i.e. `ops` differs from
    /// the input).
    pub fn changed(&self) -> bool {
        !self.admitted.is_empty()
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
/// slice (`CompileConfig::current_func_facts`). Total: every input yields a
/// result — inapplicable shapes surface as loud declines, never errors.
pub fn specialize_function(
    func_name: &str,
    ops: &[WasmOp],
    block_arity: &[(u8, u8)],
    facts: &[WscFact],
) -> FactSpecResult {
    let mut pass = Pass::new(func_name, ops, block_arity, facts);
    pass.walk();
    pass.finish()
}

struct Pass<'a> {
    func: &'a str,
    ops: &'a [WasmOp],
    block_arity: &'a [(u8, u8)],
    /// op index → ordinal into `block_arity` (for `Block`/`Loop`/`If` ops).
    opener_ordinal: HashMap<usize, usize>,
    /// op index → signed i32 range fact attached to that op's result.
    range_facts: HashMap<usize, (i32, i32)>,
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
}

impl<'a> Pass<'a> {
    fn new(
        func: &'a str,
        ops: &'a [WasmOp],
        block_arity: &'a [(u8, u8)],
        facts: &'a [WscFact],
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
        for f in facts {
            if let FactKind::ValueRange { lo, hi } = f.kind {
                // i32-only prototype: clamp the s64 bound into i32; a bound
                // wholly outside i32 (or inverted) is vacuous — ignore it
                // (the encoding doc's rule for unusable facts).
                let lo = lo.clamp(i64::from(i32::MIN), i64::from(i32::MAX)) as i32;
                let hi = hi.clamp(i64::from(i32::MIN), i64::from(i32::MAX)) as i32;
                if lo <= hi && (f.value_id as usize) < ops.len() {
                    range_facts.insert(f.value_id as usize, (lo, hi));
                }
            }
        }
        Self {
            func,
            ops,
            block_arity,
            opener_ordinal,
            range_facts,
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
        let v = self.fresh_var(format!("fs_l{idx}"));
        self.locals.insert(idx, v.clone());
        v
    }

    /// Attach a value-range premise if a fact names op `i`'s result.
    fn attach_fact(&mut self, i: usize, bv: &BV) {
        if let Some(&(lo, hi)) = self.range_facts.get(&i) {
            let lo_bv = BV::from_i64(i64::from(lo), 32);
            let hi_bv = BV::from_i64(i64::from(hi), 32);
            let p = Bool::and(&[&bv.bvsge(&lo_bv), &bv.bvsle(&hi_bv)]);
            self.premises.push(p);
            self.premise_desc
                .push(format!("value(op#{i}) ∈ [{lo}, {hi}] (signed)"));
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
        if self.range_facts.is_empty() {
            self.decline("no usable value-range fact targets this function".to_string());
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
                WasmOp::If => {
                    let Some(cond) = self.stack.pop() else {
                        self.decline(format!("op#{i} `if` on empty symbolic stack"));
                        return;
                    };
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
            ..
        } = self;
        if deletions.is_empty() {
            return FactSpecResult {
                ops: ops.to_vec(),
                block_arity: block_arity.to_vec(),
                kept: (0..ops.len()).collect(),
                admitted,
                declined,
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
        FactSpecResult {
            ops: out_ops,
            block_arity: out_arity,
            kept,
            admitted,
            declined,
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
        let r = specialize_function("gust_mix", &ops, CLAMP_ARITY, &[fact(0, 524, 1524)]);
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
        let r = specialize_function("gust_mix", &ops, CLAMP_ARITY, &[fact(0, 0, 4000)]);
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
        let r = specialize_function("gust_mix", &ops, CLAMP_ARITY, &[fact(0, 524, 4000)]);
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
        let r = specialize_function("gust_mix", &ops, CLAMP_ARITY, &[]);
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
        let r = specialize_function("f", &ops, CLAMP_ARITY, &[fact(0, 524, 1524)]);
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
        let r = specialize_function("f", &ops, &[(0, 0)], &[fact(0, 0, 0)]);
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
        let r = specialize_function("f", &ops, arity, &[fact(0, 5, 5)]);
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
        let r = specialize_function("f", &ops, &[(0, 0)], &[fact(0, 1, 1)]);
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
        let r = specialize_function("f", &ops, &[], &[fact(0, 1, 2)]);
        assert!(!r.changed());
        assert!(
            r.declined.iter().any(|d| d.contains("outside the tracked")),
            "{:?}",
            r.declined
        );
    }

    #[test]
    fn out_of_range_value_id_is_vacuous_494() {
        let ops = clamp_ops();
        let r = specialize_function("f", &ops, CLAMP_ARITY, &[fact(999, 524, 1524)]);
        assert!(!r.changed());
        assert_eq!(r.ops, ops);
    }
}
