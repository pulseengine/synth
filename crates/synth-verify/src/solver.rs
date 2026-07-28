//! The thin solver trait behind which the SMT engines sit (#553).
//!
//! Queries are built once as solver-agnostic terms ([`crate::term`]) and
//! discharged through [`BvSolver`]:
//!
//! - [`OrdealSolver`] — the **default engine**: `ordeal`, the pure-Rust,
//!   certificate-checked QF_BV solver (every `Unsat` carries an LRAT proof
//!   the trusted `ordeal-lrat` checker validated before it is reported).
//!   No C++ toolchain, no `z3-sys` build.
//! - `Z3Solver` (feature `z3-solver`) — the former engine, retained as the
//!   **differential oracle**.
//! - `DifferentialSolver` — used when both backends are compiled in and
//!   `SYNTH_SOLVER_DIFF=1`: every query runs through both engines. A verdict
//!   disagreement (`Sat` vs `Unsat`) is a **hard error** (panic — one of the
//!   solvers is wrong, and nothing downstream may proceed on either answer).
//!   An ordeal `Unknown` falls through to Z3's verdict (logged, not fatal —
//!   `Unknown` is the conservative non-answer, not a verdict).
//!
//! Budget: every query runs under a **wall-clock deadline**
//! (`Solver::check_with_deadline`, ordeal ≥0.15) so an adversarial query
//! degrades to a clean conservative `Unknown` instead of hanging. See
//! [`DEFAULT_DEADLINE_MS`] for the budget, the env overrides and the
//! documented limitation.

use crate::term::{BV, Bool};
use ordeal::{BoolTerm, CheckResult};

/// Default conflict budget for the ordeal CDCL core. The synth burn-in corpus
/// (pulseengine/ordeal#29) decides at a median of ~1 ms and well under this;
/// the budget exists to bound adversarial shapes (e.g. non-canonicalized
/// commuted multiplies) to a conservative `Unknown`.
///
/// Only consulted when the wall-clock deadline is explicitly disabled
/// (`SYNTH_ORDEAL_DEADLINE_MS=0`) — ordeal's `Bound` is one-of, so a query
/// carries either a deadline or a conflict cap, never both.
const DEFAULT_MAX_CONFLICTS: u64 = 1_000_000;

/// Default **wall-clock** per-query budget, in milliseconds (#848/#849).
///
/// This is the real insurance against a solver cliff. A conflict budget does
/// not map to wall-clock time: the 4–6 h CI hangs of #849 burned hours inside
/// a single `check` that never came near 1 M conflicts, because there was no
/// wall-clock floor anywhere in the stack.
///
/// # Why 5 minutes and not 15 seconds
///
/// The budget must clear the slowest **legitimate** query with real headroom,
/// or it converts a sound proof into a spurious `Unknown`. Measured pacer on
/// a dev host (debug build, ordeal 0.16.1): the pre-existing
/// `expansion_validator` popcnt-HAKMEM link-1 equivalence decides in
/// **40.6 s** — a 15 s budget cut it off (it is genuinely hard, not a cliff).
/// The re-landed 64-bit `bvurem`/`bvsrem` i64-rem value VCs, by contrast,
/// decide in **2.4 s** for all four tests combined. 5 min is ~7× the pacer,
/// enough that a slower/parallel-loaded CI runner cannot flake it, while
/// still turning a solver cliff from "6 hours" into "5 minutes".
///
/// The per-query deadline is the INNER floor; the outer one is
/// `timeout-minutes` on the CI `Test` / `Z3 Verification` jobs (also added in
/// #848 — neither had one, which is why #849 cost days rather than minutes).
/// Together they bound both a single cliff and the aggregate.
///
/// A query that exceeds the deadline yields [`CheckOutcome::Unknown`], which
/// every caller treats conservatively — it is **never** reported as
/// `Verified`. Soundness is unaffected: the deadline bounds only
/// completeness (ordeal's certificate gate and model self-check are
/// untouched, so an abandoned search can never produce a wrong verdict).
///
/// **Documented limitation:** `check_with_deadline` bounds the *SAT search*,
/// not bit-blasting/canonicalization. A query whose blast alone is
/// pathological can still exceed the budget before the clock is ever
/// consulted, so this is a strong bound on the dominant cost — not a
/// universal wall-clock guard. Treat it as the floor it is, and keep the
/// hard-query classes (64-bit `bvsrem`/`bvurem`) under CI timing watch.
const DEFAULT_DEADLINE_MS: u64 = 300_000;

/// Read the configured per-query wall-clock budget.
///
/// `SYNTH_ORDEAL_DEADLINE_MS` overrides [`DEFAULT_DEADLINE_MS`]. The value
/// `0` **disables** the deadline and falls back to the conflict budget — note
/// this deliberately differs from ordeal's own `check_with_deadline(0)`
/// (which admits only queries decided before the first conflict); disabling
/// re-opens the #849 hang class and exists only as a debugging escape hatch.
pub(crate) fn configured_deadline_ms() -> u64 {
    std::env::var("SYNTH_ORDEAL_DEADLINE_MS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(DEFAULT_DEADLINE_MS)
}

/// Outcome of a one-shot `check` of the asserted conjunction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckOutcome {
    /// The assertions are unsatisfiable (for a negated equivalence query:
    /// the equivalence is proven).
    Unsat,
    /// The assertions are satisfiable; a model is available via
    /// [`BvSolver::value`].
    Sat,
    /// The solver could not decide (budget/timeout). Callers must treat this
    /// conservatively.
    Unknown(String),
}

/// The thin solver interface: assert boolean terms, check once, read the
/// model back on `Sat`. One instance = one query (no incremental solving —
/// synth's translation-validation fragment is one-shot by design).
pub trait BvSolver {
    /// Engine name (diagnostics).
    fn name(&self) -> &'static str;

    /// Add `cond` to the asserted conjunction.
    fn assert(&mut self, cond: &Bool);

    /// Decide satisfiability of the asserted conjunction.
    fn check(&mut self) -> CheckOutcome;

    /// After [`CheckOutcome::Sat`]: the model value of a free variable
    /// (with model completion — unconstrained variables read as 0, matching
    /// z3's `eval(_, true)`). `None` if there is no model or `var` is not a
    /// free variable.
    fn value(&self, var: &BV) -> Option<u128>;
}

/// Construct the configured solver:
///
/// - default: [`OrdealSolver`];
/// - with the `z3-solver` feature compiled in **and** `SYNTH_SOLVER_DIFF=1`:
///   the differential solver (ordeal checked against Z3 on every query).
pub fn new_solver() -> Box<dyn BvSolver> {
    #[cfg(feature = "z3-solver")]
    if std::env::var("SYNTH_SOLVER_DIFF").as_deref() == Ok("1") {
        return Box::new(z3_backend::DifferentialSolver::new());
    }
    Box::new(OrdealSolver::new())
}

// ---------------------------------------------------------------------------
// ordeal backend (default)
// ---------------------------------------------------------------------------

/// The default engine: pure-Rust `ordeal` under a per-query wall-clock
/// deadline (with a conflict budget as the disabled-deadline fallback).
pub struct OrdealSolver {
    assertions: Vec<BoolTerm>,
    /// Wall-clock budget in ms; `0` = deadline disabled (use `max_conflicts`).
    deadline_ms: u64,
    max_conflicts: u64,
    model: Option<ordeal::Model>,
}

impl OrdealSolver {
    /// New solver bounded by `SYNTH_ORDEAL_DEADLINE_MS` (default
    /// [`DEFAULT_DEADLINE_MS`]; 0 = deadline off), falling back to the
    /// `SYNTH_ORDEAL_MAX_CONFLICTS` conflict budget (default
    /// [`DEFAULT_MAX_CONFLICTS`]; 0 = unbounded) when the deadline is off.
    pub fn new() -> Self {
        let max_conflicts = std::env::var("SYNTH_ORDEAL_MAX_CONFLICTS")
            .ok()
            .and_then(|v| v.parse().ok())
            .unwrap_or(DEFAULT_MAX_CONFLICTS);
        Self {
            assertions: Vec::new(),
            deadline_ms: configured_deadline_ms(),
            max_conflicts,
            model: None,
        }
    }

    /// New solver with an explicit wall-clock budget in ms (`0` = deadline
    /// off). Env-independent, so tests can pin a budget without racing the
    /// process-global environment.
    pub fn with_deadline_ms(deadline_ms: u64) -> Self {
        Self {
            deadline_ms,
            ..Self::new()
        }
    }
}

impl Default for OrdealSolver {
    fn default() -> Self {
        Self::new()
    }
}

impl BvSolver for OrdealSolver {
    fn name(&self) -> &'static str {
        "ordeal"
    }

    fn assert(&mut self, cond: &Bool) {
        self.assertions.push(cond.term().clone());
    }

    fn check(&mut self) -> CheckOutcome {
        let mut solver = ordeal::Solver::new();
        for a in &self.assertions {
            solver.assert(a.clone());
        }
        // ordeal's `Bound` is one-of (None | Conflicts | Deadline), so a query
        // carries EITHER the wall-clock deadline (the default, #848/#849) or
        // the conflict cap — the deadline wins because it is the bound that
        // actually maps to "CI must not hang".
        let (result, bound) = if self.deadline_ms > 0 {
            (
                solver.check_with_deadline(self.deadline_ms),
                format!("wall-clock deadline {} ms", self.deadline_ms),
            )
        } else if self.max_conflicts == 0 {
            (solver.check(), "unbounded".to_string())
        } else {
            (
                solver.check_with_limit(self.max_conflicts),
                format!("conflict budget {}", self.max_conflicts),
            )
        };
        match result {
            CheckResult::Unsat(_certificate) => CheckOutcome::Unsat,
            CheckResult::Sat(model) => {
                self.model = Some(model);
                CheckOutcome::Sat
            }
            // Budget/deadline exhaustion (or an out-of-fragment query) is the
            // conservative non-answer. Callers MUST NOT read it as proven —
            // `Unknown` never becomes `Verified` anywhere downstream.
            CheckResult::Unknown => {
                CheckOutcome::Unknown(format!("ordeal returned unknown ({bound})"))
            }
        }
    }

    fn value(&self, var: &BV) -> Option<u128> {
        let model = self.model.as_ref()?;
        let name = var.var_name()?;
        Some(
            model
                .assignments
                .iter()
                .find(|(n, _)| n == name)
                .map(|(_, v)| *v)
                // Model completion: a variable the SAT core never saw is
                // unconstrained; any value witnesses — use 0 (z3 does too).
                .unwrap_or(0),
        )
    }
}

// ---------------------------------------------------------------------------
// Z3 backend (feature-gated differential oracle)
// ---------------------------------------------------------------------------

#[cfg(feature = "z3-solver")]
mod z3_backend {
    use super::*;
    use ordeal::BvTerm;
    use z3::SatResult;
    use z3::ast::Ast;

    /// Translate an ordeal `BvTerm` into a Z3 AST (the two backends consume
    /// the identical canonicalized query).
    fn bv_to_z3(t: &BvTerm) -> z3::ast::BV {
        match t {
            BvTerm::Const { value, sort } => {
                if sort.width <= 64 {
                    z3::ast::BV::from_u64(*value as u64, sort.width)
                } else {
                    // Split a wide constant into two 64-bit halves.
                    let hi = z3::ast::BV::from_u64((value >> 64) as u64, sort.width - 64);
                    let lo = z3::ast::BV::from_u64(*value as u64, 64);
                    hi.concat(&lo)
                }
            }
            BvTerm::Var { name, sort } => z3::ast::BV::new_const(name.clone(), sort.width),
            BvTerm::Add(a, b) => bv_to_z3(a).bvadd(&bv_to_z3(b)),
            BvTerm::Sub(a, b) => bv_to_z3(a).bvsub(&bv_to_z3(b)),
            BvTerm::Mul(a, b) => bv_to_z3(a).bvmul(&bv_to_z3(b)),
            BvTerm::Udiv(a, b) => bv_to_z3(a).bvudiv(&bv_to_z3(b)),
            BvTerm::Urem(a, b) => bv_to_z3(a).bvurem(&bv_to_z3(b)),
            BvTerm::And(a, b) => bv_to_z3(a).bvand(&bv_to_z3(b)),
            BvTerm::Or(a, b) => bv_to_z3(a).bvor(&bv_to_z3(b)),
            BvTerm::Xor(a, b) => bv_to_z3(a).bvxor(&bv_to_z3(b)),
            BvTerm::Shl(a, b) => bv_to_z3(a).bvshl(&bv_to_z3(b)),
            BvTerm::Lshr(a, b) => bv_to_z3(a).bvlshr(&bv_to_z3(b)),
            BvTerm::Ashr(a, b) => bv_to_z3(a).bvashr(&bv_to_z3(b)),
            BvTerm::Rotr(a, b) => bv_to_z3(a).bvrotr(&bv_to_z3(b)),
            BvTerm::Extract { hi, lo, arg } => bv_to_z3(arg).extract(*hi, *lo),
            BvTerm::Concat(a, b) => bv_to_z3(a).concat(&bv_to_z3(b)),
            BvTerm::ZeroExt { by, arg } => bv_to_z3(arg).zero_ext(*by),
            BvTerm::SignExt { by, arg } => bv_to_z3(arg).sign_ext(*by),
            BvTerm::Ite { cond, then_, else_ } => {
                bool_to_z3(cond).ite(&bv_to_z3(then_), &bv_to_z3(else_))
            }
        }
    }

    fn bool_to_z3(t: &BoolTerm) -> z3::ast::Bool {
        match t {
            BoolTerm::Eq(a, b) => bv_to_z3(a).eq(&bv_to_z3(b)),
            BoolTerm::Ne(a, b) => bv_to_z3(a).eq(&bv_to_z3(b)).not(),
            BoolTerm::Ult(a, b) => bv_to_z3(a).bvult(&bv_to_z3(b)),
            BoolTerm::Ule(a, b) => bv_to_z3(a).bvule(&bv_to_z3(b)),
            BoolTerm::Ugt(a, b) => bv_to_z3(a).bvugt(&bv_to_z3(b)),
            BoolTerm::Uge(a, b) => bv_to_z3(a).bvuge(&bv_to_z3(b)),
            BoolTerm::Slt(a, b) => bv_to_z3(a).bvslt(&bv_to_z3(b)),
            BoolTerm::Sle(a, b) => bv_to_z3(a).bvsle(&bv_to_z3(b)),
            BoolTerm::Sgt(a, b) => bv_to_z3(a).bvsgt(&bv_to_z3(b)),
            BoolTerm::Sge(a, b) => bv_to_z3(a).bvsge(&bv_to_z3(b)),
            BoolTerm::Not(a) => bool_to_z3(a).not(),
            BoolTerm::And(a, b) => z3::ast::Bool::and(&[&bool_to_z3(a), &bool_to_z3(b)]),
            BoolTerm::Or(a, b) => z3::ast::Bool::or(&[&bool_to_z3(a), &bool_to_z3(b)]),
        }
    }

    /// The former engine, now the differential oracle.
    pub struct Z3Solver {
        assertions: Vec<BoolTerm>,
        model: Option<z3::Model>,
    }

    impl Z3Solver {
        pub fn new() -> Self {
            Self {
                assertions: Vec::new(),
                model: None,
            }
        }
    }

    impl BvSolver for Z3Solver {
        fn name(&self) -> &'static str {
            "z3"
        }

        fn assert(&mut self, cond: &Bool) {
            self.assertions.push(cond.term().clone());
        }

        fn check(&mut self) -> CheckOutcome {
            let solver = z3::Solver::new();
            // Same wall-clock floor as the ordeal path (#848/#849): the Z3
            // Verification job hung for 4-6 h on the very same 64-bit
            // bvsrem/bvurem queries, so the oracle gets the identical budget.
            // Z3's `timeout` param is milliseconds; on expiry it answers
            // `Unknown`, which is the conservative non-answer here too.
            let deadline_ms = super::configured_deadline_ms();
            if deadline_ms > 0 {
                let mut params = z3::Params::new();
                params.set_u32("timeout", u32::try_from(deadline_ms).unwrap_or(u32::MAX));
                solver.set_params(&params);
            }
            for a in &self.assertions {
                solver.assert(bool_to_z3(a));
            }
            match solver.check() {
                SatResult::Unsat => CheckOutcome::Unsat,
                SatResult::Sat => {
                    self.model = solver.get_model();
                    if self.model.is_some() {
                        CheckOutcome::Sat
                    } else {
                        CheckOutcome::Unknown("z3: SAT but no model available".to_string())
                    }
                }
                SatResult::Unknown => CheckOutcome::Unknown("z3 returned unknown".to_string()),
            }
        }

        fn value(&self, var: &BV) -> Option<u128> {
            let model = self.model.as_ref()?;
            let z3_var = bv_to_z3(var.term());
            // z3::Model::eval is SMT model-value lookup (with completion),
            // not code evaluation.
            model
                .eval(&z3_var, true)
                .and_then(|v| v.as_u64())
                .map(u128::from)
        }
    }

    /// Which backend produced the authoritative model for the last `Sat`.
    #[derive(Clone, Copy, PartialEq)]
    enum ModelSource {
        Ordeal,
        Z3,
    }

    /// Runs every query through **both** engines (`SYNTH_SOLVER_DIFF=1`).
    ///
    /// Disagreement on a decided verdict is a hard error: it means one of
    /// the solvers is unsound on this query, and no downstream use of either
    /// answer is safe. ordeal `Unknown` falls through to Z3's verdict.
    pub struct DifferentialSolver {
        ordeal: OrdealSolver,
        z3: Z3Solver,
        model_source: ModelSource,
    }

    impl DifferentialSolver {
        pub fn new() -> Self {
            Self {
                ordeal: OrdealSolver::new(),
                z3: Z3Solver::new(),
                model_source: ModelSource::Ordeal,
            }
        }
    }

    impl BvSolver for DifferentialSolver {
        fn name(&self) -> &'static str {
            "ordeal+z3-differential"
        }

        fn assert(&mut self, cond: &Bool) {
            self.ordeal.assert(cond);
            self.z3.assert(cond);
        }

        fn check(&mut self) -> CheckOutcome {
            let ordeal_verdict = self.ordeal.check();
            let z3_verdict = self.z3.check();
            match (&ordeal_verdict, &z3_verdict) {
                // ordeal could not decide: conservative fall-through to the
                // oracle's verdict (logged — this is the measurable residue
                // the ordeal budget/normalization roadmap tracks).
                (CheckOutcome::Unknown(reason), _) => {
                    eprintln!(
                        "[synth-verify differential] ordeal unknown ({reason}); \
                         falling through to z3 verdict: {z3_verdict:?}"
                    );
                    self.model_source = ModelSource::Z3;
                    z3_verdict
                }
                // Oracle could not decide but ordeal did: verdicts do not
                // disagree; keep ordeal's decided answer.
                (_, CheckOutcome::Unknown(reason)) => {
                    eprintln!(
                        "[synth-verify differential] z3 unknown ({reason}); \
                         keeping ordeal verdict: {ordeal_verdict:?}"
                    );
                    self.model_source = ModelSource::Ordeal;
                    ordeal_verdict
                }
                (CheckOutcome::Unsat, CheckOutcome::Unsat) => CheckOutcome::Unsat,
                (CheckOutcome::Sat, CheckOutcome::Sat) => {
                    self.model_source = ModelSource::Ordeal;
                    CheckOutcome::Sat
                }
                // Decided disagreement: one solver is wrong. Hard error.
                (o, z) => panic!(
                    "SOLVER DISAGREEMENT (#553 differential oracle): \
                     ordeal={o:?} z3={z:?} on the same query — one engine is \
                     unsound on this fragment; refusing to proceed"
                ),
            }
        }

        fn value(&self, var: &BV) -> Option<u128> {
            match self.model_source {
                ModelSource::Ordeal => self.ordeal.value(var),
                ModelSource::Z3 => self.z3.value(var),
            }
        }
    }
}

#[cfg(feature = "z3-solver")]
pub use z3_backend::{DifferentialSolver, Z3Solver};

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn x32() -> BV {
        BV::new_const("x", 32)
    }
    fn y32() -> BV {
        BV::new_const("y", 32)
    }

    /// Small equivalence corpus: (label, query, expect_unsat).
    /// Every query is a negated equivalence, exactly the validator's shape.
    fn corpus() -> Vec<(&'static str, Bool, bool)> {
        let x = x32();
        let y = y32();
        let one = BV::from_i64(1, 32);
        vec![
            ("add-comm", x.bvadd(&y).eq(y.bvadd(&x)).not(), true),
            ("mul-comm", x.bvmul(&y).eq(y.bvmul(&x)).not(), true),
            ("and-comm", x.bvand(&y).eq(y.bvand(&x)).not(), true),
            (
                "shl1-vs-mul2",
                x.bvshl(&one).eq(x.bvmul(BV::from_i64(2, 32))).not(),
                true,
            ),
            (
                "sub-not-comm",
                x.bvsub(&y).eq(y.bvsub(&x)).not(),
                false, // SAT: x-y != y-x has witnesses
            ),
            (
                "ite-select",
                {
                    let c = x.eq(BV::from_i64(0, 32)).not();
                    c.ite(&y, &one).eq(c.ite(&y, &one)).not()
                },
                true,
            ),
            (
                "add-vs-sub-bug",
                x.bvadd(&y).eq(x.bvsub(&y)).not(),
                false, // SAT: differs whenever y != 0
            ),
        ]
    }

    #[test]
    fn ordeal_decides_the_corpus() {
        for (label, query, expect_unsat) in corpus() {
            let mut solver = OrdealSolver::new();
            solver.assert(&query);
            let outcome = solver.check();
            if expect_unsat {
                assert_eq!(outcome, CheckOutcome::Unsat, "{label}");
            } else {
                assert_eq!(outcome, CheckOutcome::Sat, "{label}");
                // Model readback must produce usable witness values.
                assert!(solver.value(&x32()).is_some(), "{label}: no model value");
            }
        }
    }

    #[test]
    fn ordeal_finds_counterexample_with_model() {
        // x + 1 == x - 1 is UNSAT-free: always differs -> negation is... the
        // direct assertion x+1 == x-1 is unsatisfiable; assert the EQUALITY
        // and expect Unsat, then assert a satisfiable disequality and read
        // the model back.
        let x = x32();
        let mut solver = OrdealSolver::new();
        solver.assert(
            &x.bvadd(BV::from_i64(1, 32))
                .eq(x.bvsub(BV::from_i64(1, 32))),
        );
        assert_eq!(solver.check(), CheckOutcome::Unsat);

        let mut solver = OrdealSolver::new();
        solver.assert(&x.eq(BV::from_i64(7, 32)));
        assert_eq!(solver.check(), CheckOutcome::Sat);
        assert_eq!(solver.value(&x), Some(7));
    }

    #[test]
    fn bool_var_bridge_is_symbolic() {
        // Bool::new_const must be genuinely free: both polarities satisfiable.
        let flag = Bool::new_const("flag");
        let one = BV::from_i64(1, 32);
        let zero = BV::from_i64(0, 32);
        // `out` selects on the flag; constraining the flag's polarity must
        // force the selected value — in both directions.
        for (cond, expected) in [(flag.clone(), 1u128), (flag.not(), 0u128)] {
            let mut solver = OrdealSolver::new();
            let out = flag.ite(&one, &zero);
            let probe = BV::new_const("probe", 32);
            solver.assert(&probe.eq(&out));
            solver.assert(&cond);
            assert_eq!(solver.check(), CheckOutcome::Sat);
            assert_eq!(solver.value(&probe), Some(expected));
        }
    }

    // --- per-query wall-clock deadline (#848/#849) ---

    /// The negated multiplication-**associativity** goal at a chosen width:
    /// `¬((x·y)·z == x·(y·z))`. Valid at every width (so a decided verdict is
    /// always `Unsat`), but *hard* for a CDCL core: commutativity is folded
    /// away by canonicalization, associativity is not, so proving it needs a
    /// real multiplier blast + search. This is exactly the shape the deadline
    /// exists to bound.
    ///
    /// Cost scales viciously — measured unbounded on a dev host (debug build,
    /// ordeal 0.16.1): width 8, 16 and 32 all run **>30 s**, width 3 decides
    /// in milliseconds. Hence the two widths below.
    fn mul_assoc_goal(width: u32) -> Bool {
        let x = BV::new_const("ha_x", width);
        let y = BV::new_const("ha_y", width);
        let z = BV::new_const("ha_z", width);
        x.bvmul(&y).bvmul(&z).eq(x.bvmul(&y.bvmul(&z))).not()
    }

    /// Wide enough that no 1 ms budget can finish it (>30 s unbounded).
    const HARD_WIDTH: u32 = 8;
    /// Narrow enough to decide in milliseconds — the cheap validity control.
    const EASY_WIDTH: u32 = 3;

    /// SOUNDNESS GATE: a query that exceeds its wall-clock deadline must
    /// degrade to [`CheckOutcome::Unknown`] — **never** `Unsat`, which every
    /// caller reads as "proven". This is the mechanism that would have turned
    /// the #849 six-hour hang into a bounded, loud non-answer.
    ///
    /// Non-vacuity comes from the narrow control: the SAME construction at
    /// [`EASY_WIDTH`] decides `Unsat` in milliseconds, so the `Unknown` above
    /// is the deadline biting a well-formed, in-fragment, *valid* obligation —
    /// not a query builder bug or an out-of-fragment term. (Associativity is a
    /// mathematical identity at every width; what the control rules out is a
    /// coding error in `mul_assoc_goal`, which is the only way this gate could
    /// go vacuous.) Re-proving the width-8 instance unbounded would cost the
    /// suite >30 s for no extra information.
    #[test]
    fn deadline_degrades_to_unknown_never_to_proven() {
        // 1 ms: orders of magnitude below what the wide instance needs.
        let mut bounded = OrdealSolver::with_deadline_ms(1);
        bounded.assert(&mul_assoc_goal(HARD_WIDTH));
        let outcome = bounded.check();
        assert!(
            matches!(outcome, CheckOutcome::Unknown(_)),
            "an undecided query must be Unknown, got {outcome:?}"
        );
        assert_ne!(
            outcome,
            CheckOutcome::Unsat,
            "SOUNDNESS: a timed-out query must never be reported as proven"
        );
        // And it must say *why* — a deadline, not a silent shrug.
        let CheckOutcome::Unknown(reason) = &outcome else {
            unreachable!("asserted above")
        };
        assert!(
            reason.contains("deadline"),
            "the non-answer must name the bound that produced it, got {reason:?}"
        );

        // Non-vacuity control: same construction, narrow, given the time.
        let mut control = OrdealSolver::with_deadline_ms(0);
        control.assert(&mul_assoc_goal(EASY_WIDTH));
        assert_eq!(
            control.check(),
            CheckOutcome::Unsat,
            "control: the mul-associativity goal is well-formed and valid"
        );
    }

    /// The deadline must not cost decidability on ordinary queries: the whole
    /// equivalence corpus still decides under the shipped default budget.
    #[test]
    fn default_deadline_decides_the_corpus() {
        for (label, query, expect_unsat) in corpus() {
            let mut solver = OrdealSolver::new();
            solver.assert(&query);
            let outcome = solver.check();
            assert_ne!(
                outcome,
                CheckOutcome::Unknown(format!(
                    "ordeal returned unknown (wall-clock deadline {DEFAULT_DEADLINE_MS} ms)"
                )),
                "{label}: default budget must not starve an ordinary query"
            );
            if expect_unsat {
                assert_eq!(outcome, CheckOutcome::Unsat, "{label}");
            } else {
                assert_eq!(outcome, CheckOutcome::Sat, "{label}");
            }
        }
    }

    /// The differential oracle itself: run the corpus through BOTH engines.
    /// Any decided disagreement panics inside `DifferentialSolver::check`.
    /// This runs in the CI Z3 job (`--features z3-solver,arm`) regardless of
    /// the SYNTH_SOLVER_DIFF env, so the cross-check is always exercised
    /// where Z3 is available.
    #[cfg(feature = "z3-solver")]
    #[test]
    fn differential_zero_disagreements_on_corpus() {
        crate::with_z3_context(|| {
            for (label, query, expect_unsat) in corpus() {
                let mut solver = DifferentialSolver::new();
                solver.assert(&query);
                let outcome = solver.check();
                if expect_unsat {
                    assert_eq!(outcome, CheckOutcome::Unsat, "{label}");
                } else {
                    assert_eq!(outcome, CheckOutcome::Sat, "{label}");
                }
            }
        });
    }
}
