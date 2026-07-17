//! #778 (v0.46 Wave-1 Lane 2) — the `synth-wcet-v1` static worst-case-cycle map.
//!
//! synth holds the EXACT final instruction sequence of every compiled function,
//! so it is the natural owner of a SOUND static per-function worst-case execution
//! time (WCET) bound. gale's schedulability track (spar T3/T4) computes a
//! machine-checked response-time bound, but its per-task cost inputs (`C_i`) are
//! only DWT high-water-marks — *observations*, not *bounds* — and a hard build
//! gate forbids sizing budgets from DWT. This sidecar supplies the missing SOUND
//! input: a cycle bound that is provably ≥ any real execution of the function.
//!
//! ## Soundness contract (the whole point)
//!
//! A bound that is EVER less than the real cycle count is a defect. This module
//! is therefore deliberately conservative and DECLINES loudly rather than emit a
//! number it cannot defend:
//!
//! - **Loop-free functions** get an EXACT-form bound: every instruction in the
//!   final stream executes at most once, so the bound is the SUM of each
//!   instruction's documented worst-case cycles. Summing every instruction
//!   (including both arms of an `if/else`) is an over-estimate, hence sound; no
//!   path enumeration is needed.
//! - **Loops with statically-evident trip counts** (#778 phase 2): a canonical
//!   counted loop — const-initialized counter, const step, const bound, single
//!   backward branch — whose trip count synth PROVES from the final instruction
//!   stream gets `trip × body-worst + overhead` as an upper bound; every
//!   instruction's cost is multiplied by its proven worst-case execution count.
//!   Nested loops multiply only when EVERY level proves.
//! - **Everything else** — any loop synth cannot prove a trip count for
//!   (data-dependent bounds, non-canonical shapes), any residual/external
//!   label branch (unknown direction), any call (`Bl`/`Blx`, inter-procedural),
//!   any op whose encoder expansion contains an internal runtime loop
//!   (`i64` software div/rem), any unsupported core class — is DECLINED with a
//!   machine-readable reason. gale cannot size a budget from an unsound number,
//!   so a decline is strictly better than a guess.
//!
//! `--wcet-hints` (#778 phase 2, the scry seam) supplies UNTRUSTED per-loop
//! trip-count hints; each is soundly CHECKED against synth's own induction
//! proof before use and REJECTED with a machine reason otherwise (see
//! [`WcetHints`] / [`WcetHintReject`]). Richer hint certificates (data-dependent
//! bounds) and inter-procedural composition remain the named scry / spar
//! follow-ups, explicitly OUT of scope.
//!
//! ## Precondition — a bound without its assumptions is not a safety input
//!
//! The per-instruction cycle numbers are documented worst cases for the
//! **Cortex-M3 / Cortex-M4(F)** in-order pipeline under a **zero-wait-state**
//! instruction memory (flash accelerator / I-cache hit). The bound is CONDITIONAL
//! on that precondition, which is recorded in the JSON (`core_class`,
//! `wait_states`, `memory_assumption`) so the T4 consumer knows exactly what it
//! holds under. Cortex-M7 (dual-issue + caches with wait-states that can make
//! actual cycles EXCEED a zero-wait straight sum) is DECLINED, not
//! approximated — soundness over coverage.
//!
//! ## Schema (`synth-wcet-v1`)
//!
//! A JSON sidecar written next to the object (`<output>.wcet.json`). Purely
//! additive metadata: it is derived from the already-decided instruction stream
//! and never touches `.text`, so the emitted bytes are byte-identical whether or
//! not the bound is emitted (frozen-safe).

use serde::{Deserialize, Serialize};

/// The schema version string embedded at the top of the sidecar.
pub const SCHEMA: &str = "synth-wcet-v1";

/// The schema string a `--wcet-hints` file must carry (#778 phase 2).
pub const HINTS_SCHEMA: &str = "synth-wcet-hints-v1";

/// Why a function could not receive a sound static cycle bound. Each variant is a
/// distinct, machine-readable decline reason so a consumer (spar T4) can tell an
/// unbounded loop from an inter-procedural edge from an unsupported core.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WcetDecline {
    /// A backward branch in the final instruction stream — a loop — whose trip
    /// count synth could NOT statically prove (#778 phase 2 proves canonical
    /// const-init/const-step/const-bound counted loops; equality-exit shapes
    /// additionally need a verified `--wcet-hints` entry). Data-dependent
    /// bounds remain the scry loop-bound-inference follow-up.
    Loop,
    /// A DIRECT call (`Bl func_N`) that could not be composed into a bound because
    /// the callee is unbounded or unresolvable in THIS module — an external/imported
    /// callee (a WASM import, `__meld_dispatch_import`, or an `__aeabi_*` runtime
    /// helper: it has no per-function body in this module to sum). #778 phase 3
    /// composes direct calls to LOCAL, bounded callees over the direct call graph;
    /// this reason remains for the direct edges that cannot be composed.
    Call,
    /// A cycle in the direct call graph (self-recursion or mutual recursion). An
    /// upper cycle bound cannot be composed from a call graph that revisits a frame
    /// an unbounded number of times, so every function on the cycle DECLINES. This
    /// is the #778 phase-3 decline-honesty guard: composition only bounds an acyclic
    /// direct call graph.
    Recursion,
    /// An INDIRECT call (`Blx <reg>` / `call_indirect` / a function-pointer
    /// dispatch such as `__meld_dispatch_import`): the callee is not statically
    /// known, so its bound cannot be composed. Declined, not guessed. (#778 phase 3.)
    IndirectCall,
    /// A caller whose own body is bounded but that DIRECTLY calls a callee which
    /// itself declined (transitively): a decline must PROPAGATE up the call graph —
    /// a caller cannot be bounded while a callee it invokes is unbounded. (#778
    /// phase 3.) The `note()` names the first unbounded callee for diagnosis.
    CalleeUnbounded,
    /// A residual/external label branch (`B`/`Bcc`/… still carrying a label): its
    /// direction is not statically known here, so it cannot be proven loop-free.
    UnresolvedBranch,
    /// An op whose encoder expansion contains an internal RUNTIME loop (the `i64`
    /// software div/rem shift-subtract: emitted once but executed 64×). Its body
    /// bytes appear once in the stream, so a straight sum would undercount — a
    /// sound bound needs a per-op `trip × body` model, a named follow-up.
    LoopedExpansion,
    /// The target core class is not soundly summable with a zero-wait per-op table
    /// (Cortex-M7/M7dp: dual-issue + cache wait-states). Declined, not
    /// approximated.
    UnsupportedCore,
    /// An op the cycle model has not classified. Never emitted in a released
    /// build (the classifier is exhaustive with no wildcard) — present so the
    /// schema can carry a conservative decline if the table is ever incomplete.
    UnmodeledOp,
}

impl WcetDecline {
    /// A short human-readable explanation, embedded alongside the machine reason.
    pub fn note(&self) -> &'static str {
        match self {
            WcetDecline::Loop => {
                "backward branch (loop) without a statically-proven trip count — \
                 canonical const-bound counted loops are proven automatically; \
                 equality-exit shapes need a verified --wcet-hints entry; \
                 data-dependent bounds are the scry loop-bound-inference follow-up"
            }
            WcetDecline::Call => {
                "direct call to an external/imported/unresolvable callee with no \
                 per-function bound in this module — cannot compose an \
                 inter-procedural bound (local direct calls ARE composed, #778 phase 3)"
            }
            WcetDecline::Recursion => {
                "cycle in the direct call graph (self- or mutual recursion) — an \
                 upper cycle bound cannot be composed from a recursive call graph"
            }
            WcetDecline::IndirectCall => {
                "indirect call (Blx <reg> / call_indirect / function-pointer \
                 dispatch) — the callee is not statically known, cannot compose"
            }
            WcetDecline::CalleeUnbounded => {
                "a directly-called callee is itself unbounded — the decline \
                 propagates up the call graph (a caller cannot be bounded while a \
                 callee it invokes is unbounded)"
            }
            WcetDecline::UnresolvedBranch => {
                "residual external/unresolved label branch — direction not \
                 statically known, cannot prove loop-free"
            }
            WcetDecline::LoopedExpansion => {
                "op expands to an internal runtime loop (i64 software div/rem, \
                 executed 64×) — straight sum would undercount"
            }
            WcetDecline::UnsupportedCore => {
                "core class not soundly summable with a zero-wait per-op table \
                 (Cortex-M7 dual-issue + cache wait-states)"
            }
            WcetDecline::UnmodeledOp => "op not classified by the cycle model",
        }
    }
}

/// How a loop's trip count was established (#778 phase 2).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WcetLoopBoundSource {
    /// Fully static proof: const-initialized counter, const step, const bound,
    /// exit-guaranteeing comparison — the trip count is derived by synth alone.
    Static,
    /// The loop is an equality-exit shape synth only bounds under an explicit
    /// `--wcet-hints` assertion; the hint was CHECKED against synth's own derived
    /// trip count (divisibility + monotonicity + derived ≤ hint) before use. The
    /// emitted trip count is still synth's DERIVED value, never the raw hint.
    HintVerified,
}

/// One proven-bounded loop inside a bounded function (#778 phase 2). Loops are
/// listed in ascending `head_offset` order — the SAME order `--wcet-hints`
/// `loop_bounds` entries are matched by.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetLoopBound {
    /// Byte offset of the loop head (backward-branch target) within the function.
    pub head_offset: u64,
    /// The PROVEN maximum number of body executions (full iterations).
    pub trip_count: u64,
    /// Number of instructions inside the loop region (head..=backward branch),
    /// so a consumer can cross-check `cycles ≥ trip_count × region_instr_count`
    /// (every instruction costs ≥ 1 cycle).
    pub region_instr_count: usize,
    /// How the trip count was established.
    pub source: WcetLoopBoundSource,
    /// The hint value consumed (present iff `source == HintVerified` or a
    /// redundant hint was cross-checked against a static proof).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hint: Option<u64>,
}

/// Machine-readable reason a `--wcet-hints` entry was REJECTED (#778 phase 2).
/// The hint file is UNTRUSTED input: a hint is only ever consumed after synth
/// verifies the loop's induction against it; everything else lands here.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WcetHintReject {
    /// The hint is SMALLER than synth's own derived trip count — a wrong hint.
    /// Trusting it would emit a bound < a real execution (the fatal class).
    HintBelowDerivedTrip,
    /// synth could not verify the loop's induction against the hint (counter not
    /// provably monotonic toward a statically-known bound ≤ hint — e.g. a
    /// data-dependent bound register, a non-canonical shape, or an equality exit
    /// whose step does not divide the distance). An unverifiable hint is never
    /// trusted into a bound.
    HintUnverifiableInduction,
    /// The hint indexes a loop that does not exist in this function's final
    /// instruction stream.
    HintUnknownLoop,
}

impl WcetHintReject {
    /// A short human-readable explanation, embedded alongside the machine reason.
    pub fn note(&self) -> &'static str {
        match self {
            WcetHintReject::HintBelowDerivedTrip => {
                "hint is below synth's derived trip count — a wrong hint; \
                 trusting it would emit an unsound bound"
            }
            WcetHintReject::HintUnverifiableInduction => {
                "loop induction not verifiable against the hint (counter not \
                 provably monotonic toward a statically-known bound ≤ hint) — \
                 an unverifiable hint is never trusted into a bound"
            }
            WcetHintReject::HintUnknownLoop => {
                "hint indexes a loop that does not exist in the final \
                 instruction stream"
            }
        }
    }
}

/// One rejected hint, recorded in the sidecar so the oracle (scry) sees exactly
/// which of its claims synth refused and why.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetHintRejection {
    /// Index into the function's `loop_bounds` hint array (== loop order by
    /// ascending head offset).
    pub loop_index: usize,
    /// Byte offset of the loop head this hint addressed, when the loop exists.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub head_offset: Option<u64>,
    /// The rejected hint value.
    pub hint: u64,
    /// Machine-readable rejection reason.
    pub reason: WcetHintReject,
    /// Human-readable note (`reason.note()`).
    pub note: String,
}

/// The per-function result: either a sound cycle bound or a loud decline.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum WcetFunction {
    /// A sound upper bound on this function's execution in cycles.
    Bounded {
        /// Function name (WASM export or generated).
        name: String,
        /// The sound worst-case cycle bound. For a loop-free function this is the
        /// SUM of each instruction's documented worst-case cycles (each executes
        /// at most once). For a function whose loops ALL have proven trip counts
        /// (#778 phase 2) each instruction's cost is multiplied by its proven
        /// worst-case execution count. Always ≥ any real execution under the
        /// stated precondition.
        cycles: u64,
        /// Number of ARM instructions summed (diagnostic).
        instr_count: usize,
        /// Proven loops (empty for a loop-free function), ascending head offset.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        loops: Vec<WcetLoopBound>,
        /// Hints that were rejected (the static proof stands independently).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        hint_rejections: Vec<WcetHintRejection>,
    },
    /// No bound emitted — a loud decline with a machine-readable reason. A decline
    /// is emitted (rather than the function omitted) so the map is COMPLETE: a
    /// consumer sees every function is either bounded or explicitly unbounded,
    /// never silently missing.
    Declined {
        /// Function name.
        name: String,
        /// Machine-readable reason.
        reason: WcetDecline,
        /// Human-readable note (`reason.note()`).
        note: String,
        /// Hints that were offered for this function and rejected.
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        hint_rejections: Vec<WcetHintRejection>,
    },
}

impl WcetFunction {
    /// Construct a decline, filling in the note from the reason.
    pub fn declined(name: impl Into<String>, reason: WcetDecline) -> Self {
        let note = reason.note().to_string();
        WcetFunction::Declined {
            name: name.into(),
            reason,
            note,
            hint_rejections: Vec::new(),
        }
    }

    /// Construct a decline carrying rejected-hint records.
    pub fn declined_with_rejections(
        name: impl Into<String>,
        reason: WcetDecline,
        hint_rejections: Vec<WcetHintRejection>,
    ) -> Self {
        let note = reason.note().to_string();
        WcetFunction::Declined {
            name: name.into(),
            reason,
            note,
            hint_rejections,
        }
    }
}

/// One direct call site inside a composable function (#778 phase 3). Records the
/// callee's `BL` label (`func_<idx>` for a local/relocatable-import call) and the
/// per-instruction execution-count multiplier of the `BL` (1 outside any loop; the
/// enclosing loop's proven trip product when the call sits inside a proven counted
/// loop, so a call in a loop is counted `trip` times, never once).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WcetCallSite {
    /// The `BL` target label as emitted by the selector (`func_<wasm_index>` for a
    /// direct local/import call; any other label is a runtime helper → external).
    pub callee_label: String,
    /// The call site's worst-case execution count (product of enclosing proven loop
    /// trip factors; 1 outside any loop). `u128` to survive deep nesting without
    /// wrapping, matching the loop-multiplier domain.
    pub multiplier: u128,
}

/// The per-function INTERMEDIATE result of the WCET pass BEFORE inter-procedural
/// composition (#778 phase 3). The backend produces one of these per function; the
/// module-level composer ([`crate::wcet`] consumers call `synth_backend::wcet_compose`)
/// resolves each function's direct call sites against the whole module and emits the
/// final [`WcetFunction`] (a composed bound, or a propagated/recursion/indirect
/// decline).
///
/// Splitting the pass in two keeps composition a PURE function over already-decided
/// per-function facts: `own_cycles` already prices every non-call instruction
/// (including each `BL`'s branch overhead) at its proven execution count, so the
/// composed total is `own_cycles + Σ_site multiplier_site × callee_total` — the
/// per-site multiplier makes a call inside a proven loop sound by construction.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WcetIntermediate {
    /// The function declines for a reason INDEPENDENT of composition (an unproven
    /// loop, an internal looped expansion, an unsupported core, an unresolved label
    /// branch, an indirect call, or an unmodeled op). Carried straight through to a
    /// [`WcetFunction::Declined`]; composition never rescues these.
    Declined {
        name: String,
        reason: WcetDecline,
        hint_rejections: Vec<WcetHintRejection>,
    },
    /// The function's own body is bounded; its final bound depends only on resolving
    /// the recorded direct call sites against the module's other functions.
    Composable {
        name: String,
        /// The summed worst-case cost of every instruction in the final stream
        /// (each priced at its documented worst case × its proven execution-count
        /// multiplier), INCLUDING each direct `BL`'s branch overhead. The callee
        /// bodies are added by the composer via `call_sites`.
        own_cycles: u64,
        /// Number of ARM instructions summed (diagnostic, carried to the bound).
        instr_count: usize,
        /// The direct call sites to resolve at compose time.
        call_sites: Vec<WcetCallSite>,
        /// Proven loops inside this function (carried to the bound unchanged).
        loops: Vec<WcetLoopBound>,
        /// Hints rejected while analyzing this function (carried to the bound).
        hint_rejections: Vec<WcetHintRejection>,
    },
}

impl WcetIntermediate {
    /// The compiled function name this intermediate is for.
    pub fn name(&self) -> &str {
        match self {
            WcetIntermediate::Declined { name, .. } | WcetIntermediate::Composable { name, .. } => {
                name
            }
        }
    }
}

/// The parsed `--wcet-hints` file (`synth-wcet-hints-v1`) — an UNTRUSTED oracle
/// input (#778 phase 2, the scry integration seam). Per function, an ordered
/// array of claimed loop-trip-count upper bounds, matched to loops by ascending
/// head offset (entry N = N-th loop head in the function; `null` skips a loop).
/// Every entry is soundly CHECKED before use: synth re-derives the loop's trip
/// count from its own induction proof and consumes the hint only when the
/// derived count is ≤ the hint. A wrong or unverifiable hint is rejected with a
/// machine reason ([`WcetHintReject`]) — never trusted into a bound.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetHints {
    /// Must equal [`HINTS_SCHEMA`].
    pub schema: String,
    /// Per-function hint arrays, keyed by the compiled function name.
    #[serde(default)]
    pub functions: std::collections::BTreeMap<String, WcetFunctionHints>,
}

/// Per-function loop-bound hints.
#[derive(Debug, Clone, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetFunctionHints {
    /// Claimed trip-count upper bounds, one per loop in ascending-head-offset
    /// order; `null` leaves that loop unhinted.
    #[serde(default)]
    pub loop_bounds: Vec<Option<u64>>,
}

/// The full `synth-wcet-v1` sidecar: schema header, precondition, and per-function
/// bounds/declines.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct WcetReport {
    /// Schema version (`synth-wcet-v1`).
    pub schema: String,
    /// The compiled module name (for diagnostics).
    pub module: String,
    /// The core class the cycle table is written for (e.g. `"cortex-m4"`). The
    /// bound is CONDITIONAL on this core.
    pub core_class: String,
    /// Assumed instruction-memory wait states (0 for the sound zero-wait table).
    pub wait_states: u32,
    /// Human statement of the memory precondition the bound holds under.
    pub memory_assumption: String,
    /// Per-function bound or decline. Complete: one entry per compiled function.
    pub functions: Vec<WcetFunction>,
}

impl WcetReport {
    /// Start an empty report for `module`, targeting `core_class` under the sound
    /// zero-wait precondition.
    pub fn new(module: impl Into<String>, core_class: impl Into<String>) -> Self {
        WcetReport {
            schema: SCHEMA.to_string(),
            module: module.into(),
            core_class: core_class.into(),
            wait_states: 0,
            memory_assumption:
                "zero-wait-state instruction memory (flash accelerator / I-cache hit); \
                 in-order single-issue pipeline; documented per-instruction worst-case cycles"
                    .to_string(),
            functions: Vec::new(),
        }
    }

    /// Serialize to pretty JSON.
    pub fn to_json(&self) -> serde_json::Result<String> {
        serde_json::to_string_pretty(self)
    }

    /// Resolve the sidecar path (`<output>.wcet.json`) next to the ELF output.
    pub fn sidecar_path(output: &std::path::Path) -> std::path::PathBuf {
        let mut s = output.as_os_str().to_os_string();
        s.push(".wcet.json");
        std::path::PathBuf::from(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bounded_and_declined_roundtrip() {
        let mut r = WcetReport::new("m", "cortex-m4");
        r.functions.push(WcetFunction::Bounded {
            name: "leaf".into(),
            cycles: 42,
            instr_count: 7,
            loops: Vec::new(),
            hint_rejections: Vec::new(),
        });
        r.functions
            .push(WcetFunction::declined("spins", WcetDecline::Loop));
        let json = r.to_json().unwrap();
        let back: WcetReport = serde_json::from_str(&json).unwrap();
        assert_eq!(r, back);
        // Decline reason is machine-readable and carries a note.
        assert!(json.contains("\"reason\": \"loop\""));
        assert!(json.contains("synth-wcet-v1"));
    }

    #[test]
    fn sidecar_path_appends_suffix() {
        let p = WcetReport::sidecar_path(std::path::Path::new("out/app.elf"));
        assert_eq!(p, std::path::PathBuf::from("out/app.elf.wcet.json"));
    }
}
