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
//! - **Everything else** — any backward branch (a loop), any residual/external
//!   label branch (unknown direction), any call (`Bl`/`Blx`, inter-procedural),
//!   any op whose encoder expansion contains an internal runtime loop
//!   (`i64` software div/rem), any unsupported core class — is DECLINED with a
//!   machine-readable reason. gale cannot size a budget from an unsound number,
//!   so a decline is strictly better than a guess.
//!
//! Loop-bound INFERENCE (recovering an unknown trip count) and inter-procedural
//! composition are the named scry / spar follow-ups, explicitly OUT of scope.
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

/// Why a function could not receive a sound static cycle bound. Each variant is a
/// distinct, machine-readable decline reason so a consumer (spar T4) can tell an
/// unbounded loop from an inter-procedural edge from an unsupported core.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum WcetDecline {
    /// A backward branch in the final instruction stream — a loop. Bounding it
    /// requires a trip count, which WASM does not carry; that is the scry
    /// loop-bound-inference follow-up.
    Loop,
    /// A call (`Bl`/`Blx`) — the bound is per-function (intra-procedural). Summing
    /// a callee's cost is the spar inter-procedural-composition follow-up.
    Call,
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
                "backward branch (loop) — a sound bound needs a trip count \
                 (scry loop-bound-inference follow-up)"
            }
            WcetDecline::Call => {
                "call (Bl/Blx) — per-function bound is intra-procedural \
                 (spar inter-procedural-composition follow-up)"
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

/// The per-function result: either a sound cycle bound or a loud decline.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "status", rename_all = "kebab-case")]
pub enum WcetFunction {
    /// A sound upper bound on this function's execution in cycles.
    Bounded {
        /// Function name (WASM export or generated).
        name: String,
        /// The sound worst-case cycle bound: for a loop-free function this is the
        /// SUM of each instruction's documented worst-case cycles (each executes
        /// at most once). Always ≥ any real execution under the stated
        /// precondition.
        cycles: u64,
        /// Number of ARM instructions summed (diagnostic).
        instr_count: usize,
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
        }
    }
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
