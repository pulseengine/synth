//! Formal Verification for Synth Compiler
//!
//! This crate provides SMT-based translation validation and property-based testing
//! to formally verify the correctness of WebAssembly-to-native synthesis.
//!
//! # Architecture
//!
//! The verification system proves that synthesized native code has
//! semantically equivalent behavior to the input WASM code, discharging the
//! QF_BV queries through a thin solver trait ([`solver::BvSolver`], #553):
//!
//! - **Default engine:** [`ordeal`] — pure Rust, certificate-checked
//!   (every `Unsat` verdict carries an LRAT proof validated by the trusted
//!   `ordeal-lrat` checker). No C++ toolchain required.
//! - **Differential oracle** (feature `z3-solver`): Z3, the former engine.
//!   With both backends compiled in and `SYNTH_SOLVER_DIFF=1`, every query
//!   runs through both — a verdict disagreement is a hard error; an ordeal
//!   `Unknown` falls through to Z3's verdict.
//!
//! ## Backend-Agnostic Traits
//!
//! `SourceSemantics` and `TargetSemantics` traits allow any backend to provide
//! SMT semantics. The ARM semantics are one implementation, behind the `arm`
//! feature. All semantics encode into the solver-agnostic [`term::BV`] /
//! [`term::Bool`] terms.
//!
//! ## Translation Validation
//!
//! For each synthesis rule WASM → target, we construct SMT formulas:
//! - φ_wasm: Semantics of WASM operations
//! - φ_target: Semantics of generated target operations
//! - Prove: ∀inputs. φ_wasm(inputs) ⟺ φ_target(inputs)

// Solver-agnostic terms + the thin solver trait (always available)
pub mod solver;
pub mod term;

// Trap-preservation obligations over `ordeal::trap` (VCR-VER-002, #166): maps
// WASM partial ops (div/rem, load/store, call_indirect, unreachable,
// float→int trunc) to trap
// conditions and gates a lowering on preserving them. Backend-agnostic (builds
// on `term`), so always available like `wasm_semantics`.
pub mod trap;

// Verification traits (always available)
pub mod traits;

// WASM semantics — source language for all backends (always available)
pub mod wasm_semantics;

// Proof-carrying specialization (VCR-PERF-002 / #494 Phase 2): value-range
// facts ⇒ dead conditional-branch elision, each site behind a per-elision
// ordeal obligation. Backend-agnostic (rewrites the WasmOp stream), so it is
// always available like `wasm_semantics`.
pub mod fact_spec;

// ARM semantics (behind the arm feature)
#[cfg(feature = "arm")]
pub mod arm_semantics;

// Translation validator (requires arm for the existing concrete implementation)
#[cfg(feature = "arm")]
pub mod translation_validator;

// Validator-pattern prototype (issue #76 — CompCert-style certifying
// validator scaffolding; see docs/validator-pattern.md).
#[cfg(feature = "arm")]
pub mod validator_pattern;

// Expansion-level certifying validation for the i64 pseudo-ops (#667 move 2):
// decodes the SHIPPED encoder's emitted Thumb-2 bytes and proves them
// equivalent to the WASM op — see docs/validator-pattern.md.
#[cfg(feature = "arm")]
pub mod expansion_validator;

// Property-based testing (requires arm: exercises the ARM synthesis rules)
#[cfg(feature = "arm")]
pub mod properties;

#[cfg(feature = "arm")]
pub use properties::CompilerProperties;

#[cfg(feature = "arm")]
pub use arm_semantics::{ArmSemantics, ArmState};
#[cfg(feature = "arm")]
pub use expansion_validator::{
    ExpansionError, ExpansionWitness, covered_i64_pseudo_selections, validate_expansion,
};
pub use fact_spec::{FactSpecResult, specialize_function};
pub use solver::{BvSolver, CheckOutcome, OrdealSolver, new_solver};
pub use term::{BV, Bool};
#[cfg(feature = "arm")]
pub use translation_validator::{
    CallIndirectSpec, TranslationValidator, ValidationResult, VerificationError,
};
#[cfg(feature = "arm")]
pub use validator_pattern::{
    CertifiedSelection, SolverResultKind, ValidationError as PatternValidationError, Validator,
    Witness, Z3ArmValidator,
};
pub use wasm_semantics::WasmSemantics;

/// Run verification operations in a configured context.
///
/// With the default (ordeal) engine this is a plain call — the pure-Rust
/// solver needs no global context. With the `z3-solver` feature compiled in,
/// it additionally configures the Z3 thread-local context (30-second timeout,
/// model generation) so the differential oracle is ready.
pub fn with_verification_context<F, R>(f: F) -> R
where
    F: FnOnce() -> R + Send + Sync,
    R: Send + Sync,
{
    #[cfg(feature = "z3-solver")]
    {
        with_z3_context(f)
    }
    #[cfg(not(feature = "z3-solver"))]
    {
        f()
    }
}

/// Run verification operations with a configured Z3 context.
///
/// Z3 0.19 uses thread-local context — this function configures it
/// with a 30-second timeout and model generation enabled.
#[cfg(feature = "z3-solver")]
pub fn with_z3_context<F, R>(f: F) -> R
where
    F: FnOnce() -> R + Send + Sync,
    R: Send + Sync,
{
    let mut cfg = z3::Config::new();
    cfg.set_timeout_msec(30000); // 30 second timeout
    cfg.set_model_generation(true);
    z3::with_z3_config(&cfg, f)
}

/// Create a Z3 solver with default configuration (differential-oracle use)
#[cfg(feature = "z3-solver")]
pub fn create_solver() -> z3::Solver {
    z3::Solver::new()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_solver_decides() {
        with_verification_context(|| {
            let mut solver = new_solver();
            let x = BV::new_const("x", 32);
            solver.assert(&x.eq(&x).not());
            assert_eq!(solver.check(), CheckOutcome::Unsat);
        });
    }

    #[cfg(feature = "z3-solver")]
    #[test]
    fn test_z3_context_creation() {
        with_z3_context(|| {
            let solver = create_solver();
            assert_eq!(solver.check(), z3::SatResult::Sat);
        });
    }
}
