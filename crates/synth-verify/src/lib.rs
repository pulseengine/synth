//! Formal Verification for Synth Compiler
//!
//! This crate provides SMT-based translation validation and property-based testing
//! to formally verify the correctness of WebAssembly-to-native synthesis.
//!
//! # Architecture
//!
//! The verification system uses Z3 SMT solver to prove that synthesized native code
//! has semantically equivalent behavior to the input WASM code.
//!
//! ## Backend-Agnostic Traits
//!
//! `SourceSemantics` and `TargetSemantics` traits allow any backend to provide
//! SMT semantics. The ARM semantics are one implementation, behind the `arm` feature.
//!
//! ## Translation Validation
//!
//! For each synthesis rule WASM → target, we construct SMT formulas:
//! - φ_wasm: Semantics of WASM operations
//! - φ_target: Semantics of generated target operations
//! - Prove: ∀inputs. φ_wasm(inputs) ⟺ φ_target(inputs)

// Verification traits (always available)
#[cfg(feature = "z3-solver")]
pub mod traits;

// ARM semantics (behind arm + z3-solver features)
#[cfg(all(feature = "z3-solver", feature = "arm"))]
pub mod arm_semantics;

// WASM semantics (z3-solver only — source language for all backends)
#[cfg(feature = "z3-solver")]
pub mod wasm_semantics;

// Translation validator (requires arm for the existing concrete implementation)
#[cfg(all(feature = "z3-solver", feature = "arm"))]
pub mod translation_validator;

// Property-based testing (always available)
pub mod properties;

pub use properties::CompilerProperties;

#[cfg(all(feature = "z3-solver", feature = "arm"))]
pub use arm_semantics::{ArmSemantics, ArmState};
#[cfg(all(feature = "z3-solver", feature = "arm"))]
pub use translation_validator::{TranslationValidator, ValidationResult, VerificationError};
#[cfg(feature = "z3-solver")]
pub use wasm_semantics::WasmSemantics;

#[cfg(feature = "z3-solver")]
use z3::{Config, Solver};

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
    let mut cfg = Config::new();
    cfg.set_timeout_msec(30000); // 30 second timeout
    cfg.set_model_generation(true);
    z3::with_z3_config(&cfg, f)
}

/// Create a Z3 solver with default configuration
#[cfg(feature = "z3-solver")]
pub fn create_solver() -> Solver {
    Solver::new()
}

#[cfg(all(test, feature = "z3-solver"))]
mod tests {
    use super::*;

    #[test]
    fn test_z3_context_creation() {
        with_z3_context(|| {
            let solver = create_solver();
            assert_eq!(solver.check(), z3::SatResult::Sat);
        });
    }
}
