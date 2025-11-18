//! Formal Verification for Synth Compiler
//!
//! This crate provides SMT-based translation validation and property-based testing
//! to formally verify the correctness of WebAssembly-to-ARM synthesis.
//!
//! # Architecture
//!
//! The verification system uses Z3 SMT solver to prove that synthesized ARM code
//! has semantically equivalent behavior to the input WASM code.
//!
//! ## Translation Validation
//!
//! For each synthesis rule WASM → ARM, we construct SMT formulas:
//! - φ_wasm: Semantics of WASM operations
//! - φ_arm: Semantics of generated ARM operations
//! - Prove: ∀inputs. φ_wasm(inputs) ⟺ φ_arm(inputs)
//!
//! ## Proof Technique
//!
//! We use bounded translation validation (Alive2-style):
//! 1. Encode WASM operation semantics as SMT bitvector formulas
//! 2. Encode ARM operation semantics as SMT bitvector formulas
//! 3. For each synthesis rule, prove equivalence under all input values
//! 4. Use Z3 to either prove equivalence or find counterexample
//!
//! ## Property-Based Testing
//!
//! We use proptest to generate random test cases and verify properties:
//! - Type preservation
//! - Memory safety
//! - Control flow correctness
//! - Optimization semantic preservation

#[cfg(feature = "z3-solver")]
pub mod arm_semantics;
pub mod properties;
#[cfg(feature = "z3-solver")]
pub mod translation_validator;
#[cfg(feature = "z3-solver")]
pub mod wasm_semantics;

pub use properties::CompilerProperties;
#[cfg(feature = "z3-solver")]
pub use translation_validator::{TranslationValidator, ValidationResult, VerificationError};
#[cfg(feature = "z3-solver")]
pub use arm_semantics::{ArmSemantics, ArmState};
#[cfg(feature = "z3-solver")]
pub use wasm_semantics::WasmSemantics;

#[cfg(feature = "z3-solver")]
use z3::{Config, Context, Solver};

/// Create a Z3 context for verification
#[cfg(feature = "z3-solver")]
pub fn create_z3_context() -> Context {
    let mut cfg = Config::new();
    cfg.set_timeout_msec(30000); // 30 second timeout
    cfg.set_model_generation(true);
    Context::new(&cfg)
}

/// Create a Z3 solver with default configuration
#[cfg(feature = "z3-solver")]
pub fn create_solver(ctx: &Context) -> Solver<'_> {
    Solver::new(ctx)
}

#[cfg(all(test, feature = "z3-solver"))]
mod tests {
    use super::*;

    #[test]
    fn test_z3_context_creation() {
        let ctx = create_z3_context();
        let solver = create_solver(&ctx);
        assert_eq!(solver.check(), z3::SatResult::Sat);
    }
}
