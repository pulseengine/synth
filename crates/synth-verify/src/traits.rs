//! Verification traits for backend-agnostic translation validation
//!
//! These traits allow any backend to provide SMT semantics for its target
//! instruction set. The translation validator is generic over source and
//! target semantics.
//!
//! Z3 0.19 uses thread-local context — no lifetime parameters needed.

use z3::ast::BV;

/// Encodes source (WASM) operation semantics as SMT formulas
pub trait SourceSemantics {
    /// Encode a source operation, returning the result as a bitvector
    fn encode_op(&self, op_name: &str, inputs: &[BV]) -> Option<BV>;
}

/// Encodes target (ARM, RISC-V, etc.) operation semantics as SMT formulas
pub trait TargetSemantics {
    /// The target state type (registers, flags, memory)
    type State;

    /// Create a fresh symbolic state
    fn fresh_state(&self) -> Self::State;

    /// Apply a target operation to the state, returning updated state
    fn apply_op(&self, state: &Self::State, op_name: &str, inputs: &[BV]) -> Option<Self::State>;

    /// Extract the result bitvector from a state (e.g. read Rd register)
    fn extract_result(&self, state: &Self::State, result_loc: &str) -> Option<BV>;
}
