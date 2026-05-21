//! Validator-Pattern Verification (Issue #76)
//!
//! This module implements the **certifying-algorithm** verification pattern
//! that CompCert uses for NP-hard passes (register allocation, instruction
//! scheduling). Rather than verifying the *selector* — which is heuristic,
//! large, and changes frequently — we verify a small *validator* that
//! consumes the selector's output and confirms each concrete selection is
//! semantically equivalent to the WASM op it replaces.
//!
//! See `docs/validator-pattern.md` for the architecture rationale.
//!
//! # Status
//!
//! This is the **prototype scaffolding** landed by issue #76. It defines:
//!
//! - [`CertifiedSelection`] — the per-op output of the selector
//! - [`Validator`] — the trait the validator implements
//! - [`Z3ArmValidator`] — a Z3-backed validator. The prototype only handles
//!   `WasmOp::I32Add` (mapped to `ArmOp::Add`). Subsequent PRs extend the
//!   coverage matrix per the migration plan in the design doc.
//!
//! # Worked example: `I32Add`
//!
//! WASM `i32.add` is a 32-bit bitvector add. The selector emits
//! `ADD Rd, Rn, op2` where `op2` is also a register. Z3 trivially proves
//! `bvadd(R0, R1) ≡ wasm_add(R0, R1)`.
//!
//! If the selector is buggy and emits `SUB` instead, Z3 returns a
//! counterexample (e.g. `R0 = 5, R1 = 3, wasm = 8, arm = 2`).

#![cfg(all(feature = "z3-solver", feature = "arm"))]

use crate::arm_semantics::{ArmSemantics, ArmState};
use crate::wasm_semantics::WasmSemantics;
use synth_core::WasmOp;
use synth_synthesis::{ArmOp, Reg};
use thiserror::Error;
use z3::ast::BV;
use z3::{SatResult, Solver};

/// A concrete selection produced by the instruction selector.
///
/// Generic over the source op `W` (initially `WasmOp`) and target op `A`
/// (initially `ArmOp`, later `RiscvOp`). The `witness` is `None` when the
/// selector emits the selection and `Some(Witness)` after the validator
/// accepts it.
#[derive(Debug, Clone)]
pub struct CertifiedSelection<W, A> {
    /// The source operation (e.g. `WasmOp::I32Add`).
    pub wasm: W,
    /// The target instruction sequence (e.g. `[ArmOp::Add { ... }]`).
    pub arm: Vec<A>,
    /// Witness attached by the validator (`None` until validated).
    pub witness: Option<Witness>,
}

impl<W, A> CertifiedSelection<W, A> {
    /// Create a new selection with no witness attached.
    pub fn new(wasm: W, arm: Vec<A>) -> Self {
        Self {
            wasm,
            arm,
            witness: None,
        }
    }

    /// Attach a witness, marking this selection as validated.
    pub fn with_witness(mut self, witness: Witness) -> Self {
        self.witness = Some(witness);
        self
    }

    /// Whether this selection has been validated.
    pub fn is_certified(&self) -> bool {
        self.witness.is_some()
    }
}

/// A witness recording the validator's acceptance of a selection.
///
/// For the prototype this is intentionally minimal. A v0.5 expansion will
/// embed the SMT-LIB2 script that Z3 was given, so a third party can
/// independently replay the verification without trusting the validator's
/// encoding logic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Witness {
    /// Human-readable label for the WASM op (e.g. `"I32Add"`).
    pub wasm_op_label: String,
    /// Number of ARM instructions in the validated sequence.
    pub arm_op_count: usize,
    /// The Z3 result that produced this witness (always `Unsat` for accepted
    /// selections — `Unsat` of `wasm ≠ arm` means `wasm ≡ arm`).
    pub solver_result: SolverResultKind,
}

/// Solver result kind (mirrors `z3::SatResult` but without the lifetime).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SolverResultKind {
    /// `Unsat` of the negated equivalence — selection is correct.
    Unsat,
    /// `Sat` of the negated equivalence — counterexample found.
    Sat,
    /// Solver returned `unknown` (timeout or unsupported theory).
    Unknown,
}

/// Validation failure reasons.
#[derive(Debug, Error)]
pub enum ValidationError {
    /// The selection is semantically wrong; the validator found a
    /// counterexample (a concrete input where WASM and ARM disagree).
    #[error("counterexample for {wasm_op_label}: {description}")]
    Counterexample {
        wasm_op_label: String,
        description: String,
    },

    /// The validator does not yet support this WASM op. This is the common
    /// case during the per-op rollout (see `docs/validator-pattern.md`).
    #[error("validator does not yet support {0:?}")]
    UnsupportedOp(WasmOp),

    /// Z3 returned `unknown` (timeout or unsupported theory).
    #[error("solver returned unknown: {0}")]
    SolverUnknown(String),

    /// Internal encoding error (e.g. too many inputs for the ARM model).
    #[error("internal validator error: {0}")]
    Internal(String),
}

/// A backend-agnostic validator for [`CertifiedSelection`].
///
/// Implementations consume a selection and either return a [`Witness`]
/// (selection is correct) or a [`ValidationError`] (selection is wrong, or
/// unsupported, or inconclusive).
pub trait Validator<W, A> {
    /// Validate `sel`. Returns `Ok(Witness)` iff the selection is
    /// semantically equivalent to the source op.
    fn validate(&self, sel: &CertifiedSelection<W, A>) -> Result<Witness, ValidationError>;
}

/// Z3-backed validator for the WASM → ARM selection pattern.
///
/// Wraps the existing [`WasmSemantics`] and [`ArmSemantics`] encoders in
/// `synth-verify`, treating a concrete selection as the verification subject
/// (rather than a `SynthesisRule` pattern). For each call the validator:
///
/// 1. Allocates symbolic 32-bit inputs.
/// 2. Encodes the WASM op into a Z3 expression.
/// 3. Encodes the ARM sequence by stepping the ARM state machine.
/// 4. Asserts the *negation* of equivalence and checks satisfiability:
///    `unsat` ⇒ equivalent for all inputs (accept), `sat` ⇒ counterexample
///    (reject).
pub struct Z3ArmValidator {
    wasm_encoder: WasmSemantics,
    arm_encoder: ArmSemantics,
}

impl Default for Z3ArmValidator {
    fn default() -> Self {
        Self::new()
    }
}

impl Z3ArmValidator {
    /// Construct a fresh validator. Z3 0.19 uses thread-local contexts, so
    /// callers should wrap any sequence of `validate` calls in
    /// `crate::with_z3_context`.
    pub fn new() -> Self {
        Self {
            wasm_encoder: WasmSemantics::new(),
            arm_encoder: ArmSemantics::new(),
        }
    }

    /// Per-op support gate. Returns `Ok(())` if this op is in the prototype's
    /// supported set, `Err(UnsupportedOp)` otherwise.
    ///
    /// The prototype only supports `I32Add`. Subsequent PRs extend this set
    /// per the migration plan in `docs/validator-pattern.md`.
    fn check_supported(&self, op: &WasmOp) -> Result<(), ValidationError> {
        match op {
            WasmOp::I32Add => Ok(()),
            other => Err(ValidationError::UnsupportedOp(other.clone())),
        }
    }

    /// Number of 32-bit inputs a WASM op consumes from the stack.
    ///
    /// Mirrors `TranslationValidator::get_num_inputs` for the ops the
    /// prototype supports; extend as new ops are added.
    fn num_inputs(&self, op: &WasmOp) -> usize {
        match op {
            WasmOp::I32Add => 2,
            _ => 0,
        }
    }

    /// Encode an ARM sequence on top of symbolic input registers, returning
    /// the symbolic value of R0 after execution (the ARM result register).
    fn encode_arm_sequence(&self, arm_ops: &[ArmOp], inputs: &[BV]) -> Result<BV, ValidationError> {
        let mut state = ArmState::new_symbolic();

        for (i, input) in inputs.iter().enumerate() {
            let reg = match i {
                0 => Reg::R0,
                1 => Reg::R1,
                2 => Reg::R2,
                _ => {
                    return Err(ValidationError::Internal(format!(
                        "too many inputs: {}",
                        inputs.len()
                    )));
                }
            };
            state.set_reg(&reg, input.clone());
        }

        for arm_op in arm_ops {
            self.arm_encoder.encode_op(arm_op, &mut state);
        }

        Ok(self.arm_encoder.extract_result(&state, &Reg::R0))
    }
}

impl Validator<WasmOp, ArmOp> for Z3ArmValidator {
    fn validate(
        &self,
        sel: &CertifiedSelection<WasmOp, ArmOp>,
    ) -> Result<Witness, ValidationError> {
        self.check_supported(&sel.wasm)?;

        let solver = Solver::new();
        let n = self.num_inputs(&sel.wasm);

        let inputs: Vec<BV> = (0..n)
            .map(|i| BV::new_const(format!("input_{}", i), 32))
            .collect();

        let wasm_result = self.wasm_encoder.encode_op(&sel.wasm, &inputs);
        let arm_result = self.encode_arm_sequence(&sel.arm, &inputs)?;

        // Assert ¬(wasm == arm); unsat ⇒ equivalent for all inputs.
        solver.assert(wasm_result.eq(&arm_result).not());

        let label = format!("{:?}", sel.wasm);
        match solver.check() {
            SatResult::Unsat => Ok(Witness {
                wasm_op_label: label,
                arm_op_count: sel.arm.len(),
                solver_result: SolverResultKind::Unsat,
            }),
            SatResult::Sat => {
                let description = match solver.get_model() {
                    Some(model) => inputs
                        .iter()
                        .enumerate()
                        .filter_map(|(i, bv)| {
                            model
                                .eval(bv, true)
                                .and_then(|v| v.as_i64())
                                .map(|v| format!("input_{}={}", i, v))
                        })
                        .collect::<Vec<_>>()
                        .join(", "),
                    None => "no model available".to_string(),
                };
                Err(ValidationError::Counterexample {
                    wasm_op_label: label,
                    description,
                })
            }
            SatResult::Unknown => Err(ValidationError::SolverUnknown(label)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::with_z3_context;
    use synth_synthesis::Operand2;

    /// The headline test: with a correct selector picking `ADD`, the
    /// validator accepts; with a deliberately wrong selector picking `SUB`,
    /// the validator rejects with a counterexample.
    ///
    /// This is the working example that the PR is built around. Extending
    /// coverage to other ops is the v0.5 milestone described in
    /// `docs/validator-pattern.md`.
    #[test]
    fn i32_add_certifies() {
        with_z3_context(|| {
            let validator = Z3ArmValidator::new();

            // --- Correct selection: I32Add → ADD R0, R0, R1 ---
            let correct = CertifiedSelection::new(
                WasmOp::I32Add,
                vec![ArmOp::Add {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                }],
            );
            let witness = validator
                .validate(&correct)
                .expect("validator must accept I32Add → ADD");
            assert_eq!(witness.wasm_op_label, "I32Add");
            assert_eq!(witness.arm_op_count, 1);
            assert_eq!(witness.solver_result, SolverResultKind::Unsat);

            // --- Wrong selection: I32Add → SUB R0, R0, R1 ---
            let wrong = CertifiedSelection::new(
                WasmOp::I32Add,
                vec![ArmOp::Sub {
                    rd: Reg::R0,
                    rn: Reg::R0,
                    op2: Operand2::Reg(Reg::R1),
                }],
            );
            match validator.validate(&wrong) {
                Err(ValidationError::Counterexample { wasm_op_label, .. }) => {
                    assert_eq!(wasm_op_label, "I32Add");
                }
                other => panic!("expected Counterexample for SUB, got {:?}", other),
            }
        });
    }

    /// Smoke test: unsupported ops return `UnsupportedOp`, not a panic.
    ///
    /// This guards the prototype-rollout invariant: ops outside the
    /// supported set must produce a structured error so the caller (the
    /// `synth compile --verify` driver) can decide whether to fall back
    /// to the existing Rocq-based confidence story.
    #[test]
    fn unsupported_op_returns_structured_error() {
        with_z3_context(|| {
            let validator = Z3ArmValidator::new();
            let sel = CertifiedSelection::<WasmOp, ArmOp>::new(WasmOp::I32Sub, vec![]);
            match validator.validate(&sel) {
                Err(ValidationError::UnsupportedOp(op)) => assert_eq!(op, WasmOp::I32Sub),
                other => panic!("expected UnsupportedOp, got {:?}", other),
            }
        });
    }

    /// CertifiedSelection plumbing test: witnesses round-trip through
    /// `with_witness` / `is_certified` without losing information.
    #[test]
    fn certified_selection_witness_roundtrip() {
        let sel = CertifiedSelection::<WasmOp, ArmOp>::new(
            WasmOp::I32Add,
            vec![ArmOp::Add {
                rd: Reg::R0,
                rn: Reg::R0,
                op2: Operand2::Reg(Reg::R1),
            }],
        );
        assert!(!sel.is_certified());
        let witness = Witness {
            wasm_op_label: "I32Add".to_string(),
            arm_op_count: 1,
            solver_result: SolverResultKind::Unsat,
        };
        let certified = sel.with_witness(witness.clone());
        assert!(certified.is_certified());
        assert_eq!(certified.witness, Some(witness));
    }
}
