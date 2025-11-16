//! Synth Synthesis - Code synthesis engine

pub mod rules;

pub use rules::{
    ArmOp, Cost, MemAddr, Operand2, Pattern, Reg, Replacement, RuleDatabase, ShiftType,
    SynthesisRule, WasmOp,
};

// Stub for PoC
pub struct SynthesisEngine;
