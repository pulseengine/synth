//! Synth Synthesis - Code synthesis engine

pub mod instruction_selector;
pub mod pattern_matcher;
pub mod rules;

pub use instruction_selector::{ArmInstruction, InstructionSelector, RegisterState, SelectionStats};
pub use pattern_matcher::{ApplyStats, Bindings, MatchResult, MatchValue, PatternMatcher, RuleApplicator};
pub use rules::{
    ArmOp, Cost, MemAddr, Operand2, Pattern, Reg, Replacement, RuleDatabase, ShiftType,
    SynthesisRule, WasmOp,
};

// Stub for PoC
pub struct SynthesisEngine;
