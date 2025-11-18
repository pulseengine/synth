//! Synth Synthesis - Code synthesis engine

pub mod instruction_selector;
pub mod optimizer_bridge;
pub mod pattern_matcher;
pub mod peephole;
pub mod rules;

pub use instruction_selector::{
    ArmInstruction, InstructionSelector, RegisterState, SelectionStats,
};
pub use optimizer_bridge::{OptimizationConfig, OptimizationStats, OptimizerBridge};
pub use pattern_matcher::{
    ApplyStats, Bindings, MatchResult, MatchValue, PatternMatcher, RuleApplicator,
};
pub use peephole::{OptimizationStats as PeepholeStats, PeepholeOptimizer};
pub use rules::{
    ArmOp, Condition, Cost, MemAddr, Operand2, Pattern, Reg, Replacement, RuleDatabase,
    ShiftType, SynthesisRule, WasmOp,
};

// Stub for PoC
pub struct SynthesisEngine;
