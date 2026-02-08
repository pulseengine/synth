//! Synth Synthesis - Code synthesis engine

pub mod control_flow;
pub mod instruction_selector;
pub mod optimizer_bridge;
pub mod pattern_matcher;
pub mod peephole;
pub mod rules;
pub mod wasm_decoder;

pub use instruction_selector::{
    ArmInstruction, BoundsCheckConfig, InstructionSelector, RegisterState, SelectionStats,
};
pub use optimizer_bridge::{OptimizationConfig, OptimizationStats, OptimizerBridge};
pub use pattern_matcher::{
    ApplyStats, Bindings, MatchResult, MatchValue, PatternMatcher, RuleApplicator,
};
pub use peephole::{OptimizationStats as PeepholeStats, PeepholeOptimizer};
pub use rules::{
    ArmOp, Condition, Cost, MemAddr, Operand2, Pattern, Reg, Replacement, RuleDatabase, ShiftType,
    SynthesisRule, WasmOp,
};
pub use wasm_decoder::{
    decode_wasm_functions, decode_wasm_module, DecodedModule, FunctionOps, WasmMemory,
};

// Stub for PoC
pub struct SynthesisEngine;
