//! Synth Synthesis - Code synthesis engine

pub mod contracts;
pub mod control_flow;
pub mod instruction_selector;
pub mod optimizer_bridge;
pub mod pattern_matcher;
pub mod peephole;
pub mod rules;
pub mod wasm_decoder;

pub use control_flow::{
    BlockType, BranchableInstruction, ControlBlock, ControlFlowManager, Label, PendingBranch,
    resolve_branches,
};
pub use instruction_selector::{
    ArmInstruction, BoundsCheckConfig, InstructionSelector, RegisterState, SelectionStats,
    validate_instructions, validate_instructions_with_helium,
};
pub use optimizer_bridge::{OptimizationConfig, OptimizationStats, OptimizerBridge};
pub use pattern_matcher::{
    ApplyStats, Bindings, MatchResult, MatchValue, PatternMatcher, RuleApplicator,
};
pub use peephole::{OptimizationStats as PeepholeStats, PeepholeOptimizer};
pub use rules::{
    ArmOp, Condition, Cost, MemAddr, MveSize, Operand2, Pattern, QReg, Reg, Replacement,
    RuleDatabase, ShiftType, SynthesisRule, VfpReg, WasmOp,
};
pub use wasm_decoder::{
    DecodedModule, FunctionOps, WasmMemory, decode_wasm_functions, decode_wasm_module,
};

// Stub for PoC
pub struct SynthesisEngine;
