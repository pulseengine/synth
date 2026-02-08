//! Synth Backend - Code generation and binary emission
//!
//! Generic scaffolding (ELF builder, linker scripts, memory layout) is always
//! available. ARM-specific modules are behind the `arm-cortex-m` feature.

// === Always available (generic embedded scaffolding) ===
pub mod elf_builder;
pub mod linker_script;
pub mod memory_layout;
pub mod mpu;
pub mod mpu_allocator;
pub mod w2c2_wrapper;

pub use elf_builder::{
    ElfBuilder, ElfClass, ElfData, ElfMachine, ElfType, ProgramFlags, ProgramHeader, ProgramType,
    Section, SectionFlags, SectionType as ElfSectionType, Symbol, SymbolBinding, SymbolType,
};
pub use linker_script::{LinkerScriptGenerator, MemoryRegion};
pub use memory_layout::{MemoryLayout, MemoryLayoutAnalyzer, MemorySection, SectionType};
pub use mpu::{MPUAttributes, MPUPermissions, MPURegion, MPUSize};
pub use mpu_allocator::{MPUAllocationRequest, MPUAllocator};
pub use w2c2_wrapper::{TranspileOptions, TranspileResult, W2C2Backend, W2C2Transpiler};

// === ARM Cortex-M specific (behind feature gate) ===
#[cfg(feature = "arm-cortex-m")]
pub mod arm_backend;
#[cfg(feature = "arm-cortex-m")]
pub mod arm_encoder;
#[cfg(feature = "arm-cortex-m")]
pub mod arm_startup;
#[cfg(feature = "arm-cortex-m")]
pub mod cortex_m;
#[cfg(feature = "arm-cortex-m")]
pub mod reset_handler;
#[cfg(feature = "arm-cortex-m")]
pub mod vector_table;

#[cfg(feature = "arm-cortex-m")]
pub use arm_backend::ArmBackend;
#[cfg(feature = "arm-cortex-m")]
pub use arm_encoder::ArmEncoder;
#[cfg(feature = "arm-cortex-m")]
pub use arm_startup::ARMStartupGenerator;
#[cfg(feature = "arm-cortex-m")]
pub use reset_handler::ResetHandlerGenerator;
#[cfg(feature = "arm-cortex-m")]
pub use vector_table::{VectorEntry, VectorTable};
