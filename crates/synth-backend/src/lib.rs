//! Synth Backend - Code generation and binary emission

pub mod arm_encoder;
pub mod arm_startup;
pub mod elf_builder;
pub mod memory_layout;
pub mod mpu;
pub mod mpu_allocator;
pub mod w2c2_wrapper;

pub use arm_encoder::ArmEncoder;
pub use arm_startup::ARMStartupGenerator;
pub use elf_builder::{
    ElfBuilder, ElfClass, ElfData, ElfMachine, ElfType, Section, SectionFlags,
    SectionType as ElfSectionType, Symbol, SymbolBinding, SymbolType,
};
pub use memory_layout::{MemoryLayout, MemoryLayoutAnalyzer, MemorySection, SectionType};
pub use mpu::{MPUAttributes, MPUPermissions, MPURegion, MPUSize};
pub use mpu_allocator::{MPUAllocationRequest, MPUAllocator};
pub use w2c2_wrapper::{TranspileOptions, TranspileResult, W2C2Transpiler};

// Stub for PoC
pub struct CodeGenerator;
