//! Synth Backend - Code generation and binary emission

pub mod arm_startup;
pub mod memory_layout;
pub mod mpu;
pub mod mpu_allocator;
pub mod w2c2_wrapper;

pub use arm_startup::ARMStartupGenerator;
pub use memory_layout::{MemoryLayout, MemoryLayoutAnalyzer, MemorySection, SectionType};
pub use mpu::{MPUAttributes, MPUPermissions, MPURegion, MPUSize};
pub use mpu_allocator::{MPUAllocationRequest, MPUAllocator};
pub use w2c2_wrapper::{TranspileOptions, TranspileResult, W2C2Transpiler};

// Stub for PoC
pub struct CodeGenerator;
