//! Synth Backend - Code generation and binary emission

pub mod arm_startup;
pub mod memory_layout;
pub mod mpu;
pub mod mpu_allocator;

pub use arm_startup::ARMStartupGenerator;
pub use memory_layout::{MemoryLayout, MemoryLayoutAnalyzer, MemorySection, SectionType};
pub use mpu::{MPUAttributes, MPUPermissions, MPURegion, MPUSize};
pub use mpu_allocator::{MPUAllocationRequest, MPUAllocator};

// Stub for PoC
pub struct CodeGenerator;
