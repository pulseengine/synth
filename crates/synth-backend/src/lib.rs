//! Synth Backend - Code generation and binary emission

pub mod mpu;
pub mod mpu_allocator;
pub mod memory_layout;

pub use mpu::{MPUAttributes, MPUPermissions, MPURegion, MPUSize};
pub use mpu_allocator::{MPUAllocationRequest, MPUAllocator};
pub use memory_layout::{MemoryLayout, MemoryLayoutAnalyzer, MemorySection, SectionType};

// Stub for PoC
pub struct CodeGenerator;
