//! Portable Memory Management for Synth
//!
//! This crate provides a platform-abstracted memory management layer that works across:
//! - Bare metal (direct MPU access)
//! - Zephyr RTOS (Memory Domains)
//! - FreeRTOS (MPU API)
//!
//! It supports the WebAssembly multi-memory proposal with up to 8 memories per module.

#![cfg_attr(not(feature = "std"), no_std)]

pub mod bounds;
pub mod descriptor;
pub mod table;

#[cfg(feature = "std")]
pub mod platform;

pub use bounds::{BoundsChecker, MaskingBoundsChecker, SoftwareBoundsChecker};
pub use descriptor::{MemoryDescriptor, MemoryFlags, ProtectionStrategy};
pub use table::{MemoryTable, MAX_MEMORIES};

/// WASM page size (64KB)
pub const WASM_PAGE_SIZE: u32 = 65536;

/// Memory trap error
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Trap {
    /// Memory access out of bounds
    OutOfBounds,
    /// Null pointer dereference
    NullPointer,
    /// Alignment fault
    Alignment,
    /// Memory not initialized
    Uninitialized,
}

/// Memory allocation error
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocError {
    /// Out of memory
    OutOfMemory,
    /// Invalid alignment
    InvalidAlignment,
    /// Size too large
    SizeTooLarge,
}

/// MPU configuration error
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MpuError {
    /// No more regions available
    NoRegionsAvailable,
    /// Invalid region size (must be power of 2)
    InvalidSize,
    /// Invalid alignment (must match size)
    InvalidAlignment,
    /// Configuration failed
    ConfigurationFailed,
}
