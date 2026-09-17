//! Portable Memory Management for Synth
//!
//! This crate provides a platform-abstracted memory management layer that works across:
//! - Bare metal (direct MPU access)
//! - Zephyr RTOS (Memory Domains)
//! - FreeRTOS (MPU API)
//!
//! It supports the WebAssembly multi-memory proposal with up to 8 memories per module.

#![cfg_attr(not(feature = "std"), no_std)]

// #1279: without `std` the crate still needs `Vec` (bounds.rs), which lives in
// `alloc`. Before this line `--no-default-features` failed with six
// "cannot find type `Vec`" errors, and no CI job built that configuration.
#[cfg(not(feature = "std"))]
extern crate alloc;

pub mod bounds;
pub mod descriptor;
pub mod table;

#[cfg(feature = "std")]
pub mod platform;

#[cfg(feature = "std")]
pub mod space;

pub use bounds::{
    BoundsChecker, MaskingBoundsChecker, ProvenSafeBoundsChecker, ProvenSafeSites,
    SoftwareBoundsChecker,
};
pub use descriptor::{MemoryDescriptor, MemoryFlags, ProtectionStrategy};
pub use table::{MAX_MEMORIES, MemoryTable};

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
