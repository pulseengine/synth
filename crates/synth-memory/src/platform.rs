//! Platform Abstraction Layer (PAL)
//!
//! This module provides platform-specific memory operations.
//! It's only available with the "std" feature for now.

use crate::{AllocError, MpuError};

/// MPU access permissions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MpuAccess {
    /// No access (triggers fault)
    NoAccess,
    /// Read-only access
    ReadOnly,
    /// Read-write access
    ReadWrite,
    /// Read-execute access
    ReadExecute,
}

/// What to do on memory fault
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaultAction {
    /// Convert to WASM trap
    Trap(crate::Trap),
    /// Continue execution (for debugging)
    Continue,
    /// Panic (unrecoverable)
    Panic,
}

/// Platform-specific memory operations
pub trait MemoryPlatform {
    /// Allocate memory region with specified alignment
    fn allocate(&mut self, size: u32, align: u32) -> Result<*mut u8, AllocError>;

    /// Free memory region
    fn deallocate(&mut self, ptr: *mut u8, size: u32);

    /// Configure MPU region (if available)
    fn configure_mpu_region(
        &mut self,
        region_id: u8,
        base: *const u8,
        size: u32,
        access: MpuAccess,
    ) -> Result<(), MpuError>;

    /// Disable MPU region
    fn disable_mpu_region(&mut self, region_id: u8);

    /// Get number of available MPU regions
    fn available_mpu_regions(&self) -> u8;

    /// Handle memory fault (for trap conversion)
    fn handle_fault(&mut self, addr: u32) -> FaultAction;
}

/// Simple host platform (for testing on desktop)
///
/// This uses standard allocation and provides no MPU support.
#[cfg(feature = "std")]
pub struct HostPlatform;

#[cfg(feature = "std")]
impl HostPlatform {
    pub fn new() -> Self {
        Self
    }
}

#[cfg(feature = "std")]
impl Default for HostPlatform {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(feature = "std")]
impl MemoryPlatform for HostPlatform {
    fn allocate(&mut self, size: u32, align: u32) -> Result<*mut u8, AllocError> {
        use std::alloc::{alloc, Layout};

        let layout = Layout::from_size_align(size as usize, align as usize)
            .map_err(|_| AllocError::InvalidAlignment)?;

        let ptr = unsafe { alloc(layout) };
        if ptr.is_null() {
            Err(AllocError::OutOfMemory)
        } else {
            Ok(ptr)
        }
    }

    fn deallocate(&mut self, ptr: *mut u8, size: u32) {
        use std::alloc::{dealloc, Layout};

        // Assume 8-byte alignment for deallocation
        let layout = Layout::from_size_align(size as usize, 8).unwrap();
        unsafe { dealloc(ptr, layout) };
    }

    fn configure_mpu_region(
        &mut self,
        _region_id: u8,
        _base: *const u8,
        _size: u32,
        _access: MpuAccess,
    ) -> Result<(), MpuError> {
        // No MPU on host
        Err(MpuError::NoRegionsAvailable)
    }

    fn disable_mpu_region(&mut self, _region_id: u8) {
        // No-op on host
    }

    fn available_mpu_regions(&self) -> u8 {
        0 // No MPU on host
    }

    fn handle_fault(&mut self, _addr: u32) -> FaultAction {
        FaultAction::Trap(crate::Trap::OutOfBounds)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_host_platform_allocate() {
        let mut platform = HostPlatform::new();

        let ptr = platform.allocate(4096, 16).unwrap();
        assert!(!ptr.is_null());
        assert_eq!(ptr as usize % 16, 0); // Aligned

        platform.deallocate(ptr, 4096);
    }

    #[test]
    fn test_host_platform_no_mpu() {
        let platform = HostPlatform::new();
        assert_eq!(platform.available_mpu_regions(), 0);
    }
}
