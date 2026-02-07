//! Bounds Checking Strategies
//!
//! Provides pluggable bounds checking for memory access safety.

use crate::{MemoryDescriptor, Trap};

/// Bounds checking strategy trait
///
/// Implementors provide different strategies for validating memory accesses.
pub trait BoundsChecker {
    /// Check if address + size is within memory bounds
    ///
    /// Returns the (possibly adjusted) address on success, or a trap on failure.
    fn check(&self, memory: &MemoryDescriptor, addr: u32, size: u32) -> Result<u32, Trap>;

    /// Get the overhead category for this checker
    fn overhead(&self) -> BoundsCheckOverhead;
}

/// Overhead category for bounds checking
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoundsCheckOverhead {
    /// No overhead (unsafe or hardware-protected)
    Zero,
    /// Low overhead (~5%, e.g., address masking)
    Low,
    /// Medium overhead (~25%, e.g., software check with branch)
    Medium,
    /// High overhead (~40%, e.g., software check with call)
    High,
}

/// Software bounds checking (portable, ~25-40% overhead)
///
/// Performs an explicit comparison before each memory access.
/// This is the safest portable option.
#[derive(Debug, Clone, Copy, Default)]
pub struct SoftwareBoundsChecker;

impl BoundsChecker for SoftwareBoundsChecker {
    #[inline]
    fn check(&self, memory: &MemoryDescriptor, addr: u32, size: u32) -> Result<u32, Trap> {
        let end = addr.checked_add(size).ok_or(Trap::OutOfBounds)?;
        if end > memory.size {
            return Err(Trap::OutOfBounds);
        }
        Ok(addr)
    }

    fn overhead(&self) -> BoundsCheckOverhead {
        BoundsCheckOverhead::Medium
    }
}

/// Address masking for power-of-2 memories (~5% overhead)
///
/// Instead of checking bounds, mask the address to always be in range.
/// This only works when memory size is a power of 2.
///
/// **Warning**: This wraps out-of-bounds accesses instead of trapping!
/// Use only when security is less important than performance.
#[derive(Debug, Clone, Copy)]
pub struct MaskingBoundsChecker {
    /// Mask value (size - 1, e.g., 0xFFFF for 64KB)
    pub mask: u32,
}

impl MaskingBoundsChecker {
    /// Create a new masking bounds checker for a given size
    ///
    /// # Panics
    /// Panics if size is not a power of 2
    pub fn new(size: u32) -> Self {
        assert!(size.is_power_of_two(), "Size must be power of 2 for masking");
        Self { mask: size - 1 }
    }

    /// Try to create a masking bounds checker
    ///
    /// Returns None if size is not a power of 2
    pub fn try_new(size: u32) -> Option<Self> {
        if size.is_power_of_two() {
            Some(Self { mask: size - 1 })
        } else {
            None
        }
    }
}

impl BoundsChecker for MaskingBoundsChecker {
    #[inline]
    fn check(&self, _memory: &MemoryDescriptor, addr: u32, _size: u32) -> Result<u32, Trap> {
        // Masking always "succeeds" by wrapping the address
        Ok(addr & self.mask)
    }

    fn overhead(&self) -> BoundsCheckOverhead {
        BoundsCheckOverhead::Low
    }
}

/// No bounds checking (unsafe, ~0% overhead)
///
/// **Warning**: This provides no safety! Use only for:
/// - Trusted WASM modules
/// - When MPU provides hardware protection
/// - Performance testing
#[derive(Debug, Clone, Copy, Default)]
pub struct NoBoundsChecker;

impl BoundsChecker for NoBoundsChecker {
    #[inline]
    fn check(&self, _memory: &MemoryDescriptor, addr: u32, _size: u32) -> Result<u32, Trap> {
        Ok(addr)
    }

    fn overhead(&self) -> BoundsCheckOverhead {
        BoundsCheckOverhead::Zero
    }
}

/// MPU-based bounds checking stub
///
/// The actual MPU configuration happens at memory initialization time.
/// At runtime, we rely on hardware faults for out-of-bounds access.
/// This checker is just a marker that MPU is in use.
#[derive(Debug, Clone, Copy)]
pub struct MpuBoundsChecker {
    /// The MPU region ID protecting this memory
    pub region_id: u8,
}

impl MpuBoundsChecker {
    pub fn new(region_id: u8) -> Self {
        Self { region_id }
    }
}

impl BoundsChecker for MpuBoundsChecker {
    #[inline]
    fn check(&self, _memory: &MemoryDescriptor, addr: u32, _size: u32) -> Result<u32, Trap> {
        // No software check - MPU handles it
        // Out-of-bounds access will trigger HardFault which we convert to trap
        Ok(addr)
    }

    fn overhead(&self) -> BoundsCheckOverhead {
        BoundsCheckOverhead::Zero
    }
}

/// Code generation helpers for bounds checking
///
/// These functions generate ARM Thumb-2 instruction sequences for inline bounds checking.
pub mod codegen {
    /// Generate software bounds check instructions
    ///
    /// Generates: CMP Raddr, Rsize; BHS trap
    ///
    /// Returns (instructions, size_in_bytes)
    pub fn generate_software_check(addr_reg: u8, size_reg: u8, trap_label: u32) -> (Vec<u8>, usize) {
        let mut bytes = Vec::with_capacity(8);

        // CMP Raddr, Rsize (Thumb-2: compare registers)
        // Encoding: 0100 0010 10 Rm Rn => 0x4280 | (rm << 3) | rn
        let cmp = 0x4280u16 | ((size_reg as u16) << 3) | (addr_reg as u16);
        bytes.extend_from_slice(&cmp.to_le_bytes());

        // BHS (branch if higher or same, unsigned >=) to trap
        // Thumb-2: 0xD2xx where xx is signed offset/2
        // For now, we'll use a placeholder - actual offset depends on trap handler location
        let bhs = 0xD200u16 | ((trap_label as u16) & 0xFF);
        bytes.extend_from_slice(&bhs.to_le_bytes());

        (bytes, 4)
    }

    /// Generate address masking instruction
    ///
    /// Generates: AND Raddr, Raddr, #mask
    ///
    /// Returns (instructions, size_in_bytes)
    pub fn generate_masking(addr_reg: u8, mask: u32) -> (Vec<u8>, usize) {
        let mut bytes = Vec::with_capacity(4);

        // For masks that fit in Thumb-2 modified immediate:
        // AND Rd, Rn, #imm - Thumb-2 32-bit encoding
        // This is complex; for now, assume mask is loaded in a register

        // Simple version: AND Rd, Rm (Thumb-1)
        // This assumes mask is in a register. For real implementation,
        // we'd need to handle the full Thumb-2 immediate encoding.

        // Placeholder: BIC (bit clear) or AND immediate
        // For 64KB (0xFFFF mask), we can use: UXTH Rd, Rd (zero-extend halfword)
        if mask == 0xFFFF {
            // UXTH Rd, Rm: 1011 0010 10 Rm Rd
            let uxth = 0xB280u16 | ((addr_reg as u16) << 3) | (addr_reg as u16);
            bytes.extend_from_slice(&uxth.to_le_bytes());
            return (bytes, 2);
        }

        // Generic case: need full Thumb-2 AND immediate
        // For now, return empty (caller should use register-based masking)
        (bytes, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_test_descriptor(size: u32) -> MemoryDescriptor {
        MemoryDescriptor {
            base: core::ptr::null_mut(),
            size,
            max_size: size,
            pages: size / 65536,
            max_pages: size / 65536,
            protection: crate::ProtectionStrategy::Software,
            flags: crate::MemoryFlags::empty(),
            platform_data: 0,
        }
    }

    #[test]
    fn test_software_bounds_checker() {
        let checker = SoftwareBoundsChecker;
        let mem = make_test_descriptor(65536);

        // Valid access
        assert_eq!(checker.check(&mem, 0, 4), Ok(0));
        assert_eq!(checker.check(&mem, 65532, 4), Ok(65532));

        // Invalid access
        assert_eq!(checker.check(&mem, 65533, 4), Err(Trap::OutOfBounds));
        assert_eq!(checker.check(&mem, 65536, 1), Err(Trap::OutOfBounds));

        // Overflow check
        assert_eq!(checker.check(&mem, u32::MAX, 1), Err(Trap::OutOfBounds));
    }

    #[test]
    fn test_masking_bounds_checker() {
        let checker = MaskingBoundsChecker::new(65536);
        let mem = make_test_descriptor(65536);

        // Valid access - returns as-is
        assert_eq!(checker.check(&mem, 0, 4), Ok(0));
        assert_eq!(checker.check(&mem, 65532, 4), Ok(65532));

        // "Invalid" access - wraps around
        assert_eq!(checker.check(&mem, 65536, 4), Ok(0)); // Wraps to 0
        assert_eq!(checker.check(&mem, 65537, 4), Ok(1)); // Wraps to 1
        assert_eq!(checker.check(&mem, 0x20000, 4), Ok(0)); // Wraps to 0
    }

    #[test]
    fn test_masking_checker_requires_power_of_2() {
        assert!(MaskingBoundsChecker::try_new(65536).is_some());
        assert!(MaskingBoundsChecker::try_new(65535).is_none());
        assert!(MaskingBoundsChecker::try_new(100).is_none());
    }

    #[test]
    fn test_no_bounds_checker() {
        let checker = NoBoundsChecker;
        let mem = make_test_descriptor(65536);

        // Always returns the address unchanged
        assert_eq!(checker.check(&mem, 0, 4), Ok(0));
        assert_eq!(checker.check(&mem, u32::MAX, 1), Ok(u32::MAX));
    }
}
