//! Memory Descriptor Types
//!
//! Defines the core data structures for describing WASM linear memories.

use bitflags::bitflags;

/// Memory protection strategy
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum ProtectionStrategy {
    /// No protection (trust WASM code) - fastest but unsafe
    None = 0,
    /// Software bounds check before each access (~25-40% overhead)
    Software = 1,
    /// Address masking for power-of-2 sizes (~5% overhead)
    Masking = 2,
    /// MPU guard regions (~0% overhead, uses hardware)
    Mpu { region_id: u8 } = 3,
}

impl Default for ProtectionStrategy {
    fn default() -> Self {
        ProtectionStrategy::Software
    }
}

bitflags! {
    /// Memory flags for special behaviors
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub struct MemoryFlags: u32 {
        /// Memory is shared between threads (requires atomics)
        const SHARED = 0b0000_0001;
        /// Memory persists across module reloads
        const PERSISTENT = 0b0000_0010;
        /// Memory is read-only after initialization
        const READONLY = 0b0000_0100;
        /// Memory is exported to host
        const EXPORTED = 0b0000_1000;
        /// Memory uses 64-bit addressing (memory64 proposal)
        const MEMORY64 = 0b0001_0000;
    }
}

impl Default for MemoryFlags {
    fn default() -> Self {
        MemoryFlags::empty()
    }
}

/// Single memory instance descriptor
///
/// This is the runtime representation of a WASM linear memory.
/// It's designed to be FFI-safe and can be placed in a fixed-size table.
#[repr(C)]
#[derive(Debug, Clone)]
pub struct MemoryDescriptor {
    /// Base address of this memory region
    pub base: *mut u8,
    /// Current size in bytes
    pub size: u32,
    /// Maximum size in bytes (for grow operations)
    pub max_size: u32,
    /// Current page count (size / WASM_PAGE_SIZE)
    pub pages: u32,
    /// Maximum pages (max_size / WASM_PAGE_SIZE)
    pub max_pages: u32,
    /// Protection strategy for this memory
    pub protection: ProtectionStrategy,
    /// Memory flags
    pub flags: MemoryFlags,
    /// Platform-specific data (MPU region ID, Zephyr partition ptr, etc.)
    pub platform_data: usize,
}

impl MemoryDescriptor {
    /// Create a new uninitialized memory descriptor
    pub const fn uninit() -> Self {
        Self {
            base: core::ptr::null_mut(),
            size: 0,
            max_size: 0,
            pages: 0,
            max_pages: 0,
            protection: ProtectionStrategy::None,
            flags: MemoryFlags::empty(),
            platform_data: 0,
        }
    }

    /// Create a new memory descriptor with the given parameters
    pub fn new(
        base: *mut u8,
        initial_pages: u32,
        max_pages: Option<u32>,
        protection: ProtectionStrategy,
        flags: MemoryFlags,
    ) -> Self {
        let size = initial_pages * crate::WASM_PAGE_SIZE;
        let max_pages = max_pages.unwrap_or(initial_pages);
        let max_size = max_pages * crate::WASM_PAGE_SIZE;

        Self {
            base,
            size,
            max_size,
            pages: initial_pages,
            max_pages,
            protection,
            flags,
            platform_data: 0,
        }
    }

    /// Check if this memory is initialized
    pub fn is_initialized(&self) -> bool {
        !self.base.is_null()
    }

    /// Check if address is within bounds
    #[inline]
    pub fn contains(&self, addr: u32, len: u32) -> bool {
        addr.checked_add(len)
            .map(|end| end <= self.size)
            .unwrap_or(false)
    }

    /// Get a pointer to an address within this memory (unchecked)
    ///
    /// # Safety
    /// Caller must ensure addr + len <= size
    #[inline]
    pub unsafe fn ptr_at(&self, addr: u32) -> *mut u8 {
        self.base.add(addr as usize)
    }

    /// Grow memory by delta pages
    ///
    /// Returns the previous page count on success, or None if growth would exceed max.
    pub fn grow(&mut self, delta: u32) -> Option<u32> {
        let new_pages = self.pages.checked_add(delta)?;
        if new_pages > self.max_pages {
            return None;
        }

        let old_pages = self.pages;
        self.pages = new_pages;
        self.size = new_pages * crate::WASM_PAGE_SIZE;
        Some(old_pages)
    }
}

// Safety: MemoryDescriptor can be sent between threads if the underlying
// memory is either thread-local or properly synchronized
unsafe impl Send for MemoryDescriptor {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_memory_descriptor_uninit() {
        let desc = MemoryDescriptor::uninit();
        assert!(!desc.is_initialized());
        assert_eq!(desc.size, 0);
    }

    #[test]
    fn test_memory_descriptor_new() {
        let mut buffer = [0u8; 65536];
        let desc = MemoryDescriptor::new(
            buffer.as_mut_ptr(),
            1,
            Some(4),
            ProtectionStrategy::Software,
            MemoryFlags::empty(),
        );

        assert!(desc.is_initialized());
        assert_eq!(desc.pages, 1);
        assert_eq!(desc.max_pages, 4);
        assert_eq!(desc.size, 65536);
        assert_eq!(desc.max_size, 65536 * 4);
    }

    #[test]
    fn test_memory_bounds_check() {
        let mut buffer = [0u8; 65536];
        let desc = MemoryDescriptor::new(
            buffer.as_mut_ptr(),
            1,
            None,
            ProtectionStrategy::Software,
            MemoryFlags::empty(),
        );

        // Within bounds
        assert!(desc.contains(0, 100));
        assert!(desc.contains(65532, 4));

        // Out of bounds
        assert!(!desc.contains(65533, 4));
        assert!(!desc.contains(65536, 1));
        assert!(!desc.contains(u32::MAX, 1));
    }

    #[test]
    fn test_memory_grow() {
        let mut buffer = [0u8; 65536 * 4];
        let mut desc = MemoryDescriptor::new(
            buffer.as_mut_ptr(),
            1,
            Some(4),
            ProtectionStrategy::Software,
            MemoryFlags::empty(),
        );

        // Grow by 2 pages
        let old = desc.grow(2);
        assert_eq!(old, Some(1));
        assert_eq!(desc.pages, 3);
        assert_eq!(desc.size, 65536 * 3);

        // Grow by 1 more (at max)
        let old = desc.grow(1);
        assert_eq!(old, Some(3));
        assert_eq!(desc.pages, 4);

        // Try to grow past max
        let old = desc.grow(1);
        assert_eq!(old, None);
        assert_eq!(desc.pages, 4); // Unchanged
    }
}
