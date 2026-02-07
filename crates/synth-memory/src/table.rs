//! Memory Table
//!
//! Fixed-size table of memory descriptors for multi-memory support.

use crate::{MemoryDescriptor, Trap};

/// Maximum memories per module
///
/// The WASM spec allows unlimited memories, but we cap for embedded use.
/// 8 memories allows for common patterns:
/// - Memory 0: Main heap
/// - Memory 1: Shared IPC buffer
/// - Memory 2: Persistent state
/// - Memory 3-7: Additional as needed
pub const MAX_MEMORIES: usize = 8;

/// Memory table for a WASM module
///
/// This is a fixed-size array that can be statically allocated.
/// It's designed to be FFI-safe and cache-friendly.
#[repr(C)]
#[derive(Debug)]
pub struct MemoryTable {
    /// Memory descriptors (fixed-size array)
    pub memories: [MemoryDescriptor; MAX_MEMORIES],
    /// Number of active memories (0..=MAX_MEMORIES)
    pub count: u8,
}

impl MemoryTable {
    /// Create a new empty memory table
    pub const fn new() -> Self {
        Self {
            memories: [
                MemoryDescriptor::uninit(),
                MemoryDescriptor::uninit(),
                MemoryDescriptor::uninit(),
                MemoryDescriptor::uninit(),
                MemoryDescriptor::uninit(),
                MemoryDescriptor::uninit(),
                MemoryDescriptor::uninit(),
                MemoryDescriptor::uninit(),
            ],
            count: 0,
        }
    }

    /// Add a memory to the table
    ///
    /// Returns the memory index on success.
    pub fn add(&mut self, descriptor: MemoryDescriptor) -> Option<u32> {
        if self.count as usize >= MAX_MEMORIES {
            return None;
        }
        let index = self.count;
        self.memories[index as usize] = descriptor;
        self.count += 1;
        Some(index as u32)
    }

    /// Get a memory descriptor by index
    pub fn get(&self, index: u32) -> Option<&MemoryDescriptor> {
        if index < self.count as u32 {
            Some(&self.memories[index as usize])
        } else {
            None
        }
    }

    /// Get a mutable memory descriptor by index
    pub fn get_mut(&mut self, index: u32) -> Option<&mut MemoryDescriptor> {
        if index < self.count as u32 {
            Some(&mut self.memories[index as usize])
        } else {
            None
        }
    }

    /// Get the base address of a memory
    ///
    /// This is the hot path for code generation - returns just the base pointer.
    #[inline]
    pub fn base(&self, index: u32) -> Option<*mut u8> {
        self.get(index).map(|m| m.base)
    }

    /// Get the size of a memory in bytes
    #[inline]
    pub fn size(&self, index: u32) -> Option<u32> {
        self.get(index).map(|m| m.size)
    }

    /// Load i32 from memory (with bounds checking)
    #[inline]
    pub fn load_i32(&self, memory_idx: u32, addr: u32) -> Result<i32, Trap> {
        let mem = self.get(memory_idx).ok_or(Trap::OutOfBounds)?;
        if !mem.contains(addr, 4) {
            return Err(Trap::OutOfBounds);
        }
        // SAFETY: bounds checked above
        unsafe {
            let ptr = mem.base.add(addr as usize) as *const i32;
            Ok(ptr.read_unaligned())
        }
    }

    /// Store i32 to memory (with bounds checking)
    #[inline]
    pub fn store_i32(&self, memory_idx: u32, addr: u32, value: i32) -> Result<(), Trap> {
        let mem = self.get(memory_idx).ok_or(Trap::OutOfBounds)?;
        if !mem.contains(addr, 4) {
            return Err(Trap::OutOfBounds);
        }
        // SAFETY: bounds checked above
        unsafe {
            let ptr = mem.base.add(addr as usize) as *mut i32;
            ptr.write_unaligned(value);
        }
        Ok(())
    }

    /// Load i64 from memory (with bounds checking)
    #[inline]
    pub fn load_i64(&self, memory_idx: u32, addr: u32) -> Result<i64, Trap> {
        let mem = self.get(memory_idx).ok_or(Trap::OutOfBounds)?;
        if !mem.contains(addr, 8) {
            return Err(Trap::OutOfBounds);
        }
        unsafe {
            let ptr = mem.base.add(addr as usize) as *const i64;
            Ok(ptr.read_unaligned())
        }
    }

    /// Store i64 to memory (with bounds checking)
    #[inline]
    pub fn store_i64(&self, memory_idx: u32, addr: u32, value: i64) -> Result<(), Trap> {
        let mem = self.get(memory_idx).ok_or(Trap::OutOfBounds)?;
        if !mem.contains(addr, 8) {
            return Err(Trap::OutOfBounds);
        }
        unsafe {
            let ptr = mem.base.add(addr as usize) as *mut i64;
            ptr.write_unaligned(value);
        }
        Ok(())
    }

    /// Load byte from memory (with bounds checking)
    #[inline]
    pub fn load_u8(&self, memory_idx: u32, addr: u32) -> Result<u8, Trap> {
        let mem = self.get(memory_idx).ok_or(Trap::OutOfBounds)?;
        if !mem.contains(addr, 1) {
            return Err(Trap::OutOfBounds);
        }
        unsafe { Ok(*mem.base.add(addr as usize)) }
    }

    /// Store byte to memory (with bounds checking)
    #[inline]
    pub fn store_u8(&self, memory_idx: u32, addr: u32, value: u8) -> Result<(), Trap> {
        let mem = self.get(memory_idx).ok_or(Trap::OutOfBounds)?;
        if !mem.contains(addr, 1) {
            return Err(Trap::OutOfBounds);
        }
        unsafe {
            *mem.base.add(addr as usize) = value;
        }
        Ok(())
    }

    /// Grow memory by delta pages
    ///
    /// Returns previous page count on success, -1 on failure (per WASM spec).
    pub fn grow(&mut self, memory_idx: u32, delta: u32) -> i32 {
        match self.get_mut(memory_idx) {
            Some(mem) => mem.grow(delta).map(|p| p as i32).unwrap_or(-1),
            None => -1,
        }
    }

    /// Get memory size in pages
    pub fn size_pages(&self, memory_idx: u32) -> Option<u32> {
        self.get(memory_idx).map(|m| m.pages)
    }

    /// Copy memory from one region to another (within same or different memories)
    pub fn copy(
        &self,
        dst_mem: u32,
        dst_addr: u32,
        src_mem: u32,
        src_addr: u32,
        len: u32,
    ) -> Result<(), Trap> {
        // Get both memories
        let src = self.get(src_mem).ok_or(Trap::OutOfBounds)?;
        let dst = self.get(dst_mem).ok_or(Trap::OutOfBounds)?;

        // Bounds check both
        if !src.contains(src_addr, len) || !dst.contains(dst_addr, len) {
            return Err(Trap::OutOfBounds);
        }

        // SAFETY: bounds checked above
        unsafe {
            let src_ptr = src.base.add(src_addr as usize);
            let dst_ptr = dst.base.add(dst_addr as usize);

            // Use memmove semantics (handles overlap)
            core::ptr::copy(src_ptr, dst_ptr, len as usize);
        }

        Ok(())
    }

    /// Fill memory region with a value
    pub fn fill(&self, memory_idx: u32, addr: u32, value: u8, len: u32) -> Result<(), Trap> {
        let mem = self.get(memory_idx).ok_or(Trap::OutOfBounds)?;

        if !mem.contains(addr, len) {
            return Err(Trap::OutOfBounds);
        }

        // SAFETY: bounds checked above
        unsafe {
            let ptr = mem.base.add(addr as usize);
            core::ptr::write_bytes(ptr, value, len as usize);
        }

        Ok(())
    }
}

impl Default for MemoryTable {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{MemoryFlags, ProtectionStrategy};

    fn make_test_table() -> (MemoryTable, Vec<u8>) {
        let mut buffer = vec![0u8; 65536 * 2]; // 2 pages
        let mut table = MemoryTable::new();

        let desc = MemoryDescriptor::new(
            buffer.as_mut_ptr(),
            2,
            Some(4),
            ProtectionStrategy::Software,
            MemoryFlags::empty(),
        );

        table.add(desc);
        (table, buffer)
    }

    #[test]
    fn test_memory_table_add() {
        let mut table = MemoryTable::new();
        assert_eq!(table.count, 0);

        let mut buf = [0u8; 65536];
        let desc = MemoryDescriptor::new(
            buf.as_mut_ptr(),
            1,
            None,
            ProtectionStrategy::Software,
            MemoryFlags::empty(),
        );

        let idx = table.add(desc);
        assert_eq!(idx, Some(0));
        assert_eq!(table.count, 1);
    }

    #[test]
    fn test_memory_table_load_store() {
        let (table, mut _buffer) = make_test_table();

        // Store and load
        table.store_i32(0, 100, 0x12345678).unwrap();
        let value = table.load_i32(0, 100).unwrap();
        assert_eq!(value, 0x12345678);
    }

    #[test]
    fn test_memory_table_bounds() {
        let (table, mut _buffer) = make_test_table();

        // Out of bounds
        assert!(table.load_i32(0, 65536 * 2).is_err());
        assert!(table.store_i32(0, 65536 * 2, 0).is_err());

        // Invalid memory index
        assert!(table.load_i32(1, 0).is_err());
    }

    #[test]
    fn test_memory_table_fill() {
        let (table, mut _buffer) = make_test_table();

        table.fill(0, 0, 0xAB, 100).unwrap();

        for i in 0..100 {
            assert_eq!(table.load_u8(0, i).unwrap(), 0xAB);
        }
        // Next byte should still be 0
        assert_eq!(table.load_u8(0, 100).unwrap(), 0);
    }

    #[test]
    fn test_memory_table_copy() {
        let (table, mut _buffer) = make_test_table();

        // Write some data at offset 0
        table.store_i32(0, 0, 0x11223344).unwrap();
        table.store_i32(0, 4, 0x55667788).unwrap();

        // Copy to offset 100
        table.copy(0, 100, 0, 0, 8).unwrap();

        // Verify copy
        assert_eq!(table.load_i32(0, 100).unwrap(), 0x11223344);
        assert_eq!(table.load_i32(0, 104).unwrap(), 0x55667788);
    }
}
