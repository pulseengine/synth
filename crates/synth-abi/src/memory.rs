//! Memory management for Canonical ABI

use crate::{AbiError, AbiResult};

/// Memory interface for ABI operations
pub trait Memory {
    /// Read bytes from memory
    fn read(&self, addr: u32, len: usize) -> AbiResult<Vec<u8>>;

    /// Write bytes to memory
    fn write(&mut self, addr: u32, data: &[u8]) -> AbiResult<()>;

    /// Read a single byte
    fn read_u8(&self, addr: u32) -> AbiResult<u8> {
        let bytes = self.read(addr, 1)?;
        Ok(bytes[0])
    }

    /// Read a u16 (little-endian)
    fn read_u16(&self, addr: u32) -> AbiResult<u16> {
        let bytes = self.read(addr, 2)?;
        Ok(u16::from_le_bytes([bytes[0], bytes[1]]))
    }

    /// Read a u32 (little-endian)
    fn read_u32(&self, addr: u32) -> AbiResult<u32> {
        let bytes = self.read(addr, 4)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    /// Read a u64 (little-endian)
    fn read_u64(&self, addr: u32) -> AbiResult<u64> {
        let bytes = self.read(addr, 8)?;
        Ok(u64::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3],
            bytes[4], bytes[5], bytes[6], bytes[7],
        ]))
    }

    /// Write a u32 (little-endian)
    fn write_u32(&mut self, addr: u32, value: u32) -> AbiResult<()> {
        self.write(addr, &value.to_le_bytes())
    }

    /// Allocate memory
    fn allocate(&mut self, size: usize, align: usize) -> AbiResult<u32>;

    /// Free memory (optional, may be no-op)
    fn free(&mut self, _addr: u32, _size: usize, _align: usize) -> AbiResult<()> {
        Ok(()) // Default: no-op
    }
}

/// Simple in-memory implementation for testing
pub struct SimpleMemory {
    data: Vec<u8>,
    next_addr: u32,
}

impl SimpleMemory {
    pub fn new(size: usize) -> Self {
        Self {
            data: vec![0; size],
            next_addr: 0,
        }
    }

    pub fn with_data(data: Vec<u8>) -> Self {
        let next_addr = data.len() as u32;
        Self { data, next_addr }
    }
}

impl Memory for SimpleMemory {
    fn read(&self, addr: u32, len: usize) -> AbiResult<Vec<u8>> {
        let start = addr as usize;
        let end = start + len;

        if end > self.data.len() {
            return Err(AbiError::Trap(format!(
                "Memory access out of bounds: {} + {} > {}",
                addr, len, self.data.len()
            )));
        }

        Ok(self.data[start..end].to_vec())
    }

    fn write(&mut self, addr: u32, data: &[u8]) -> AbiResult<()> {
        let start = addr as usize;
        let end = start + data.len();

        if end > self.data.len() {
            return Err(AbiError::Trap(format!(
                "Memory write out of bounds: {} + {} > {}",
                addr, data.len(), self.data.len()
            )));
        }

        self.data[start..end].copy_from_slice(data);
        Ok(())
    }

    fn allocate(&mut self, size: usize, align: usize) -> AbiResult<u32> {
        // Align current address
        let aligned = ((self.next_addr as usize + align - 1) / align) * align;

        let new_addr = aligned + size;
        if new_addr > self.data.len() {
            // Try to grow memory
            if new_addr > self.data.capacity() {
                return Err(AbiError::OutOfMemory);
            }
            self.data.resize(new_addr, 0);
        }

        let result = aligned as u32;
        self.next_addr = new_addr as u32;
        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_memory_read_write() {
        let mut mem = SimpleMemory::new(1024);

        // Write some data
        mem.write(0, b"Hello").unwrap();

        // Read it back
        let data = mem.read(0, 5).unwrap();
        assert_eq!(&data, b"Hello");
    }

    #[test]
    fn test_simple_memory_u32() {
        let mut mem = SimpleMemory::new(1024);

        mem.write_u32(0, 0x12345678).unwrap();
        let value = mem.read_u32(0).unwrap();
        assert_eq!(value, 0x12345678);
    }

    #[test]
    fn test_simple_memory_allocate() {
        let mut mem = SimpleMemory::new(1024);

        // Allocate 100 bytes with 4-byte alignment
        let addr1 = mem.allocate(100, 4).unwrap();
        assert_eq!(addr1 % 4, 0);

        // Allocate another 50 bytes
        let addr2 = mem.allocate(50, 4).unwrap();
        assert!(addr2 >= addr1 + 100);
        assert_eq!(addr2 % 4, 0);
    }

    #[test]
    fn test_memory_out_of_bounds() {
        let mem = SimpleMemory::new(10);

        // Try to read past end
        let result = mem.read(0, 20);
        assert!(result.is_err());
    }
}
