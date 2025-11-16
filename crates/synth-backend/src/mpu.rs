//! ARM Cortex-M Memory Protection Unit (MPU) Support

use synth_core::{Error, Result};

/// MPU Region Size
///
/// ARM Cortex-M MPU requires power-of-2 sized regions
/// Values represent the power of 2 (e.g., Size32B = 5 means 2^5 = 32 bytes)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MPUSize {
    /// 32 bytes (2^5)
    Size32B = 5,
    /// 64 bytes (2^6)
    Size64B = 6,
    /// 128 bytes (2^7)
    Size128B = 7,
    /// 256 bytes (2^8)
    Size256B = 8,
    /// 512 bytes (2^9)
    Size512B = 9,
    /// 1 KB (2^10)
    Size1KB = 10,
    /// 2 KB (2^11)
    Size2KB = 11,
    /// 4 KB (2^12)
    Size4KB = 12,
    /// 8 KB (2^13)
    Size8KB = 13,
    /// 16 KB (2^14)
    Size16KB = 14,
    /// 32 KB (2^15)
    Size32KB = 15,
    /// 64 KB (2^16)
    Size64KB = 16,
    /// 128 KB (2^17)
    Size128KB = 17,
    /// 256 KB (2^18)
    Size256KB = 18,
    /// 512 KB (2^19)
    Size512KB = 19,
    /// 1 MB (2^20)
    Size1MB = 20,
    /// 2 MB (2^21)
    Size2MB = 21,
    /// 4 MB (2^22)
    Size4MB = 22,
    /// 8 MB (2^23)
    Size8MB = 23,
    /// 16 MB (2^24)
    Size16MB = 24,
    /// 32 MB (2^25)
    Size32MB = 25,
    /// 64 MB (2^26)
    Size64MB = 26,
    /// 128 MB (2^27)
    Size128MB = 27,
    /// 256 MB (2^28)
    Size256MB = 28,
    /// 512 MB (2^29)
    Size512MB = 29,
    /// 1 GB (2^30)
    Size1GB = 30,
    /// 2 GB (2^31)
    Size2GB = 31,
    /// 4 GB (2^32)
    Size4GB = 32,
}

impl MPUSize {
    /// Get size in bytes
    pub fn bytes(&self) -> u64 {
        1u64 << (*self as u8)
    }

    /// Create from byte size (rounds up to next power of 2)
    pub fn from_bytes(bytes: u64) -> Result<Self> {
        if bytes < 32 {
            return Err(Error::HardwareProtectionError(
                "MPU minimum region size is 32 bytes".to_string(),
            ));
        }
        if bytes > (1u64 << 32) {
            return Err(Error::HardwareProtectionError(
                "MPU maximum region size is 4GB".to_string(),
            ));
        }

        // Find the smallest power of 2 >= bytes
        let bit_pos = 64 - bytes.leading_zeros() - 1;
        let power = if bytes == (1u64 << bit_pos) {
            bit_pos
        } else {
            bit_pos + 1
        };

        match power {
            5 => Ok(MPUSize::Size32B),
            6 => Ok(MPUSize::Size64B),
            7 => Ok(MPUSize::Size128B),
            8 => Ok(MPUSize::Size256B),
            9 => Ok(MPUSize::Size512B),
            10 => Ok(MPUSize::Size1KB),
            11 => Ok(MPUSize::Size2KB),
            12 => Ok(MPUSize::Size4KB),
            13 => Ok(MPUSize::Size8KB),
            14 => Ok(MPUSize::Size16KB),
            15 => Ok(MPUSize::Size32KB),
            16 => Ok(MPUSize::Size64KB),
            17 => Ok(MPUSize::Size128KB),
            18 => Ok(MPUSize::Size256KB),
            19 => Ok(MPUSize::Size512KB),
            20 => Ok(MPUSize::Size1MB),
            21 => Ok(MPUSize::Size2MB),
            22 => Ok(MPUSize::Size4MB),
            23 => Ok(MPUSize::Size8MB),
            24 => Ok(MPUSize::Size16MB),
            25 => Ok(MPUSize::Size32MB),
            26 => Ok(MPUSize::Size64MB),
            27 => Ok(MPUSize::Size128MB),
            28 => Ok(MPUSize::Size256MB),
            29 => Ok(MPUSize::Size512MB),
            30 => Ok(MPUSize::Size1GB),
            31 => Ok(MPUSize::Size2GB),
            32 => Ok(MPUSize::Size4GB),
            _ => unreachable!(),
        }
    }
}

/// MPU Access Permissions
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MPUPermissions {
    /// No access
    NoAccess = 0,
    /// Privileged read/write, user no access
    PrivilegedRW = 1,
    /// Privileged read/write, user read-only
    PrivilegedRWUserRO = 2,
    /// Full read/write access
    FullRW = 3,
    /// Privileged read-only
    PrivilegedRO = 5,
    /// Read-only (privileged and user)
    FullRO = 6,
}

/// MPU Memory Attributes
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MPUAttributes {
    /// Shareable
    pub shareable: bool,
    /// Cacheable
    pub cacheable: bool,
    /// Bufferable
    pub bufferable: bool,
    /// Execute Never (XN)
    pub execute_never: bool,
}

impl MPUAttributes {
    /// Normal memory (cacheable, bufferable)
    pub fn normal() -> Self {
        Self {
            shareable: false,
            cacheable: true,
            bufferable: true,
            execute_never: false,
        }
    }

    /// Device memory (non-cacheable, non-bufferable)
    pub fn device() -> Self {
        Self {
            shareable: true,
            cacheable: false,
            bufferable: false,
            execute_never: true,
        }
    }

    /// Strongly-ordered memory
    pub fn strongly_ordered() -> Self {
        Self {
            shareable: true,
            cacheable: false,
            bufferable: false,
            execute_never: false,
        }
    }
}

/// MPU Region Configuration
#[derive(Debug, Clone)]
pub struct MPURegion {
    /// Region number (0-7 or 0-15 depending on implementation)
    pub number: u8,

    /// Base address (must be aligned to region size)
    pub base_address: u32,

    /// Region size
    pub size: MPUSize,

    /// Access permissions
    pub permissions: MPUPermissions,

    /// Memory attributes
    pub attributes: MPUAttributes,

    /// Subregion disable mask (8 bits, 1 = disabled)
    pub subregion_disable: u8,

    /// Region enabled
    pub enabled: bool,
}

impl MPURegion {
    /// Create a new MPU region
    pub fn new(number: u8, base_address: u32, size: MPUSize) -> Self {
        Self {
            number,
            base_address,
            size,
            permissions: MPUPermissions::FullRW,
            attributes: MPUAttributes::normal(),
            subregion_disable: 0,
            enabled: true,
        }
    }

    /// Validate region configuration
    pub fn validate(&self) -> Result<()> {
        // Check alignment
        let size_bytes = self.size.bytes();
        if size_bytes > u32::MAX as u64 {
            return Err(Error::HardwareProtectionError(
                "Region size exceeds 32-bit address space".to_string(),
            ));
        }

        let alignment = size_bytes as u32;
        if self.base_address % alignment != 0 {
            return Err(Error::HardwareProtectionError(format!(
                "Base address 0x{:08X} not aligned to region size {} bytes",
                self.base_address, size_bytes
            )));
        }

        Ok(())
    }

    /// Get RASR (Region Attribute and Size Register) value
    pub fn rasr(&self) -> u32 {
        let mut rasr = 0u32;

        // Enable bit
        if self.enabled {
            rasr |= 1 << 0;
        }

        // Size field (bits 1-5)
        rasr |= ((self.size as u32) << 1) & 0x3E;

        // Subregion disable (bits 8-15)
        rasr |= (self.subregion_disable as u32) << 8;

        // Attributes (bits 16-21)
        if self.attributes.bufferable {
            rasr |= 1 << 16;
        }
        if self.attributes.cacheable {
            rasr |= 1 << 17;
        }
        if self.attributes.shareable {
            rasr |= 1 << 18;
        }

        // TEX field (bits 19-21) - set to 0 for normal memory

        // Access permissions (bits 24-26)
        rasr |= (self.permissions as u32) << 24;

        // Execute Never (bit 28)
        if self.attributes.execute_never {
            rasr |= 1 << 28;
        }

        rasr
    }

    /// Get RBAR (Region Base Address Register) value
    pub fn rbar(&self) -> u32 {
        let mut rbar = self.base_address & 0xFFFFFFE0; // Clear lower 5 bits
        rbar |= (self.number as u32) & 0xF; // Region number in bits 0-3
        rbar |= 1 << 4; // VALID bit
        rbar
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mpu_size_from_bytes() {
        assert_eq!(MPUSize::from_bytes(32).unwrap(), MPUSize::Size32B);
        assert_eq!(MPUSize::from_bytes(64).unwrap(), MPUSize::Size64B);
        assert_eq!(MPUSize::from_bytes(100).unwrap(), MPUSize::Size128B); // Rounds up
        assert_eq!(MPUSize::from_bytes(1024).unwrap(), MPUSize::Size1KB);
        assert_eq!(MPUSize::from_bytes(65536).unwrap(), MPUSize::Size64KB);
    }

    #[test]
    fn test_mpu_size_bytes() {
        assert_eq!(MPUSize::Size32B.bytes(), 32);
        assert_eq!(MPUSize::Size1KB.bytes(), 1024);
        assert_eq!(MPUSize::Size64KB.bytes(), 65536);
        assert_eq!(MPUSize::Size1MB.bytes(), 1048576);
    }

    #[test]
    fn test_mpu_region_alignment() {
        let region = MPURegion::new(0, 0x20000000, MPUSize::Size64KB);
        assert!(region.validate().is_ok());

        let misaligned = MPURegion::new(0, 0x20000100, MPUSize::Size64KB);
        assert!(misaligned.validate().is_err());
    }

    #[test]
    fn test_mpu_rasr_generation() {
        let region = MPURegion::new(0, 0x20000000, MPUSize::Size64KB);
        let rasr = region.rasr();

        // Check enable bit
        assert_eq!(rasr & 0x1, 1);

        // Check size field
        let size_field = (rasr >> 1) & 0x1F;
        assert_eq!(size_field, MPUSize::Size64KB as u32);
    }
}
