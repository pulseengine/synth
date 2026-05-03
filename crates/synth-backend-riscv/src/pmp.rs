//! Physical Memory Protection (PMP) allocator.
//!
//! PMP is RISC-V's analogue of ARM's MPU — a small set of memory regions
//! (8 or 16 entries on RV32) checked by hardware on every load/store/fetch.
//! Unlike the ARM MPU, PMP supports both *naturally aligned power-of-two*
//! (NAPOT) and *top-of-range* (TOR) modes, which makes arbitrary-size
//! regions cheaper than on Cortex-M.
//!
//! Reference: RISC-V Privileged Architecture, version 20211203,
//! Chapter 3.7 (Physical Memory Protection).

use synth_core::{HardwareCapabilities, Memory};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum PMPError {
    #[error("no PMP entries available (max: {max})")]
    OutOfEntries { max: u8 },

    #[error("region size {0} is too small for NAPOT (minimum 4 bytes)")]
    NapotTooSmall(u64),

    #[error("region [{base:#X}..{end:#X}] overlaps with existing PMP entry {existing}")]
    RegionOverlap { base: u64, end: u64, existing: u8 },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct PMPPermissions {
    pub read: bool,
    pub write: bool,
    pub execute: bool,
}

impl PMPPermissions {
    pub const fn rwx() -> Self {
        Self {
            read: true,
            write: true,
            execute: true,
        }
    }
    pub const fn rw() -> Self {
        Self {
            read: true,
            write: true,
            execute: false,
        }
    }
    pub const fn ro() -> Self {
        Self {
            read: true,
            write: false,
            execute: false,
        }
    }
    pub const fn rx() -> Self {
        Self {
            read: true,
            write: false,
            execute: true,
        }
    }
}

/// Address-matching mode encoded in `pmpcfg.A` (2 bits).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PMPMode {
    /// Region disabled (A = 0b00)
    Off,
    /// Top-of-range — entry `i` matches `[pmpaddr[i-1], pmpaddr[i])`
    Tor,
    /// Naturally-aligned 4-byte region (A = 0b10) — rarely used
    Na4,
    /// Naturally-aligned power-of-2 (A = 0b11) — most common
    Napot,
}

impl PMPMode {
    pub fn bits(self) -> u8 {
        match self {
            PMPMode::Off => 0b00,
            PMPMode::Tor => 0b01,
            PMPMode::Na4 => 0b10,
            PMPMode::Napot => 0b11,
        }
    }
}

/// One PMP entry: a region with permissions and matching mode.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PMPEntry {
    pub index: u8,
    pub mode: PMPMode,
    pub perms: PMPPermissions,
    pub base: u64,
    pub size: u64,
    pub locked: bool,
}

impl PMPEntry {
    /// Compute the value to write into the corresponding `pmpaddr<i>` CSR.
    /// PMP addresses are *byte-aligned*, but the CSR holds them shifted right
    /// by 2 (so each LSB represents 4 bytes).
    pub fn pmpaddr_value(&self) -> u64 {
        match self.mode {
            PMPMode::Napot => {
                // For NAPOT: the address encodes both base and size.
                // The lowest (log2(size) - 3) bits are 1, the rest hold the base.
                if self.size < 8 {
                    // 4-byte regions use NA4, not NAPOT — but still encode shifted.
                    self.base >> 2
                } else {
                    let trailing_ones = (self.size.trailing_zeros() as u64).saturating_sub(3);
                    let mask = (1u64 << trailing_ones) - 1;
                    (self.base >> 2) | mask
                }
            }
            PMPMode::Tor => self.base >> 2,
            PMPMode::Na4 => self.base >> 2,
            PMPMode::Off => 0,
        }
    }

    /// Compute the byte to OR into `pmpcfg<n>` for this entry.
    pub fn pmpcfg_byte(&self) -> u8 {
        let mut b = 0u8;
        if self.perms.read {
            b |= 0b001;
        }
        if self.perms.write {
            b |= 0b010;
        }
        if self.perms.execute {
            b |= 0b100;
        }
        b |= self.mode.bits() << 3;
        if self.locked {
            b |= 0b1000_0000;
        }
        b
    }
}

/// Allocator for PMP entries — picks `Napot` mode when the region is a
/// power of two, falls back to `Tor` (which costs 2 entries) otherwise.
pub struct PMPAllocator {
    hw_caps: HardwareCapabilities,
    entries: Vec<PMPEntry>,
}

impl PMPAllocator {
    pub fn new(hw_caps: HardwareCapabilities) -> Self {
        Self {
            hw_caps,
            entries: Vec::new(),
        }
    }

    pub fn entries(&self) -> &[PMPEntry] {
        &self.entries
    }

    pub fn available_entries(&self) -> u8 {
        self.hw_caps
            .pmp_entries
            .saturating_sub(self.entries.len() as u8)
    }

    /// Add a region described by a wasm `Memory` plus permissions.
    pub fn allocate_for_memory(
        &mut self,
        memory: Memory,
        base: u64,
        perms: PMPPermissions,
    ) -> Result<&PMPEntry, PMPError> {
        let size_bytes = memory.initial as u64 * 65536;
        self.allocate_region(base, size_bytes, perms)
    }

    /// Add a flat byte-range region.
    pub fn allocate_region(
        &mut self,
        base: u64,
        size: u64,
        perms: PMPPermissions,
    ) -> Result<&PMPEntry, PMPError> {
        if self.available_entries() == 0 {
            return Err(PMPError::OutOfEntries {
                max: self.hw_caps.pmp_entries,
            });
        }
        if size < 4 {
            return Err(PMPError::NapotTooSmall(size));
        }

        for existing in &self.entries {
            let e_start = existing.base;
            let e_end = existing.base + existing.size;
            let n_end = base + size;
            if !(n_end <= e_start || e_end <= base) {
                return Err(PMPError::RegionOverlap {
                    base,
                    end: n_end,
                    existing: existing.index,
                });
            }
        }

        let mode = if size.is_power_of_two() && size >= 8 && (base & (size - 1)) == 0 {
            PMPMode::Napot
        } else if size == 4 && (base & 3) == 0 {
            PMPMode::Na4
        } else {
            // TOR consumes two entries; check we have room.
            if self.available_entries() < 2 {
                return Err(PMPError::OutOfEntries {
                    max: self.hw_caps.pmp_entries,
                });
            }
            PMPMode::Tor
        };

        if mode == PMPMode::Tor {
            // Entry N: base address (mode = OFF, addr = base)
            // Entry N+1: TOR mode, addr = base+size
            let lo_idx = self.entries.len() as u8;
            self.entries.push(PMPEntry {
                index: lo_idx,
                mode: PMPMode::Off,
                perms: PMPPermissions::default(),
                base,
                size: 0,
                locked: false,
            });
            let hi_idx = self.entries.len() as u8;
            self.entries.push(PMPEntry {
                index: hi_idx,
                mode: PMPMode::Tor,
                perms,
                base: base + size,
                size,
                locked: false,
            });
            return Ok(self.entries.last().unwrap());
        }

        let idx = self.entries.len() as u8;
        self.entries.push(PMPEntry {
            index: idx,
            mode,
            perms,
            base,
            size,
            locked: false,
        });
        Ok(self.entries.last().unwrap())
    }

    /// Generate C-like initialization code (mirrors the ARM MPU emitter).
    pub fn generate_init_code(&self) -> String {
        let mut out = String::new();
        out.push_str("/* PMP Initialization Code */\n");
        out.push_str("/* Generated by Synth WebAssembly Component Synthesizer */\n\n");
        out.push_str("#include <stdint.h>\n\n");
        out.push_str("static inline void csrw_pmpaddr(int i, unsigned long v) {\n");
        out.push_str("    switch(i) {\n");
        for i in 0..self.hw_caps.pmp_entries {
            out.push_str(&format!(
                "        case {0}: __asm__ volatile(\"csrw pmpaddr{0}, %0\" :: \"r\"(v)); break;\n",
                i
            ));
        }
        out.push_str("    }\n}\n\n");

        out.push_str("void pmp_init(void) {\n");
        for entry in &self.entries {
            out.push_str(&format!(
                "    /* Entry {}: base=0x{:X} size=0x{:X} mode={:?} */\n",
                entry.index, entry.base, entry.size, entry.mode
            ));
            out.push_str(&format!(
                "    csrw_pmpaddr({}, 0x{:X}UL);\n",
                entry.index,
                entry.pmpaddr_value()
            ));
        }
        // Aggregate pmpcfg writes — pack 4 entries per pmpcfg<N> CSR on RV32.
        let mut cfg_word: [u8; 16] = [0; 16];
        for entry in &self.entries {
            cfg_word[entry.index as usize] = entry.pmpcfg_byte();
        }
        for chunk in 0..(self.hw_caps.pmp_entries.div_ceil(4) as usize) {
            let base = chunk * 4;
            let mut w: u32 = 0;
            for (i, b) in cfg_word.iter().skip(base).take(4).enumerate() {
                w |= (*b as u32) << (i * 8);
            }
            out.push_str(&format!(
                "    __asm__ volatile(\"csrw pmpcfg{0}, %0\" :: \"r\"(0x{1:08X}UL));\n",
                chunk, w
            ));
        }
        out.push_str("}\n");
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use synth_core::{HardwareCapabilities, RISCVVariant, TargetArch};

    fn riscv32_caps() -> HardwareCapabilities {
        HardwareCapabilities {
            arch: TargetArch::RISCV(RISCVVariant::RV32IMAC),
            has_mpu: false,
            mpu_regions: 0,
            has_pmp: true,
            pmp_entries: 16,
            has_fpu: false,
            fpu_precision: None,
            has_simd: false,
            simd_level: None,
            xip_capable: true,
            flash_size: 4 * 1024 * 1024,
            ram_size: 256 * 1024,
        }
    }

    #[test]
    fn napot_mode_for_power_of_two() {
        let mut alloc = PMPAllocator::new(riscv32_caps());
        let entry = alloc
            .allocate_region(0x80000000, 0x10000, PMPPermissions::rw())
            .unwrap();
        assert_eq!(entry.mode, PMPMode::Napot);
    }

    #[test]
    fn tor_mode_for_non_power_of_two_consumes_two_entries() {
        let mut alloc = PMPAllocator::new(riscv32_caps());
        let _ = alloc
            .allocate_region(0x80000000, 12288, PMPPermissions::rw()) // 12 KB — not pow2
            .unwrap();
        assert_eq!(alloc.entries().len(), 2);
        assert_eq!(alloc.entries()[0].mode, PMPMode::Off);
        assert_eq!(alloc.entries()[1].mode, PMPMode::Tor);
    }

    #[test]
    fn napot_addr_encoding_64kb() {
        // 64 KB region @ 0x80000000:
        // pmpaddr = (base >> 2) | mask where mask = 0x3FFF (14 ones)
        // 64 KB = 2^16, so trailing_zeros = 16, trailing_ones = 16 - 3 = 13
        // base >> 2 = 0x20000000
        // mask = 0x1FFF
        // result = 0x20001FFF
        let entry = PMPEntry {
            index: 0,
            mode: PMPMode::Napot,
            perms: PMPPermissions::rw(),
            base: 0x80000000,
            size: 0x10000,
            locked: false,
        };
        assert_eq!(entry.pmpaddr_value(), 0x20001FFF);
    }

    #[test]
    fn pmpcfg_byte_rwx() {
        let entry = PMPEntry {
            index: 0,
            mode: PMPMode::Napot,
            perms: PMPPermissions::rwx(),
            base: 0,
            size: 16,
            locked: false,
        };
        // R | W | X | mode 0b11<<3
        assert_eq!(entry.pmpcfg_byte(), 0b0001_1111);
    }

    #[test]
    fn out_of_entries() {
        let mut caps = riscv32_caps();
        caps.pmp_entries = 1;
        let mut alloc = PMPAllocator::new(caps);
        alloc.allocate_region(0, 16, PMPPermissions::rw()).unwrap();
        let r = alloc.allocate_region(0x1000, 16, PMPPermissions::rw());
        assert!(matches!(r, Err(PMPError::OutOfEntries { .. })));
    }

    #[test]
    fn overlap_detected() {
        let mut alloc = PMPAllocator::new(riscv32_caps());
        alloc
            .allocate_region(0x80000000, 0x10000, PMPPermissions::rw())
            .unwrap();
        let r = alloc.allocate_region(0x80008000, 0x10000, PMPPermissions::rw());
        assert!(matches!(r, Err(PMPError::RegionOverlap { .. })));
    }

    #[test]
    fn init_code_contains_csr_writes() {
        let mut alloc = PMPAllocator::new(riscv32_caps());
        alloc
            .allocate_region(0x80000000, 0x10000, PMPPermissions::rw())
            .unwrap();
        let code = alloc.generate_init_code();
        assert!(code.contains("pmp_init"));
        assert!(code.contains("csrw pmpaddr0"));
        assert!(code.contains("csrw pmpcfg0"));
    }
}
