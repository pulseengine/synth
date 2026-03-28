//! Formal contracts for synth's critical subsystems.
//!
//! These specifications define the safety invariants that must hold for correct
//! compilation of WebAssembly to ARM Cortex-M machine code.
//!
//! # Dual-mode operation
//!
//! This file is written with Verus annotations inside `verus! {}` blocks.
//! Two compilation paths are supported:
//!
//! 1. **Verus verification**: `verus_test` (via rules_verus) checks the specs
//! 2. **Plain Rust**: `verus_strip` removes annotations; `debug_assert!` provides
//!    runtime contract checking in debug builds
//!
//! The `verus_strip` tool (rules_verus @ 24d5ddb5) removes:
//! - `verus! { }` macro wrappers
//! - `spec fn`, `proof fn` items
//! - `requires` / `ensures` / `decreases` clauses
//! - `#[verifier::*]` attributes
//!
//! See: <https://pulseengine.eu/guides/VERIFICATION-GUIDE.md>

#![allow(unexpected_cfgs)]

use crate::rules::Reg;

// ---------------------------------------------------------------------------
// Verus specifications (machine-checked when running verus_test)
//
// When building with plain cargo (no Verus), the verus! macro is a no-op.
// When building with Verus, it enables verification.
// When using verus_strip, the entire block is removed.
// ---------------------------------------------------------------------------

/// No-op verus! macro for plain Rust compilation.
/// Verus replaces this with its own macro; verus_strip removes the block entirely.
#[cfg(not(verus_keep_ghost))]
macro_rules! verus {
    ($($t:tt)*) => {};
}

verus! {

/// Spec: a register number is safe to allocate as a temporary.
pub open spec fn spec_is_allocatable(reg_num: u8) -> bool {
    reg_num <= 12
    && reg_num != 9   // R9  = globals base
    && reg_num != 10  // R10 = memory size
    && reg_num != 11  // R11 = memory base
}

/// Spec: a Thumb-16 instruction is exactly 2 bytes.
pub open spec fn spec_valid_thumb16(len: usize) -> bool {
    len == 2
}

/// Spec: a Thumb-32 instruction is exactly 4 bytes.
pub open spec fn spec_valid_thumb32(len: usize) -> bool {
    len == 4
}

/// Spec: a MOVW/MOVT immediate fits in 16 bits.
pub open spec fn spec_valid_imm16(imm: u32) -> bool {
    imm <= 0xFFFF
}

/// Spec: a register number is valid for Thumb-2 encoding.
pub open spec fn spec_valid_reg(rd: u32) -> bool {
    rd <= 14
}

/// Spec: an access size is valid for WebAssembly memory operations.
pub open spec fn spec_valid_access_size(size: u32) -> bool {
    size == 1 || size == 2 || size == 4 || size == 8
}

/// Spec: a bounds check correctly covers the full access range.
pub open spec fn spec_bounds_check_correct(addr: u32, access_size: u32, memory_size: u32) -> bool {
    addr as int + access_size as int <= memory_size as int
}

/// Spec: a division trap guard has the minimum instruction count.
pub open spec fn spec_valid_trap_guard(sequence_len: usize) -> bool {
    sequence_len >= 4
}

} // verus!

// ---------------------------------------------------------------------------
// Runtime contract checking (debug_assert! — works in plain Rust)
// ---------------------------------------------------------------------------

/// Register allocator invariants.
///
/// The register allocator must never hand out registers reserved by the
/// runtime calling convention:
/// - R9:  globals base pointer
/// - R10: linear memory size (for bounds checks)
/// - R11: linear memory base pointer
pub mod regalloc {
    use super::Reg;

    /// Reserved registers that must NEVER be allocated as temporaries.
    pub const RESERVED_REGS: [Reg; 3] = [Reg::R9, Reg::R10, Reg::R11];

    /// Maximum register index for general-purpose temporaries.
    pub const MAX_GP_REG: u8 = 12;

    /// Check that a register is safe to allocate as a temporary.
    #[inline]
    pub fn is_allocatable(reg: &Reg) -> bool {
        !RESERVED_REGS.contains(reg) && !matches!(reg, Reg::SP | Reg::LR | Reg::PC)
    }

    /// Assert that a register allocation satisfies the allocator postcondition.
    #[inline]
    pub fn verify_allocation(reg: &Reg) {
        debug_assert!(
            is_allocatable(reg),
            "CONTRACT VIOLATION [regalloc::alloc_reg]: allocated reserved register {:?} \
             (R9=globals, R10=mem_size, R11=mem_base are reserved)",
            reg
        );
    }

    /// Assert that a register index is within the allocatable set.
    #[inline]
    pub fn verify_index(index: u8, allocatable_len: usize) {
        debug_assert!(
            (index as usize) < allocatable_len,
            "CONTRACT VIOLATION [regalloc::index_to_reg]: register index {} >= allocatable set \
             size {}",
            index,
            allocatable_len
        );
    }
}

/// ARM instruction encoding invariants.
pub mod encoding {
    /// Verify Thumb-2 16-bit encoding produces exactly 2 bytes.
    #[inline]
    pub fn verify_thumb16(bytes: &[u8]) {
        debug_assert_eq!(
            bytes.len(),
            2,
            "CONTRACT VIOLATION [encoding::thumb16]: must be 2 bytes, got {}",
            bytes.len()
        );
    }

    /// Verify Thumb-2 32-bit encoding produces exactly 4 bytes.
    #[inline]
    pub fn verify_thumb32(bytes: &[u8]) {
        debug_assert_eq!(
            bytes.len(),
            4,
            "CONTRACT VIOLATION [encoding::thumb32]: must be 4 bytes, got {}",
            bytes.len()
        );
    }

    /// Verify MOVW/MOVT immediate fits in 16 bits.
    #[inline]
    pub fn verify_imm16(imm: u32) {
        debug_assert!(
            imm <= 0xFFFF,
            "CONTRACT VIOLATION [encoding::movw_movt]: immediate {:#x} exceeds 16-bit range",
            imm
        );
    }

    /// Verify register number is valid for Thumb-2 (R0-R14).
    #[inline]
    pub fn verify_reg_bits(rd: u32) {
        debug_assert!(
            rd <= 14,
            "CONTRACT VIOLATION [encoding::reg]: register {} exceeds valid range (0-14)",
            rd
        );
    }

    /// Verify register number is valid for Thumb-16 low register (R0-R7).
    #[inline]
    pub fn verify_low_reg(reg: u32) {
        debug_assert!(
            reg <= 7,
            "CONTRACT VIOLATION [encoding::low_reg]: register {} must be 0-7 for Thumb-16",
            reg
        );
    }
}

/// Memory access safety invariants.
pub mod memory {
    /// Valid access sizes for WebAssembly memory operations.
    pub const VALID_ACCESS_SIZES: [u32; 4] = [1, 2, 4, 8];

    /// Verify access size is valid.
    #[inline]
    pub fn verify_access_size(access_size: u32) {
        debug_assert!(
            VALID_ACCESS_SIZES.contains(&access_size),
            "CONTRACT VIOLATION [memory::access_size]: invalid size {} (must be 1, 2, 4, or 8)",
            access_size
        );
    }

    /// Verify bounds check covers the full access range.
    #[inline]
    pub fn verify_bounds_check(addr: u32, access_size: u32, memory_size: u32) -> bool {
        addr.checked_add(access_size)
            .is_some_and(|end| end <= memory_size)
    }
}

/// Division trap guard invariants.
pub mod division {
    /// Verify division trap guard has minimum instruction count (CMP+BNE+UDF+xDIV).
    #[inline]
    pub fn verify_trap_guard_length(sequence_len: usize) {
        debug_assert!(
            sequence_len >= 4,
            "CONTRACT VIOLATION [division::trap_guard]: must have >= 4 instructions, got {}",
            sequence_len
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_regalloc_allocatable() {
        assert!(regalloc::is_allocatable(&Reg::R0));
        assert!(regalloc::is_allocatable(&Reg::R1));
        assert!(regalloc::is_allocatable(&Reg::R4));
        assert!(regalloc::is_allocatable(&Reg::R8));
        assert!(regalloc::is_allocatable(&Reg::R12));
    }

    #[test]
    fn test_regalloc_reserved() {
        assert!(!regalloc::is_allocatable(&Reg::R9));
        assert!(!regalloc::is_allocatable(&Reg::R10));
        assert!(!regalloc::is_allocatable(&Reg::R11));
    }

    #[test]
    fn test_regalloc_architectural() {
        assert!(!regalloc::is_allocatable(&Reg::SP));
        assert!(!regalloc::is_allocatable(&Reg::LR));
        assert!(!regalloc::is_allocatable(&Reg::PC));
    }

    #[test]
    fn test_encoding_verify_imm16_valid() {
        encoding::verify_imm16(0);
        encoding::verify_imm16(0xFFFF);
        encoding::verify_imm16(42);
    }

    #[test]
    #[should_panic(expected = "CONTRACT VIOLATION")]
    fn test_encoding_verify_imm16_overflow() {
        encoding::verify_imm16(0x10000);
    }

    #[test]
    fn test_memory_valid_access_sizes() {
        memory::verify_access_size(1);
        memory::verify_access_size(2);
        memory::verify_access_size(4);
        memory::verify_access_size(8);
    }

    #[test]
    #[should_panic(expected = "CONTRACT VIOLATION")]
    fn test_memory_invalid_access_size() {
        memory::verify_access_size(3);
    }

    #[test]
    fn test_memory_bounds_check() {
        assert!(memory::verify_bounds_check(0, 4, 65536));
        assert!(memory::verify_bounds_check(65532, 4, 65536));
        assert!(!memory::verify_bounds_check(65533, 4, 65536));
        assert!(!memory::verify_bounds_check(u32::MAX, 1, u32::MAX));
    }

    #[test]
    fn test_division_trap_guard_length() {
        division::verify_trap_guard_length(4);
        division::verify_trap_guard_length(5);
    }

    #[test]
    #[should_panic(expected = "CONTRACT VIOLATION")]
    fn test_division_trap_guard_too_short() {
        division::verify_trap_guard_length(3);
    }
}
