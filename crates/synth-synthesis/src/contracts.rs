//! Formal contracts for synth's critical subsystems.
//!
//! These specifications define the safety invariants that must hold for correct
//! compilation of WebAssembly to ARM Cortex-M machine code. They serve as:
//!
//! 1. Documentation of the intended behavior and invariants
//! 2. Runtime assertions in debug builds (`debug_assert!`)
//! 3. Future Verus verification targets (`verus! {}` blocks)
//!
//! # Verus Integration Path
//!
//! When `rules_verus` with `verus_strip` is integrated into the Bazel build,
//! each contract function will be wrapped in a `verus! {}` block with
//! `requires`/`ensures` clauses. The `debug_assert!` calls serve as the
//! runtime shadow of those formal specs until then.
//!
//! See: <https://pulseengine.eu/guides/VERIFICATION-GUIDE.md>

use crate::rules::Reg;

/// Register allocator invariants.
///
/// The register allocator must never hand out registers reserved by the
/// runtime calling convention:
/// - R9:  globals base pointer
/// - R10: linear memory size (for bounds checks)
/// - R11: linear memory base pointer
///
/// # Verus spec (future)
/// ```text
/// verus! {
///     spec fn is_allocatable(reg: u8) -> bool {
///         reg <= 12 && reg != 9 && reg != 10 && reg != 11
///     }
/// }
/// ```
pub mod regalloc {
    use super::Reg;

    /// Reserved registers that must NEVER be allocated as temporaries.
    /// - R9  = globals base pointer
    /// - R10 = linear memory size
    /// - R11 = linear memory base pointer
    pub const RESERVED_REGS: [Reg; 3] = [Reg::R9, Reg::R10, Reg::R11];

    /// Maximum register index that can be used as a general-purpose temporary.
    /// R13 (SP), R14 (LR), R15 (PC) are architectural and must not be allocated.
    pub const MAX_GP_REG: u8 = 12;

    /// Check that a register is safe to allocate as a temporary.
    ///
    /// # Verus spec (future)
    /// ```text
    /// ensures |result: bool|
    ///     result <==> (reg_num <= 12 && reg_num != 9 && reg_num != 10 && reg_num != 11)
    /// ```
    #[inline]
    pub fn is_allocatable(reg: &Reg) -> bool {
        !RESERVED_REGS.contains(reg) && !matches!(reg, Reg::SP | Reg::LR | Reg::PC)
    }

    /// Assert that a register allocation satisfies the allocator postcondition.
    ///
    /// # Verus spec (future)
    /// ```text
    /// requires self.next_reg < ALLOCATABLE_REGS.len()
    /// ensures
    ///     is_allocatable(result),
    ///     result != Reg::R9,
    ///     result != Reg::R10,
    ///     result != Reg::R11,
    /// ```
    #[inline]
    pub fn verify_allocation(reg: &Reg) {
        debug_assert!(
            is_allocatable(reg),
            "CONTRACT VIOLATION [regalloc::alloc_reg]: allocated reserved register {:?} \
             (R9=globals, R10=mem_size, R11=mem_base are reserved)",
            reg
        );
    }

    /// Assert that a register index is within the allocatable set before
    /// conversion via `index_to_reg`.
    ///
    /// # Verus spec (future)
    /// ```text
    /// requires index < ALLOCATABLE_REGS.len()
    /// ```
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
///
/// These contracts ensure the encoder produces correctly-sized instruction
/// words and that operand fields are within their bit-width limits.
///
/// # Verus spec (future)
/// ```text
/// verus! {
///     spec fn valid_thumb16(bytes: Seq<u8>) -> bool {
///         bytes.len() == 2
///     }
///     spec fn valid_thumb32(bytes: Seq<u8>) -> bool {
///         bytes.len() == 4
///     }
/// }
/// ```
pub mod encoding {
    /// Verify that a Thumb-2 16-bit encoding produces exactly 2 bytes.
    ///
    /// # Verus spec (future)
    /// ```text
    /// ensures bytes.len() == 2
    /// ```
    #[inline]
    pub fn verify_thumb16(bytes: &[u8]) {
        debug_assert_eq!(
            bytes.len(),
            2,
            "CONTRACT VIOLATION [encoding::thumb16]: Thumb-16 instruction must be exactly 2 \
             bytes, got {}",
            bytes.len()
        );
    }

    /// Verify that a Thumb-2 32-bit encoding produces exactly 4 bytes.
    ///
    /// # Verus spec (future)
    /// ```text
    /// ensures bytes.len() == 4
    /// ```
    #[inline]
    pub fn verify_thumb32(bytes: &[u8]) {
        debug_assert_eq!(
            bytes.len(),
            4,
            "CONTRACT VIOLATION [encoding::thumb32]: Thumb-32 instruction must be exactly 4 \
             bytes, got {}",
            bytes.len()
        );
    }

    /// Verify that a MOVW/MOVT immediate fits in 16 bits.
    ///
    /// # Verus spec (future)
    /// ```text
    /// requires imm <= 0xFFFF
    /// ```
    #[inline]
    pub fn verify_imm16(imm: u32) {
        debug_assert!(
            imm <= 0xFFFF,
            "CONTRACT VIOLATION [encoding::movw_movt]: immediate value {:#x} exceeds 16-bit \
             range (max {:#x})",
            imm,
            0xFFFFu32
        );
    }

    /// Verify that a register number is valid for Thumb-2 encoding.
    /// General-purpose registers are R0-R12 (0-12), plus SP(13), LR(14).
    /// R15 (PC) is not valid as a destination in most encodings.
    ///
    /// # Verus spec (future)
    /// ```text
    /// requires rd <= 14
    /// ```
    #[inline]
    pub fn verify_reg_bits(rd: u32) {
        debug_assert!(
            rd <= 14,
            "CONTRACT VIOLATION [encoding::reg]: register number {} exceeds valid range (0-14)",
            rd
        );
    }

    /// Verify that a register number is valid for Thumb-16 low register encoding.
    /// Thumb-16 instructions can only encode R0-R7 (3-bit register field).
    ///
    /// # Verus spec (future)
    /// ```text
    /// requires reg <= 7
    /// ```
    #[inline]
    pub fn verify_low_reg(reg: u32) {
        debug_assert!(
            reg <= 7,
            "CONTRACT VIOLATION [encoding::low_reg]: register {} is not a low register (must be \
             0-7 for Thumb-16)",
            reg
        );
    }
}

/// Memory access safety invariants.
///
/// WebAssembly requires bounds-checked memory access. These contracts verify
/// that bounds checks correctly account for the access size, preventing
/// out-of-bounds reads/writes.
///
/// # Verus spec (future)
/// ```text
/// verus! {
///     spec fn bounds_check_correct(addr: u32, access_size: u32, memory_size: u32) -> bool {
///         addr + access_size <= memory_size
///     }
/// }
/// ```
pub mod memory {
    /// Valid access sizes for WebAssembly memory operations.
    /// - 1: i32.load8_s, i32.load8_u, i64.load8_s, i64.load8_u
    /// - 2: i32.load16_s, i32.load16_u, i64.load16_s, i64.load16_u
    /// - 4: i32.load, i32.store, f32.load, f32.store, i64.load32_s, i64.load32_u
    /// - 8: i64.load, i64.store, f64.load, f64.store
    pub const VALID_ACCESS_SIZES: [u32; 4] = [1, 2, 4, 8];

    /// Verify that the access size is a valid WebAssembly memory access width.
    ///
    /// # Verus spec (future)
    /// ```text
    /// requires access_size in set![1u32, 2u32, 4u32, 8u32]
    /// ```
    #[inline]
    pub fn verify_access_size(access_size: u32) {
        debug_assert!(
            VALID_ACCESS_SIZES.contains(&access_size),
            "CONTRACT VIOLATION [memory::access_size]: invalid access size {} (must be 1, 2, 4, \
             or 8)",
            access_size
        );
    }

    /// Verify that a bounds check correctly covers the full access range.
    /// The check must compare `addr + access_size - 1` against `memory_size`,
    /// not just `addr` alone.
    ///
    /// # Verus spec (future)
    /// ```text
    /// ensures
    ///     result ==> addr + access_size <= memory_size,
    ///     !result ==> addr + access_size > memory_size || overflow,
    /// ```
    #[inline]
    pub fn verify_bounds_check(addr: u32, access_size: u32, memory_size: u32) -> bool {
        addr.checked_add(access_size)
            .is_some_and(|end| end <= memory_size)
    }
}

/// Division trap guard invariants.
///
/// WebAssembly requires trapping on integer division by zero. ARM's SDIV/UDIV
/// instructions silently return 0 on division by zero, so the compiler must
/// emit an explicit check sequence before every division:
///
/// ```text
/// CMP  divisor, #0      ; test for zero divisor
/// BNE  skip             ; skip trap if non-zero
/// UDF  #0               ; trigger UsageFault (WASM trap)
/// skip:
/// SDIV/UDIV rd, rn, rm  ; safe to divide
/// ```
///
/// For signed division (I32DivS), an additional overflow check is needed:
/// `INT_MIN / -1` overflows in two's complement.
pub mod division {
    /// Verify that a division trap guard sequence has the correct structure.
    /// The sequence must contain: CMP, BNE (conditional branch), UDF, then SDIV/UDIV.
    ///
    /// # Verus spec (future)
    /// ```text
    /// ensures
    ///     sequence[0] is Cmp { rn: divisor, op2: Imm(0) },
    ///     sequence[1] is BCondOffset { cond: NE, .. },
    ///     sequence[2] is Udf { .. },
    ///     sequence[3] is Sdiv { .. } || sequence[3] is Udiv { .. },
    /// ```
    #[inline]
    pub fn verify_trap_guard_length(sequence_len: usize) {
        debug_assert!(
            sequence_len >= 4,
            "CONTRACT VIOLATION [division::trap_guard]: division trap guard sequence must have \
             at least 4 instructions (CMP, BNE, UDF, xDIV), got {}",
            sequence_len
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_regalloc_allocatable() {
        // R0-R8 and R12 should be allocatable
        assert!(regalloc::is_allocatable(&Reg::R0));
        assert!(regalloc::is_allocatable(&Reg::R1));
        assert!(regalloc::is_allocatable(&Reg::R4));
        assert!(regalloc::is_allocatable(&Reg::R8));
        assert!(regalloc::is_allocatable(&Reg::R12));
    }

    #[test]
    fn test_regalloc_reserved() {
        // R9, R10, R11 must NOT be allocatable
        assert!(!regalloc::is_allocatable(&Reg::R9));
        assert!(!regalloc::is_allocatable(&Reg::R10));
        assert!(!regalloc::is_allocatable(&Reg::R11));
    }

    #[test]
    fn test_regalloc_architectural() {
        // SP, LR, PC must NOT be allocatable
        assert!(!regalloc::is_allocatable(&Reg::SP));
        assert!(!regalloc::is_allocatable(&Reg::LR));
        assert!(!regalloc::is_allocatable(&Reg::PC));
    }

    #[test]
    fn test_encoding_verify_imm16_valid() {
        // Should not panic for valid values
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
        // All valid sizes should pass
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
        // In bounds: addr=0, size=4, mem=65536
        assert!(memory::verify_bounds_check(0, 4, 65536));
        // Exactly at boundary
        assert!(memory::verify_bounds_check(65532, 4, 65536));
        // Out of bounds
        assert!(!memory::verify_bounds_check(65533, 4, 65536));
        // Overflow protection
        assert!(!memory::verify_bounds_check(u32::MAX, 1, u32::MAX));
    }

    #[test]
    fn test_division_trap_guard_length() {
        // Valid: 4+ instructions
        division::verify_trap_guard_length(4);
        division::verify_trap_guard_length(5);
    }

    #[test]
    #[should_panic(expected = "CONTRACT VIOLATION")]
    fn test_division_trap_guard_too_short() {
        division::verify_trap_guard_length(3);
    }
}
