//! The ARM register contract, declared once (RQ-68-ONESOURCE, #1270).
//!
//! Every register SET the ARM selectors, the allocator and their checkers
//! agree on lives here, and every other file references it. The failure this
//! module exists to prevent is not a wrong value — each copy it replaces was
//! right when written — but a set declared N times, where a fix changes N-1 of
//! them and each missed copy is found only when a different oracle fails
//! (#1204 needed three callee-saved copies changed, found by three oracles).
//!
//! Composite sets are DERIVED with [`concat`] rather than restated, so the
//! members of, say, the direct prologue cannot drift from the callee-saved
//! pool they are built from.

use crate::rules::Reg;

/// Concatenate two register arrays at compile time. `C` must equal `A + B`;
/// a mismatch is a compile error (const evaluation panics), not a truncation.
const fn concat<const A: usize, const B: usize, const C: usize>(
    a: [Reg; A],
    b: [Reg; B],
) -> [Reg; C] {
    assert!(A + B == C, "reg_contract::concat: length mismatch");
    let mut out = [Reg::R0; C];
    let mut i = 0;
    while i < A {
        out[i] = a[i];
        i += 1;
    }
    let mut j = 0;
    while j < B {
        out[A + j] = b[j];
        j += 1;
    }
    out
}

/// The callee-saved registers inside the allocatable pool (AAPCS r4-r8). R9,
/// R10 and R11 are callee-saved too, but the register contract reserves them;
/// see [`RESERVED_CALLEE_SAVED`].
pub const CALLEE_SAVED_POOL: [Reg; 5] = [Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8];

/// The callee-saved registers the register contract RESERVES: R9 (globals
/// base), R10 (linear-memory size), R11 (linear-memory base). Never in the
/// allocatable pool — but the optimized path does WRITE them (the i64 pair
/// table's (R8,R9)/(R10,R11), base-CSE's R11, synthetic local 255), so any
/// function that defines one must save it (#1204).
pub const RESERVED_CALLEE_SAVED: [Reg; 3] = [Reg::R9, Reg::R10, Reg::R11];

/// Every AAPCS callee-saved core register (r4-r11): the pool's callee-saved
/// half followed by the reserved half.
pub const AAPCS_CALLEE_SAVED: [Reg; 8] = concat(CALLEE_SAVED_POOL, RESERVED_CALLEE_SAVED);

/// The direct selector's (`select_with_stack`) fixed prologue:
/// `push {r4-r8, lr}`. Six registers — an even count, so the 8-byte AAPCS SP
/// alignment holds at every call site once the frame is rounded to 8.
pub const DIRECT_PROLOGUE_PUSH: [Reg; 6] = concat(CALLEE_SAVED_POOL, [Reg::LR]);

/// The matching epilogue: `pop {r4-r8, pc}` restores and returns.
pub const DIRECT_EPILOGUE_POP: [Reg; 6] = concat(CALLEE_SAVED_POOL, [Reg::PC]);

/// Bytes the direct prologue moves SP by. Incoming stack-passed parameters are
/// addressed `[sp, frame_size + DIRECT_PROLOGUE_BYTES + nsaa_k]` (#359/#503);
/// before #1273 this was a literal `24` beside a comment naming the push, so a
/// change to the push list would have shifted every stack-param read silently.
/// Deriving it from [`DIRECT_PROLOGUE_PUSH`] makes the two move together.
///
/// Measured before this constant existed (#1273, v0.68 base): the offset was
/// LATENT, not live — over 133 corpus modules on the direct path, all 349
/// functions that address `[sp, …]` begin with exactly this 24-byte push, and a
/// unicorn-vs-wasmtime differential with stack parameters read inside loops,
/// branch arms and beside i64 locals matched on every vector.
pub const DIRECT_PROLOGUE_BYTES: i32 = 4 * DIRECT_PROLOGUE_PUSH.len() as i32;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aapcs_callee_saved_is_r4_through_r11_in_order() {
        assert_eq!(
            AAPCS_CALLEE_SAVED,
            [
                Reg::R4,
                Reg::R5,
                Reg::R6,
                Reg::R7,
                Reg::R8,
                Reg::R9,
                Reg::R10,
                Reg::R11
            ]
        );
    }

    #[test]
    fn direct_prologue_is_the_callee_saved_pool_plus_lr() {
        assert_eq!(
            DIRECT_PROLOGUE_PUSH,
            [Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::LR]
        );
        assert_eq!(
            DIRECT_EPILOGUE_POP,
            [Reg::R4, Reg::R5, Reg::R6, Reg::R7, Reg::R8, Reg::PC]
        );
        assert_eq!(DIRECT_PROLOGUE_BYTES, 24);
        // AAPCS: an even push keeps SP 8-byte aligned.
        assert!(DIRECT_PROLOGUE_PUSH.len().is_multiple_of(2));
    }
}
