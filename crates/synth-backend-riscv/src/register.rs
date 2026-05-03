//! RISC-V register file (RV32 / RV64 share the same 32 GPR namespace).
//!
//! ABI names follow the RISC-V psABI:
//! - `x0` = zero (hardwired)
//! - `x1` = ra (return address)
//! - `x2` = sp (stack pointer)
//! - `x3` = gp (global pointer)
//! - `x4` = tp (thread pointer)
//! - `x5..7`, `x28..31` = t0..t6 (temporaries, caller-saved)
//! - `x8..9`, `x18..27` = s0..s11 (saved, callee-saved)
//! - `x10..17` = a0..a7 (argument / return)
//!
//! For floating-point variants (F/D extensions) we'd add f0..f31 in a separate
//! `FReg` enum; this skeleton focuses on integer registers.

use std::fmt;

/// RISC-V general-purpose register (x0..x31).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[repr(u8)]
pub enum Reg {
    X0 = 0,   // zero
    X1 = 1,   // ra
    X2 = 2,   // sp
    X3 = 3,   // gp
    X4 = 4,   // tp
    X5 = 5,   // t0
    X6 = 6,   // t1
    X7 = 7,   // t2
    X8 = 8,   // s0/fp
    X9 = 9,   // s1
    X10 = 10, // a0
    X11 = 11, // a1
    X12 = 12, // a2
    X13 = 13, // a3
    X14 = 14, // a4
    X15 = 15, // a5
    X16 = 16, // a6
    X17 = 17, // a7
    X18 = 18, // s2
    X19 = 19, // s3
    X20 = 20, // s4
    X21 = 21, // s5
    X22 = 22, // s6
    X23 = 23, // s7
    X24 = 24, // s8
    X25 = 25, // s9
    X26 = 26, // s10
    X27 = 27, // s11
    X28 = 28, // t3
    X29 = 29, // t4
    X30 = 30, // t5
    X31 = 31, // t6
}

impl Reg {
    /// Numeric encoding (5-bit field).
    pub fn num(self) -> u8 {
        self as u8
    }

    /// Build from the numeric encoding. Returns `None` for values >= 32.
    pub fn from_num(n: u8) -> Option<Self> {
        if n >= 32 {
            return None;
        }
        // SAFETY: `Reg` is `#[repr(u8)]` with a contiguous 0..32 range.
        unsafe { Some(std::mem::transmute::<u8, Reg>(n)) }
    }

    /// ABI name (zero, ra, sp, ...).
    pub fn abi_name(self) -> &'static str {
        match self {
            Reg::X0 => "zero",
            Reg::X1 => "ra",
            Reg::X2 => "sp",
            Reg::X3 => "gp",
            Reg::X4 => "tp",
            Reg::X5 => "t0",
            Reg::X6 => "t1",
            Reg::X7 => "t2",
            Reg::X8 => "s0",
            Reg::X9 => "s1",
            Reg::X10 => "a0",
            Reg::X11 => "a1",
            Reg::X12 => "a2",
            Reg::X13 => "a3",
            Reg::X14 => "a4",
            Reg::X15 => "a5",
            Reg::X16 => "a6",
            Reg::X17 => "a7",
            Reg::X18 => "s2",
            Reg::X19 => "s3",
            Reg::X20 => "s4",
            Reg::X21 => "s5",
            Reg::X22 => "s6",
            Reg::X23 => "s7",
            Reg::X24 => "s8",
            Reg::X25 => "s9",
            Reg::X26 => "s10",
            Reg::X27 => "s11",
            Reg::X28 => "t3",
            Reg::X29 => "t4",
            Reg::X30 => "t5",
            Reg::X31 => "t6",
        }
    }

    /// Constants for the most-used ABI registers — improves call sites.
    pub const ZERO: Reg = Reg::X0;
    pub const RA: Reg = Reg::X1;
    pub const SP: Reg = Reg::X2;
    pub const GP: Reg = Reg::X3;
    pub const TP: Reg = Reg::X4;
    pub const FP: Reg = Reg::X8; // s0 = fp
    pub const A0: Reg = Reg::X10;
    pub const A1: Reg = Reg::X11;
    pub const A2: Reg = Reg::X12;
    pub const A3: Reg = Reg::X13;
    pub const A4: Reg = Reg::X14;
    pub const A5: Reg = Reg::X15;
    pub const A6: Reg = Reg::X16;
    pub const A7: Reg = Reg::X17;
    pub const T0: Reg = Reg::X5;
    pub const T1: Reg = Reg::X6;
    pub const T2: Reg = Reg::X7;
    pub const T3: Reg = Reg::X28;
    pub const T4: Reg = Reg::X29;
    pub const T5: Reg = Reg::X30;
    pub const T6: Reg = Reg::X31;
    pub const S0: Reg = Reg::X8; // also fp
    pub const S1: Reg = Reg::X9;
    pub const S2: Reg = Reg::X18;
    pub const S3: Reg = Reg::X19;
    pub const S4: Reg = Reg::X20;
    pub const S5: Reg = Reg::X21;
    pub const S6: Reg = Reg::X22;
    pub const S7: Reg = Reg::X23;
    pub const S8: Reg = Reg::X24;
    pub const S9: Reg = Reg::X25;
    pub const S10: Reg = Reg::X26;
    pub const S11: Reg = Reg::X27;

    /// Whether this register is callee-saved per the standard RV psABI.
    /// Callee-saved: sp, gp, tp, s0..s11.
    pub fn is_callee_saved(self) -> bool {
        matches!(
            self,
            Reg::X2
                | Reg::X3
                | Reg::X4
                | Reg::X8
                | Reg::X9
                | Reg::X18
                | Reg::X19
                | Reg::X20
                | Reg::X21
                | Reg::X22
                | Reg::X23
                | Reg::X24
                | Reg::X25
                | Reg::X26
                | Reg::X27
        )
    }

    /// First N argument registers (a0..a(n-1)). Capped at 8 (a0..a7).
    pub fn arg_regs(n: usize) -> Vec<Reg> {
        let cap = n.min(8);
        (0..cap)
            .map(|i| Reg::from_num((10 + i) as u8).unwrap())
            .collect()
    }
}

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.abi_name())
    }
}

/// Coarse register class for vreg-allocator hints.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RegClass {
    /// 32-bit GPR (the only class implemented in this skeleton).
    Gpr,
    /// 64-bit GPR — present on RV64 only.
    Gpr64,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip_num() {
        for i in 0..32u8 {
            let r = Reg::from_num(i).unwrap();
            assert_eq!(r.num(), i);
        }
    }

    #[test]
    fn out_of_range_num() {
        assert!(Reg::from_num(32).is_none());
        assert!(Reg::from_num(255).is_none());
    }

    #[test]
    fn abi_aliases() {
        assert_eq!(Reg::ZERO.abi_name(), "zero");
        assert_eq!(Reg::RA.abi_name(), "ra");
        assert_eq!(Reg::SP.abi_name(), "sp");
        assert_eq!(Reg::A0.abi_name(), "a0");
        assert_eq!(Reg::A7.abi_name(), "a7");
        assert_eq!(Reg::S0.abi_name(), "s0");
    }

    #[test]
    fn callee_saved_set() {
        // sp + gp + tp + s0..s11 = 15 registers
        let count = (0..32u8)
            .filter(|&i| Reg::from_num(i).unwrap().is_callee_saved())
            .count();
        assert_eq!(count, 15);
    }

    #[test]
    fn arg_regs_capped_at_8() {
        let r = Reg::arg_regs(20);
        assert_eq!(r.len(), 8);
        assert_eq!(r[0], Reg::A0);
        assert_eq!(r[7], Reg::A7);
    }

    #[test]
    fn arg_regs_partial() {
        let r = Reg::arg_regs(3);
        assert_eq!(r, vec![Reg::A0, Reg::A1, Reg::A2]);
    }
}
