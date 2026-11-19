//! The x86-64 instruction type and its AT&T printer.
//!
//! One variant per instruction FORM the selector can emit. The encoder
//! ([`crate::encoder`]) has one function per form; the printer here writes the
//! form as the AT&T text an assembler reads. The encoding oracles compare the
//! two from outside: `llvm-mc -show-encoding` must assemble the printed text to
//! exactly the encoded bytes (E1, `tests/encoding_llvm_mc.rs`), and iced-x86
//! must decode the emitted bytes back to the printed text (E2,
//! `tests/encoding_iced.rs`).
//!
//! HAND-WRITTEN, and said so: the printer is a second hand-written artefact
//! beside the encoder (REVIEW_2 correction X4). Neither oracle compares against
//! a byte string written in this crate; both compare against tables synth does
//! not write (LLVM's and iced-x86's).

use std::fmt;

/// The sixteen 64-bit general-purpose registers, numbered as the encoding
/// numbers them (bit 3 goes into a REX prefix).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Reg {
    Rax = 0,
    Rcx = 1,
    Rdx = 2,
    Rbx = 3,
    Rsp = 4,
    Rbp = 5,
    Rsi = 6,
    Rdi = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
}

impl Reg {
    /// Every register, in encoding order.
    pub const ALL: [Reg; 16] = [
        Reg::Rax,
        Reg::Rcx,
        Reg::Rdx,
        Reg::Rbx,
        Reg::Rsp,
        Reg::Rbp,
        Reg::Rsi,
        Reg::Rdi,
        Reg::R8,
        Reg::R9,
        Reg::R10,
        Reg::R11,
        Reg::R12,
        Reg::R13,
        Reg::R14,
        Reg::R15,
    ];

    /// The 4-bit encoding number.
    pub fn num(self) -> u8 {
        self as u8
    }

    /// The 32-bit view's AT&T name, without the `%`.
    pub fn name32(self) -> &'static str {
        match self {
            Reg::Rax => "eax",
            Reg::Rcx => "ecx",
            Reg::Rdx => "edx",
            Reg::Rbx => "ebx",
            Reg::Rsp => "esp",
            Reg::Rbp => "ebp",
            Reg::Rsi => "esi",
            Reg::Rdi => "edi",
            Reg::R8 => "r8d",
            Reg::R9 => "r9d",
            Reg::R10 => "r10d",
            Reg::R11 => "r11d",
            Reg::R12 => "r12d",
            Reg::R13 => "r13d",
            Reg::R14 => "r14d",
            Reg::R15 => "r15d",
        }
    }
}

/// One x86-64 instruction, as the selector asks for it.
///
/// Every i32 operation uses the 32-bit operand size, which zeroes bits 63:32
/// of the destination; no i32 value is ever read from the upper half of a
/// register (the upper half of a 32-bit SysV argument is undefined, and the
/// execution oracle poisons it on every call).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Inst {
    /// `movl %src, %dst` — MOV r/m32, r32 (`89 /r`), LLVM's canonical form.
    MovRR32 { dst: Reg, src: Reg },
    /// `addl %src, %dst` — ADD r/m32, r32 (`01 /r`), LLVM's canonical form.
    AddRR32 { dst: Reg, src: Reg },
    /// `retq` — near return (`C3`).
    Ret,
}

impl Inst {
    /// The AT&T text of this instruction, as `llvm-mc` reads it and as iced's
    /// GAS formatter prints it (operand-size suffix on, a space after each
    /// operand separator).
    pub fn att(&self) -> String {
        self.to_string()
    }

    /// Every register this instruction WRITES. The selector's contract — no
    /// callee-saved register and no stack pointer is ever written — is
    /// checked against this in the selector's tests.
    pub fn writes(&self) -> Option<Reg> {
        match *self {
            Inst::MovRR32 { dst, .. } | Inst::AddRR32 { dst, .. } => Some(dst),
            Inst::Ret => None,
        }
    }
}

impl fmt::Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Inst::MovRR32 { dst, src } => write!(f, "movl %{}, %{}", src.name32(), dst.name32()),
            Inst::AddRR32 { dst, src } => write!(f, "addl %{}, %{}", src.name32(), dst.name32()),
            Inst::Ret => write!(f, "retq"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn att_puts_the_source_first() {
        assert_eq!(
            Inst::AddRR32 {
                dst: Reg::R9,
                src: Reg::Rsi
            }
            .att(),
            "addl %esi, %r9d"
        );
        assert_eq!(
            Inst::MovRR32 {
                dst: Reg::Rax,
                src: Reg::Rdi
            }
            .att(),
            "movl %edi, %eax"
        );
        assert_eq!(Inst::Ret.att(), "retq");
    }

    #[test]
    fn register_numbers_are_the_encoding_numbers() {
        for (i, r) in Reg::ALL.iter().enumerate() {
            assert_eq!(r.num() as usize, i);
        }
    }
}
