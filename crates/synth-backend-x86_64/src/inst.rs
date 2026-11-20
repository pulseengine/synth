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
//!
//! IMMEDIATES are printed as lowercase hex with a `0x` prefix, unsigned at the
//! width of the field (`movl $0xffffffff`, `movq $0xffffffffffffffff` for the
//! sign-extended -1): the one spelling both `llvm-mc` reads and iced's GAS
//! formatter is configured to print.

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

    /// The 64-bit AT&T name, without the `%`.
    pub fn name64(self) -> &'static str {
        match self {
            Reg::Rax => "rax",
            Reg::Rcx => "rcx",
            Reg::Rdx => "rdx",
            Reg::Rbx => "rbx",
            Reg::Rsp => "rsp",
            Reg::Rbp => "rbp",
            Reg::Rsi => "rsi",
            Reg::Rdi => "rdi",
            Reg::R8 => "r8",
            Reg::R9 => "r9",
            Reg::R10 => "r10",
            Reg::R11 => "r11",
            Reg::R12 => "r12",
            Reg::R13 => "r13",
            Reg::R14 => "r14",
            Reg::R15 => "r15",
        }
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

    /// The 16-bit view's AT&T name.
    pub fn name16(self) -> &'static str {
        match self {
            Reg::Rax => "ax",
            Reg::Rcx => "cx",
            Reg::Rdx => "dx",
            Reg::Rbx => "bx",
            Reg::Rsp => "sp",
            Reg::Rbp => "bp",
            Reg::Rsi => "si",
            Reg::Rdi => "di",
            Reg::R8 => "r8w",
            Reg::R9 => "r9w",
            Reg::R10 => "r10w",
            Reg::R11 => "r11w",
            Reg::R12 => "r12w",
            Reg::R13 => "r13w",
            Reg::R14 => "r14w",
            Reg::R15 => "r15w",
        }
    }

    /// The low-byte view's AT&T name. `spl, bpl, sil, dil` exist only with a
    /// REX prefix (without one the same numbers name `ah, ch, dh, bh`); the
    /// encoder always emits that prefix for them.
    pub fn name8(self) -> &'static str {
        match self {
            Reg::Rax => "al",
            Reg::Rcx => "cl",
            Reg::Rdx => "dl",
            Reg::Rbx => "bl",
            Reg::Rsp => "spl",
            Reg::Rbp => "bpl",
            Reg::Rsi => "sil",
            Reg::Rdi => "dil",
            Reg::R8 => "r8b",
            Reg::R9 => "r9b",
            Reg::R10 => "r10b",
            Reg::R11 => "r11b",
            Reg::R12 => "r12b",
            Reg::R13 => "r13b",
            Reg::R14 => "r14b",
            Reg::R15 => "r15b",
        }
    }
}

/// Operand size of an integer instruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Size {
    /// 32-bit. Writing a 32-bit register zeroes bits 63:32.
    L,
    /// 64-bit (REX.W).
    Q,
}

impl Size {
    pub const ALL: [Size; 2] = [Size::L, Size::Q];

    /// The AT&T mnemonic suffix.
    pub fn suffix(self) -> char {
        match self {
            Size::L => 'l',
            Size::Q => 'q',
        }
    }

    /// The name of `r` at this size.
    pub fn reg(self, r: Reg) -> &'static str {
        match self {
            Size::L => r.name32(),
            Size::Q => r.name64(),
        }
    }
}

/// The two-register instructions encoded `op r/m, r` (the destination is the
/// ModRM r/m operand, the source the reg operand): LLVM's canonical form for
/// each. `Cmp` and `Test` write only EFLAGS.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AluOp {
    Add,
    Or,
    And,
    Sub,
    Xor,
    Cmp,
    Test,
    Mov,
}

impl AluOp {
    pub const ALL: [AluOp; 8] = [
        AluOp::Add,
        AluOp::Or,
        AluOp::And,
        AluOp::Sub,
        AluOp::Xor,
        AluOp::Cmp,
        AluOp::Test,
        AluOp::Mov,
    ];

    pub fn mnemonic(self) -> &'static str {
        match self {
            AluOp::Add => "add",
            AluOp::Or => "or",
            AluOp::And => "and",
            AluOp::Sub => "sub",
            AluOp::Xor => "xor",
            AluOp::Cmp => "cmp",
            AluOp::Test => "test",
            AluOp::Mov => "mov",
        }
    }

    /// Whether the instruction writes its destination register.
    pub fn writes_dst(self) -> bool {
        !matches!(self, AluOp::Cmp | AluOp::Test)
    }
}

/// Shifts and rotates by `%cl` (`D3 /n`). The CPU masks the count to 5 bits at
/// 32-bit operand size and 6 bits at 64-bit — the wasm rule exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ShiftOp {
    Rol,
    Ror,
    Shl,
    Shr,
    Sar,
}

impl ShiftOp {
    pub const ALL: [ShiftOp; 5] = [
        ShiftOp::Rol,
        ShiftOp::Ror,
        ShiftOp::Shl,
        ShiftOp::Shr,
        ShiftOp::Sar,
    ];

    pub fn mnemonic(self) -> &'static str {
        match self {
            ShiftOp::Rol => "rol",
            ShiftOp::Ror => "ror",
            ShiftOp::Shl => "shl",
            ShiftOp::Shr => "shr",
            ShiftOp::Sar => "sar",
        }
    }
}

/// The condition codes the selector uses, for `setcc` and `cmovcc`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Cond {
    /// Below (unsigned `<`): CF.
    B,
    /// Above or equal (unsigned `>=`).
    Ae,
    /// Equal: ZF.
    E,
    /// Not equal.
    Ne,
    /// Below or equal (unsigned `<=`).
    Be,
    /// Above (unsigned `>`).
    A,
    /// Less (signed `<`).
    L,
    /// Greater or equal (signed `>=`).
    Ge,
    /// Less or equal (signed `<=`).
    Le,
    /// Greater (signed `>`).
    G,
}

impl Cond {
    pub const ALL: [Cond; 10] = [
        Cond::B,
        Cond::Ae,
        Cond::E,
        Cond::Ne,
        Cond::Be,
        Cond::A,
        Cond::L,
        Cond::Ge,
        Cond::Le,
        Cond::G,
    ];

    /// The AT&T suffix (`sete`, `cmovbl`, ...).
    pub fn suffix(self) -> &'static str {
        match self {
            Cond::B => "b",
            Cond::Ae => "ae",
            Cond::E => "e",
            Cond::Ne => "ne",
            Cond::Be => "be",
            Cond::A => "a",
            Cond::L => "l",
            Cond::Ge => "ge",
            Cond::Le => "le",
            Cond::G => "g",
        }
    }
}

/// The widening moves: source view, extension, destination view.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Ext {
    /// `movzbl r/m8, r32` — zero-extend a byte (also zeroes bits 63:32).
    ZxBL,
    /// `movsbl r/m8, r32`.
    SxBL,
    /// `movswl r/m16, r32`.
    SxWL,
    /// `movsbq r/m8, r64`.
    SxBQ,
    /// `movswq r/m16, r64`.
    SxWQ,
    /// `movslq r/m32, r64` (`movsxd`).
    SxLQ,
}

impl Ext {
    pub const ALL: [Ext; 6] = [
        Ext::ZxBL,
        Ext::SxBL,
        Ext::SxWL,
        Ext::SxBQ,
        Ext::SxWQ,
        Ext::SxLQ,
    ];

    pub fn mnemonic(self) -> &'static str {
        match self {
            Ext::ZxBL => "movzbl",
            Ext::SxBL => "movsbl",
            Ext::SxWL => "movswl",
            Ext::SxBQ => "movsbq",
            Ext::SxWQ => "movswq",
            Ext::SxLQ => "movslq",
        }
    }

    /// The source register's name at this form's source width.
    pub fn src_name(self, r: Reg) -> &'static str {
        match self {
            Ext::ZxBL | Ext::SxBL | Ext::SxBQ => r.name8(),
            Ext::SxWL | Ext::SxWQ => r.name16(),
            Ext::SxLQ => r.name32(),
        }
    }

    /// The destination's operand size.
    pub fn dst_size(self) -> Size {
        match self {
            Ext::ZxBL | Ext::SxBL | Ext::SxWL => Size::L,
            Ext::SxBQ | Ext::SxWQ | Ext::SxLQ => Size::Q,
        }
    }

    /// The source is a byte register (so `spl..dil` need a REX prefix).
    pub fn src_is_byte(self) -> bool {
        matches!(self, Ext::ZxBL | Ext::SxBL | Ext::SxBQ)
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
    /// `op{l,q} %src, %dst` — `op r/m, r`, LLVM's canonical register form.
    Alu {
        op: AluOp,
        size: Size,
        dst: Reg,
        src: Reg,
    },
    /// `imul{l,q} %src, %dst` — IMUL r, r/m (`0F AF /r`). The low half of the
    /// product, which is wasm's `mul` for either signedness.
    Imul { size: Size, dst: Reg, src: Reg },
    /// `op{l,q} %cl, %dst` — shift or rotate by the count in `cl` (`D3 /n`).
    ShiftCl { op: ShiftOp, size: Size, dst: Reg },
    /// `setCC %dst8` — write 0 or 1 to the LOW BYTE of `dst` (`0F 9x /0`).
    /// Bits 63:8 are unchanged, so it is always followed by a `movzbl`.
    SetCc { cond: Cond, dst: Reg },
    /// `cmovCC{l,q} %src, %dst` — `0F 4x /r`. At 32-bit size the destination's
    /// upper half is zeroed whether or not the move happens.
    Cmov {
        cond: Cond,
        size: Size,
        dst: Reg,
        src: Reg,
    },
    /// A widening move, see [`Ext`].
    Movx { ext: Ext, dst: Reg, src: Reg },
    /// `movl $imm32, %dst32` — `B8+r id`. Zeroes bits 63:32.
    MovImm32 { dst: Reg, imm: u32 },
    /// `movq $imm32, %dst64` — `REX.W C7 /0 id`, the immediate SIGN-extended
    /// to 64 bits.
    MovImmSx { dst: Reg, imm: i32 },
    /// `movabsq $imm64, %dst64` — `REX.W B8+r io`.
    MovAbs { dst: Reg, imm: u64 },
    /// `retq` — near return (`C3`).
    Ret,
}

impl Inst {
    /// `movl %src, %dst`.
    pub fn mov32(dst: Reg, src: Reg) -> Inst {
        Inst::Alu {
            op: AluOp::Mov,
            size: Size::L,
            dst,
            src,
        }
    }

    /// The AT&T text of this instruction, as `llvm-mc` reads it and as iced's
    /// GAS formatter prints it (operand-size suffix on, a space after each
    /// operand separator).
    pub fn att(&self) -> String {
        self.to_string()
    }

    /// The register this instruction WRITES, if any (`cmp`/`test` write only
    /// EFLAGS). The selector's contract — no callee-saved register and no
    /// stack pointer is ever written — is checked against this in the
    /// selector's tests.
    pub fn writes(&self) -> Option<Reg> {
        match *self {
            Inst::Alu { op, dst, .. } => op.writes_dst().then_some(dst),
            Inst::Imul { dst, .. }
            | Inst::ShiftCl { dst, .. }
            | Inst::SetCc { dst, .. }
            | Inst::Cmov { dst, .. }
            | Inst::Movx { dst, .. }
            | Inst::MovImm32 { dst, .. }
            | Inst::MovImmSx { dst, .. }
            | Inst::MovAbs { dst, .. } => Some(dst),
            Inst::Ret => None,
        }
    }
}

impl fmt::Display for Inst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Inst::Alu { op, size, dst, src } => write!(
                f,
                "{}{} %{}, %{}",
                op.mnemonic(),
                size.suffix(),
                size.reg(src),
                size.reg(dst)
            ),
            Inst::Imul { size, dst, src } => write!(
                f,
                "imul{} %{}, %{}",
                size.suffix(),
                size.reg(src),
                size.reg(dst)
            ),
            Inst::ShiftCl { op, size, dst } => write!(
                f,
                "{}{} %cl, %{}",
                op.mnemonic(),
                size.suffix(),
                size.reg(dst)
            ),
            Inst::SetCc { cond, dst } => write!(f, "set{} %{}", cond.suffix(), dst.name8()),
            Inst::Cmov {
                cond,
                size,
                dst,
                src,
            } => write!(
                f,
                "cmov{}{} %{}, %{}",
                cond.suffix(),
                size.suffix(),
                size.reg(src),
                size.reg(dst)
            ),
            Inst::Movx { ext, dst, src } => write!(
                f,
                "{} %{}, %{}",
                ext.mnemonic(),
                ext.src_name(src),
                ext.dst_size().reg(dst)
            ),
            Inst::MovImm32 { dst, imm } => write!(f, "movl $0x{imm:x}, %{}", dst.name32()),
            Inst::MovImmSx { dst, imm } => {
                write!(f, "movq $0x{:x}, %{}", imm as i64 as u64, dst.name64())
            }
            Inst::MovAbs { dst, imm } => write!(f, "movabsq $0x{imm:x}, %{}", dst.name64()),
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
            Inst::Alu {
                op: AluOp::Add,
                size: Size::L,
                dst: Reg::R9,
                src: Reg::Rsi
            }
            .att(),
            "addl %esi, %r9d"
        );
        assert_eq!(Inst::mov32(Reg::Rax, Reg::Rdi).att(), "movl %edi, %eax");
        assert_eq!(
            Inst::Alu {
                op: AluOp::Sub,
                size: Size::Q,
                dst: Reg::Rax,
                src: Reg::R11
            }
            .att(),
            "subq %r11, %rax"
        );
        assert_eq!(Inst::Ret.att(), "retq");
    }

    #[test]
    fn each_form_prints_its_views() {
        assert_eq!(
            Inst::ShiftCl {
                op: ShiftOp::Sar,
                size: Size::Q,
                dst: Reg::R10
            }
            .att(),
            "sarq %cl, %r10"
        );
        assert_eq!(
            Inst::SetCc {
                cond: Cond::Ae,
                dst: Reg::Rdi
            }
            .att(),
            "setae %dil"
        );
        assert_eq!(
            Inst::Cmov {
                cond: Cond::E,
                size: Size::L,
                dst: Reg::Rax,
                src: Reg::Rsi
            }
            .att(),
            "cmovel %esi, %eax"
        );
        assert_eq!(
            Inst::Movx {
                ext: Ext::SxWQ,
                dst: Reg::Rax,
                src: Reg::R9
            }
            .att(),
            "movswq %r9w, %rax"
        );
        assert_eq!(
            Inst::Movx {
                ext: Ext::SxLQ,
                dst: Reg::R11,
                src: Reg::Rdi
            }
            .att(),
            "movslq %edi, %r11"
        );
        assert_eq!(
            Inst::MovImm32 {
                dst: Reg::R10,
                imm: u32::MAX
            }
            .att(),
            "movl $0xffffffff, %r10d"
        );
        assert_eq!(
            Inst::MovImmSx {
                dst: Reg::Rax,
                imm: -1
            }
            .att(),
            "movq $0xffffffffffffffff, %rax"
        );
        assert_eq!(
            Inst::MovAbs {
                dst: Reg::Rax,
                imm: 0x1122_3344_5566_7788
            }
            .att(),
            "movabsq $0x1122334455667788, %rax"
        );
    }

    #[test]
    fn cmp_and_test_write_no_register() {
        for op in [AluOp::Cmp, AluOp::Test] {
            assert_eq!(
                Inst::Alu {
                    op,
                    size: Size::L,
                    dst: Reg::Rbx,
                    src: Reg::Rax
                }
                .writes(),
                None
            );
        }
        assert_eq!(Inst::mov32(Reg::Rax, Reg::Rdi).writes(), Some(Reg::Rax));
    }

    #[test]
    fn register_numbers_are_the_encoding_numbers() {
        for (i, r) in Reg::ALL.iter().enumerate() {
            assert_eq!(r.num() as usize, i);
        }
    }
}
