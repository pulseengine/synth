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

    /// The condition that holds exactly when `self` does not.
    pub fn negate(self) -> Cond {
        match self {
            Cond::B => Cond::Ae,
            Cond::Ae => Cond::B,
            Cond::E => Cond::Ne,
            Cond::Ne => Cond::E,
            Cond::Be => Cond::A,
            Cond::A => Cond::Be,
            Cond::L => Cond::Ge,
            Cond::Ge => Cond::L,
            Cond::Le => Cond::G,
            Cond::G => Cond::Le,
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

/// A memory operand `disp(%base)`: a base register and a signed 32-bit
/// displacement, no index. The encoder picks the shortest of the three
/// displacement widths (none, 8-bit, 32-bit), as LLVM does; `rsp`/`r12` as a
/// base need a SIB byte and `rbp`/`r13` always carry a displacement.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Mem {
    pub base: Reg,
    pub disp: i32,
}

impl fmt::Display for Mem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let base = self.base.name64();
        match self.disp {
            0 => write!(f, "(%{base})"),
            d if d < 0 => write!(f, "-0x{:x}(%{base})", d.unsigned_abs()),
            d => write!(f, "0x{d:x}(%{base})"),
        }
    }
}

/// The instructions encoded `op r/m, imm` (`83 /n ib`, `81 /n id`, and the
/// accumulator short form): the immediate is sign-extended to the operand
/// size. `Cmp` writes only EFLAGS.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ImmOp {
    Add,
    Or,
    And,
    Sub,
    Xor,
    Cmp,
}

impl ImmOp {
    pub const ALL: [ImmOp; 6] = [
        ImmOp::Add,
        ImmOp::Or,
        ImmOp::And,
        ImmOp::Sub,
        ImmOp::Xor,
        ImmOp::Cmp,
    ];

    pub fn mnemonic(self) -> &'static str {
        match self {
            ImmOp::Add => "add",
            ImmOp::Or => "or",
            ImmOp::And => "and",
            ImmOp::Sub => "sub",
            ImmOp::Xor => "xor",
            ImmOp::Cmp => "cmp",
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
    /// `mov{l,q} disp(%base), %dst` — MOV r, r/m (`8B /r`). At 32-bit size the
    /// destination's upper half is zeroed.
    Load { size: Size, dst: Reg, mem: Mem },
    /// `mov{l,q} %src, disp(%base)` — MOV r/m, r (`89 /r`). At 32-bit size
    /// four bytes are written.
    Store { size: Size, src: Reg, mem: Mem },
    /// `op{l,q} $imm, %dst` — the immediate sign-extended to the operand size.
    AluImm {
        op: ImmOp,
        size: Size,
        dst: Reg,
        imm: i32,
    },
    /// `pushq %reg` (`50+r`): `rsp -= 8`, then store.
    Push { reg: Reg },
    /// `popq %reg` (`58+r`): load, then `rsp += 8`.
    Pop { reg: Reg },
    /// `cltd` / `cqto` (`99`): sign-extend `eax` into `edx` (or `rax` into
    /// `rdx`), the dividend of a signed divide.
    Cdq { size: Size },
    /// `div{l,q} %src` / `idiv{l,q} %src` (`F7 /6`, `F7 /7`): divide
    /// `edx:eax` (`rdx:rax`) by `src`; quotient to `eax`, remainder to `edx`.
    /// RAISES #DE on a zero divisor and on a quotient that does not fit, so
    /// the selector never emits it without its guards.
    Div { signed: bool, size: Size, src: Reg },
    /// `bsf{l,q} %src, %dst` / `bsr{l,q} %src, %dst` (`0F BC /r`, `0F BD
    /// /r`): the index of the lowest (`bsf`) or highest (`bsr`) set bit. ZF is
    /// set when `src` is zero, and then `dst` is NOT a defined value.
    BitScan {
        reverse: bool,
        size: Size,
        dst: Reg,
        src: Reg,
    },
    /// `jCC` with a 32-bit displacement (`0F 8x cd`), ALWAYS: there is no
    /// short form and no relaxation, so the length is 6 whatever the target.
    /// `rel` is relative to the END of this instruction.
    Jcc { cond: Cond, rel: i32 },
    /// `jmp` with a 32-bit displacement (`E9 cd`), ALWAYS: no short form, no
    /// relaxation, so the length is 5 whatever the target. `rel` is relative
    /// to the END of this instruction.
    Jmp { rel: i32 },
    /// `ud2` (`0F 0B`) — the trap. The only trapping instruction the selector
    /// emits on purpose.
    Ud2,
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

    /// Every register this instruction WRITES, implicit ones included
    /// (`cmp`/`test` write only EFLAGS; `push`/`pop` move `rsp`; a divide
    /// writes `rax` and `rdx`). The selector's contract — which registers may
    /// be written, and by which instructions — is checked against this in the
    /// selector's tests.
    pub fn writes(&self) -> Vec<Reg> {
        match *self {
            Inst::Alu { op, dst, .. } => {
                if op.writes_dst() {
                    vec![dst]
                } else {
                    vec![]
                }
            }
            Inst::AluImm { op, dst, .. } => {
                if op == ImmOp::Cmp {
                    vec![]
                } else {
                    vec![dst]
                }
            }
            Inst::Imul { dst, .. }
            | Inst::ShiftCl { dst, .. }
            | Inst::SetCc { dst, .. }
            | Inst::Cmov { dst, .. }
            | Inst::Movx { dst, .. }
            | Inst::MovImm32 { dst, .. }
            | Inst::MovImmSx { dst, .. }
            | Inst::MovAbs { dst, .. }
            | Inst::Load { dst, .. }
            | Inst::BitScan { dst, .. } => vec![dst],
            Inst::Push { .. } => vec![Reg::Rsp],
            Inst::Pop { reg } => vec![reg, Reg::Rsp],
            Inst::Cdq { .. } => vec![Reg::Rdx],
            Inst::Div { .. } => vec![Reg::Rax, Reg::Rdx],
            Inst::Store { .. } | Inst::Jcc { .. } | Inst::Jmp { .. } | Inst::Ud2 | Inst::Ret => {
                vec![]
            }
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
            Inst::Load { size, dst, mem } => {
                write!(f, "mov{} {mem}, %{}", size.suffix(), size.reg(dst))
            }
            Inst::Store { size, src, mem } => {
                write!(f, "mov{} %{}, {mem}", size.suffix(), size.reg(src))
            }
            Inst::AluImm { op, size, dst, imm } => {
                // Unsigned at the operand width, like every other immediate.
                let bits = match size {
                    Size::L => u64::from(imm as u32),
                    Size::Q => imm as i64 as u64,
                };
                write!(
                    f,
                    "{}{} $0x{bits:x}, %{}",
                    op.mnemonic(),
                    size.suffix(),
                    size.reg(dst)
                )
            }
            Inst::Push { reg } => write!(f, "pushq %{}", reg.name64()),
            Inst::Pop { reg } => write!(f, "popq %{}", reg.name64()),
            Inst::Cdq { size } => match size {
                Size::L => write!(f, "cltd"),
                Size::Q => write!(f, "cqto"),
            },
            Inst::Div { signed, size, src } => write!(
                f,
                "{}div{} %{}",
                if signed { "i" } else { "" },
                size.suffix(),
                size.reg(src)
            ),
            Inst::BitScan {
                reverse,
                size,
                dst,
                src,
            } => write!(
                f,
                "bs{}{} %{}, %{}",
                if reverse { 'r' } else { 'f' },
                size.suffix(),
                size.reg(src),
                size.reg(dst)
            ),
            // `.` is the address of the instruction itself, which is 6 bytes
            // long; `{disp32}` asks the assembler for the 32-bit form.
            Inst::Jcc { cond, rel } => {
                let from_start = i64::from(rel) + 6;
                if from_start < 0 {
                    write!(f, "{{disp32}} j{} .-0x{:x}", cond.suffix(), -from_start)
                } else {
                    write!(f, "{{disp32}} j{} .+0x{from_start:x}", cond.suffix())
                }
            }
            // The same for `jmp`, which is 5 bytes long.
            Inst::Jmp { rel } => {
                let from_start = i64::from(rel) + 5;
                if from_start < 0 {
                    write!(f, "{{disp32}} jmp .-0x{:x}", -from_start)
                } else {
                    write!(f, "{{disp32}} jmp .+0x{from_start:x}")
                }
            }
            Inst::Ud2 => write!(f, "ud2"),
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
    fn frame_division_and_branch_forms_print_as_att() {
        let slot = Mem {
            base: Reg::Rbp,
            disp: -8,
        };
        assert_eq!(
            Inst::Load {
                size: Size::Q,
                dst: Reg::Rax,
                mem: slot
            }
            .att(),
            "movq -0x8(%rbp), %rax"
        );
        assert_eq!(
            Inst::Store {
                size: Size::L,
                src: Reg::Rdi,
                mem: Mem {
                    base: Reg::R12,
                    disp: 0
                }
            }
            .att(),
            "movl %edi, (%r12)"
        );
        assert_eq!(
            Inst::Store {
                size: Size::Q,
                src: Reg::R9,
                mem: Mem {
                    base: Reg::Rsp,
                    disp: 0x100
                }
            }
            .att(),
            "movq %r9, 0x100(%rsp)"
        );
        assert_eq!(
            Inst::AluImm {
                op: ImmOp::Sub,
                size: Size::Q,
                dst: Reg::Rsp,
                imm: 16
            }
            .att(),
            "subq $0x10, %rsp"
        );
        // A negative immediate prints unsigned at the operand width.
        assert_eq!(
            Inst::AluImm {
                op: ImmOp::Cmp,
                size: Size::L,
                dst: Reg::Rsi,
                imm: -1
            }
            .att(),
            "cmpl $0xffffffff, %esi"
        );
        assert_eq!(
            Inst::AluImm {
                op: ImmOp::Cmp,
                size: Size::Q,
                dst: Reg::Rsi,
                imm: -1
            }
            .att(),
            "cmpq $0xffffffffffffffff, %rsi"
        );
        assert_eq!(Inst::Push { reg: Reg::Rbp }.att(), "pushq %rbp");
        assert_eq!(Inst::Pop { reg: Reg::R13 }.att(), "popq %r13");
        assert_eq!(Inst::Cdq { size: Size::L }.att(), "cltd");
        assert_eq!(Inst::Cdq { size: Size::Q }.att(), "cqto");
        assert_eq!(
            Inst::Div {
                signed: true,
                size: Size::L,
                src: Reg::Rsi
            }
            .att(),
            "idivl %esi"
        );
        assert_eq!(
            Inst::Div {
                signed: false,
                size: Size::Q,
                src: Reg::R8
            }
            .att(),
            "divq %r8"
        );
        assert_eq!(
            Inst::BitScan {
                reverse: true,
                size: Size::L,
                dst: Reg::Rax,
                src: Reg::Rsi
            }
            .att(),
            "bsrl %esi, %eax"
        );
        assert_eq!(
            Inst::BitScan {
                reverse: false,
                size: Size::Q,
                dst: Reg::R10,
                src: Reg::R9
            }
            .att(),
            "bsfq %r9, %r10"
        );
        // rel is from the END of the 6-byte instruction; `.` is its start.
        assert_eq!(
            Inst::Jcc {
                cond: Cond::Ne,
                rel: 2
            }
            .att(),
            "{disp32} jne .+0x8"
        );
        assert_eq!(
            Inst::Jcc {
                cond: Cond::E,
                rel: -6
            }
            .att(),
            "{disp32} je .+0x0"
        );
        assert_eq!(
            Inst::Jcc {
                cond: Cond::B,
                rel: -16
            }
            .att(),
            "{disp32} jb .-0xa"
        );
        assert_eq!(Inst::Ud2.att(), "ud2");
        assert_eq!(Inst::Jmp { rel: 0 }.att(), "{disp32} jmp .+0x5");
        assert_eq!(Inst::Jmp { rel: -5 }.att(), "{disp32} jmp .+0x0");
        assert_eq!(Inst::Jmp { rel: -16 }.att(), "{disp32} jmp .-0xb");
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
                vec![]
            );
        }
        assert_eq!(Inst::mov32(Reg::Rax, Reg::Rdi).writes(), vec![Reg::Rax]);
        assert!(
            Inst::AluImm {
                op: ImmOp::Cmp,
                size: Size::Q,
                dst: Reg::Rbx,
                imm: -1
            }
            .writes()
            .is_empty()
        );
        assert_eq!(
            Inst::Div {
                signed: true,
                size: Size::L,
                src: Reg::Rsi
            }
            .writes(),
            vec![Reg::Rax, Reg::Rdx]
        );
        assert_eq!(
            Inst::Pop { reg: Reg::Rbp }.writes(),
            vec![Reg::Rbp, Reg::Rsp]
        );
    }

    /// x86 pairs each condition with its negation in the low opcode bit.
    #[test]
    fn negate_flips_the_low_condition_bit() {
        for c in Cond::ALL {
            assert_eq!(c.negate().negate(), c);
            let (a, b) = (
                crate::encoder::encode(&Inst::Jcc { cond: c, rel: 0 }),
                crate::encoder::encode(&Inst::Jcc {
                    cond: c.negate(),
                    rel: 0,
                }),
            );
            assert_eq!(a[1] ^ b[1], 1, "{c:?}");
        }
    }

    #[test]
    fn register_numbers_are_the_encoding_numbers() {
        for (i, r) in Reg::ALL.iter().enumerate() {
            assert_eq!(r.num() as usize, i);
        }
    }
}
