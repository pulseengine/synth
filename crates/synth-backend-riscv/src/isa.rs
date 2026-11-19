//! RQ-91-RV32ISA (Refs #1744): the RV32 target's extension set, and the
//! check that every emitted instruction lies inside it.
//!
//! Before this, `--target` named a profile that nothing downstream read:
//! `rv32i`, `rv32imc`, `rv32imac` and `esp32c3` produced byte-identical
//! objects, so `rv32i` shipped `mul`/`remu` (M extension) and every object
//! claimed RVC in `e_flags`.
//!
//! What the backend emits, per extension (measured on the selector's op set,
//! [`RiscVOp`]):
//! - **I** (+ Zicsr): everything except the eight M ops below.
//! - **M**: `mul`/`mulh`/`mulhsu`/`mulhu`/`div`/`divu`/`rem`/`remu` — from
//!   `i32.mul`, `i32.div_*`/`rem_*`, `i64.mul` (the limb product) and
//!   `i64.popcnt` (its SWAR byte-sum collapse multiplies; `i32.popcnt` is
//!   not lowered on RV32 at all).
//! - **A**: nothing. [`RiscVOp`] has no LR/SC/AMO variant, and every wasm
//!   atomic operator is declined before selection (the decoder loud-skips the
//!   function; a `shared` memory is refused outright, #1315). So a profile
//!   without A loses no accepted input, and atomics are refused on EVERY
//!   profile, not only on one without A.
//! - **C**: nothing. The encoder emits only 32-bit forms, which every RV32
//!   core executes, so C changes only the `e_flags` RVC bit.
//! - **F/D**: nothing. Floats are declined on this backend.
//!
//! A profile without M REFUSES a function whose selection contains an M op
//! (the check runs on the emitted stream, so no wasm op that lowers through a
//! multiply can slip past a per-op list). Refusal is the smallest correct
//! option: a software multiply/divide is a data-dependent loop with its own
//! trap sequence and WCET story, and a libgcc helper call (`__mulsi3`,
//! `__udivsi3`, ...) clobbers every caller-saved register at a site the
//! selector does not treat as a call, and needs a runtime library the
//! self-contained image does not link.

use synth_core::target::{IsaVariant, TargetSpec};

use crate::riscv_op::RiscVOp;

/// A RISC-V standard extension this backend distinguishes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Extension {
    /// The base integer ISA (with Zicsr, which the trap/startup code needs).
    I,
    /// Integer multiply/divide.
    M,
    /// Atomics.
    A,
    /// Compressed instructions.
    C,
}

impl Extension {
    pub fn letter(self) -> char {
        match self {
            Extension::I => 'i',
            Extension::M => 'm',
            Extension::A => 'a',
            Extension::C => 'c',
        }
    }
}

/// The extension set a RISC-V target declares.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Rv32Profile {
    pub m: bool,
    pub a: bool,
    pub c: bool,
}

/// `e_flags` bit: the object may contain compressed instructions.
pub const EF_RISCV_RVC: u32 = 0x1;

impl Rv32Profile {
    /// The default profile, RV32IMAC: the one every object was emitted for
    /// before profiles were read. Its `e_flags` are the historical `0x1`.
    pub const IMAC: Rv32Profile = Rv32Profile {
        m: true,
        a: true,
        c: true,
    };

    /// Parse an ISA extension string (`i`, `im`, `imc`, `imac`, `gc`, ...).
    /// `g` is `imafd`. The base `i` (or `g`) must come first; unknown letters
    /// and duplicates are refused rather than ignored.
    pub fn from_extensions(ext: &str) -> Result<Self, String> {
        let mut chars = ext.chars();
        let (mut m, mut a, mut c) = match chars.next() {
            Some('i') => (false, false, false),
            Some('g') => (true, true, false),
            _ => {
                return Err(format!(
                    "RISC-V ISA string `{ext}` must start with the base `i` (or `g`)"
                ));
            }
        };
        let mut seen = String::new();
        for ch in chars {
            if seen.contains(ch) {
                return Err(format!("RISC-V ISA string `{ext}` repeats `{ch}`"));
            }
            seen.push(ch);
            match ch {
                'm' if !m => m = true,
                'a' if !a => a = true,
                'c' => c = true,
                // F/D: synth emits no float instruction on RV32, so a
                // declared F/D changes nothing it emits.
                'f' | 'd' => {}
                _ => {
                    return Err(format!(
                        "RISC-V ISA string `{ext}`: extension `{ch}` is not supported"
                    ));
                }
            }
        }
        Ok(Self { m, a, c })
    }

    /// The profile `target` declares.
    pub fn from_target(target: &TargetSpec) -> Result<Self, String> {
        match &target.isa {
            IsaVariant::RiscV32 { extensions } | IsaVariant::RiscV64 { extensions } => {
                Self::from_extensions(extensions)
            }
            other => Err(format!("not a RISC-V ISA: {other:?}")),
        }
    }

    pub fn has(self, e: Extension) -> bool {
        match e {
            Extension::I => true,
            Extension::M => self.m,
            Extension::A => self.a,
            Extension::C => self.c,
        }
    }

    /// The ELF header flags for an object of this profile: RVC iff C. The
    /// float ABI bits stay 0 (ILP32 soft-float), as before.
    pub fn e_flags(self) -> u32 {
        if self.c { EF_RISCV_RVC } else { 0 }
    }

    /// The canonical name (`rv32imac`, ...).
    pub fn name(self) -> String {
        let mut s = String::from("rv32i");
        for (on, ch) in [(self.m, 'm'), (self.a, 'a'), (self.c, 'c')] {
            if on {
                s.push(ch);
            }
        }
        s
    }

    /// The first op in `ops` that needs an extension this profile lacks.
    pub fn first_violation(self, ops: &[RiscVOp]) -> Option<(Extension, &RiscVOp)> {
        ops.iter()
            .map(|op| (op_extension(op), op))
            .find(|(e, _)| !self.has(*e))
    }
}

/// The extension an op needs. EXHAUSTIVE, no wildcard: a new [`RiscVOp`]
/// variant must be classified here before it compiles.
pub fn op_extension(op: &RiscVOp) -> Extension {
    use RiscVOp::*;
    match op {
        Mul { .. }
        | Mulh { .. }
        | Mulhsu { .. }
        | Mulhu { .. }
        | Div { .. }
        | Divu { .. }
        | Rem { .. }
        | Remu { .. } => Extension::M,
        Lui { .. }
        | Auipc { .. }
        | Jal { .. }
        | Jalr { .. }
        | Branch { .. }
        | Addi { .. }
        | Slti { .. }
        | Sltiu { .. }
        | Xori { .. }
        | Ori { .. }
        | Andi { .. }
        | Slli { .. }
        | Srli { .. }
        | Srai { .. }
        | Add { .. }
        | Sub { .. }
        | Sll { .. }
        | Slt { .. }
        | Sltu { .. }
        | Xor { .. }
        | Srl { .. }
        | Sra { .. }
        | Or { .. }
        | And { .. }
        | Lb { .. }
        | Lh { .. }
        | Lw { .. }
        | Lbu { .. }
        | Lhu { .. }
        | Sb { .. }
        | Sh { .. }
        | Sw { .. }
        | Ecall
        | Ebreak
        | Mret
        | Wfi
        | Fence
        | Csrrw { .. }
        | Csrrs { .. }
        | Csrrc { .. }
        | Csrrwi { .. }
        | Csrrsi { .. }
        | Csrrci { .. }
        | Label { .. }
        | Call { .. }
        | La { .. } => Extension::I,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::register::Reg;

    #[test]
    fn named_targets_resolve_to_their_profiles() {
        for (name, m, a, c, flags) in [
            ("rv32i", false, false, false, 0),
            ("rv32im", true, false, false, 0),
            ("rv32imc", true, false, true, 1),
            ("esp32c3", true, false, true, 1),
            ("rv32imac", true, true, true, 1),
            ("riscv32", true, true, true, 1),
            ("rv32gc", true, true, true, 1),
        ] {
            let t = TargetSpec::from_triple(name).unwrap();
            let p = Rv32Profile::from_target(&t).unwrap();
            assert_eq!((p.m, p.a, p.c), (m, a, c), "{name}");
            assert_eq!(p.e_flags(), flags, "{name}");
        }
        assert_eq!(Rv32Profile::IMAC.e_flags(), 0x1);
    }

    #[test]
    fn malformed_isa_strings_are_refused() {
        for bad in ["", "mac", "imm", "imx", "iv"] {
            assert!(Rv32Profile::from_extensions(bad).is_err(), "{bad}");
        }
    }

    #[test]
    fn m_ops_violate_a_profile_without_m() {
        let r = Reg::T0;
        let ops = vec![
            RiscVOp::Add {
                rd: r,
                rs1: r,
                rs2: r,
            },
            RiscVOp::Remu {
                rd: r,
                rs1: r,
                rs2: r,
            },
        ];
        let i = Rv32Profile::from_extensions("i").unwrap();
        let (e, op) = i.first_violation(&ops).unwrap();
        assert_eq!(e, Extension::M);
        assert!(matches!(op, RiscVOp::Remu { .. }));
        assert!(
            Rv32Profile::from_extensions("im")
                .unwrap()
                .first_violation(&ops)
                .is_none()
        );
    }
}
