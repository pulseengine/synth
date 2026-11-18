//! The EMULATOR: run one function synth compiled, under unicorn.
//!
//! The semantics follow the Python oracles this crate replaces
//! (`scripts/repro/armv6m_1301_differential.py`,
//! `scripts/repro/i64_local_roundtrip_1713_differential.py`'s ARM and RV32
//! runners): the whole `.text` is mapped, the argument registers are loaded per
//! the calling convention, the callee-saved registers are SEEDED and checked
//! preserved, the stack pointer is checked balanced, and the call returns to a
//! sentinel address. What is stricter here:
//!
//! - The CPU model is set before anything is mapped and READ BACK; a mismatch
//!   refuses the run. (unicorn applies the model only when the CPU is first
//!   materialized, so a model set after `mem_map` is silently ignored. The
//!   Python oracle recorded exactly that, as "M0 reads back as M33".)
//! - A fault is a TRAP only when the faulting instruction is a trap idiom:
//!   UDF on ARM, `ebreak`/`c.ebreak`/`unimp`/`c.unimp` on RV32. Any other
//!   stop is ILLEGAL.
//! - Running out of the instruction budget is its own outcome, never a trap.

use std::cell::Cell;
use std::rc::Rc;

use unicorn_engine::{
    Arch, ArmCpuModel, Mode, Prot, RegisterARM, RegisterRISCV, Riscv32CpuModel, Unicorn,
};

use crate::compare::EmuOutcome;
use crate::synth::{CompiledObject, Machine};
use crate::value::{Signature, ValType, WasmValue};

/// The emulated core.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cpu {
    /// ARMv6-M, Thumb.
    CortexM0,
    /// ARMv7-M, Thumb-2.
    CortexM3,
    /// ARMv7E-M, Thumb-2 (soft-float calling convention).
    CortexM4,
    /// RV32IMAC: unicorn's SiFive E31, which is exactly RV32IMAC (+U), so an
    /// F/D instruction is undefined here as it is on the target.
    Rv32Imac,
}

impl Cpu {
    fn machine(self) -> Machine {
        match self {
            Cpu::Rv32Imac => Machine::RiscV32,
            _ => Machine::Arm,
        }
    }

    /// The unicorn CPU-model id this core is emulated as.
    pub fn model_id(self) -> i32 {
        match self {
            Cpu::CortexM0 => ArmCpuModel::CORTEX_M0 as i32,
            Cpu::CortexM3 => ArmCpuModel::CORTEX_M3 as i32,
            Cpu::CortexM4 => ArmCpuModel::CORTEX_M4 as i32,
            Cpu::Rv32Imac => Riscv32CpuModel::SIFIVE_E31 as i32,
        }
    }
}

/// Where the image lives. Fixed, so a run is reproducible.
pub const TEXT_BASE: u64 = 0x0001_0000;
pub const STACK_TOP: u64 = 0x0030_0000;
const STACK_SIZE: u64 = 0x0002_0000;
pub const RETURN_ADDR: u64 = 0x0040_0000;
/// Linear memory, when configured: ARM R11 / RV32 s11 hold this base.
pub const LINEAR_BASE: u64 = 0x2000_0000;
const POISON: u32 = 0xFEED_FACE;

/// Per-run configuration.
#[derive(Clone, Debug)]
pub struct EmuConfig {
    pub cpu: Cpu,
    /// Maximum instructions; reaching it is [`EmuOutcome::Budget`].
    pub budget: usize,
    /// Wall-clock backstop in microseconds (also [`EmuOutcome::Budget`]).
    pub timeout_us: u64,
    /// Initial linear memory, mapped at [`LINEAR_BASE`] (rounded up to 4 KiB).
    /// ARM: R11 = base, R10 = byte size. RV32: s11 = base.
    pub linear_memory: Option<Vec<u8>>,
}

impl EmuConfig {
    pub fn new(cpu: Cpu) -> Self {
        Self {
            cpu,
            budget: 1_000_000,
            timeout_us: 10_000_000,
            linear_memory: None,
        }
    }
}

/// The run could not be set up (as opposed to running and failing).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EmuError {
    Unicorn(String),
    /// The model read back after `ctl_set_cpu_model` is not the one asked for.
    CpuModelMismatch {
        requested: i32,
        readback: i32,
    },
    WrongMachine {
        object: Machine,
        cpu: Cpu,
    },
    NoSymbol(String),
    /// The function carries relocations, so it cannot run without linking.
    NeedsLink {
        func: String,
        relocs: usize,
    },
    NotThumb(String),
    /// Argument or result shape the calling-convention setup does not carry.
    Abi(String),
}

fn uc<T>(r: Result<T, unicorn_engine::uc_error>, what: &str) -> Result<T, EmuError> {
    r.map_err(|e| EmuError::Unicorn(format!("{what}: {e:?}")))
}

/// One emulated call.
#[derive(Clone, Debug)]
pub struct EmuRun {
    pub outcome: EmuOutcome,
    /// What `ctl_get_cpu_model` returned (already asserted equal).
    pub cpu_model_readback: i32,
}

/// The register words of a soft-float AAPCS call (i64/f64 in an even pair).
fn aapcs_words(params: &[ValType], args: &[WasmValue]) -> Result<Vec<u32>, EmuError> {
    let mut w: Vec<u32> = Vec::new();
    for (t, v) in params.iter().zip(args) {
        if t.words() == 2 && w.len() % 2 == 1 {
            w.push(POISON);
        }
        w.extend(v.to_words());
    }
    if w.len() > 4 {
        return Err(EmuError::Abi(format!(
            "AAPCS: {} argument words do not fit R0-R3 (stack arguments are not set up)",
            w.len()
        )));
    }
    Ok(w)
}

/// The register words of an RV32 ILP32 soft-float call (pairs not aligned).
fn ilp32_words(args: &[WasmValue]) -> Result<Vec<u32>, EmuError> {
    let w: Vec<u32> = args.iter().flat_map(|v| v.to_words()).collect();
    if w.len() > 8 {
        return Err(EmuError::Abi(format!(
            "ILP32: {} argument words do not fit a0-a7 (stack arguments are not set up)",
            w.len()
        )));
    }
    Ok(w)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TrapKind {
    Udf,
    Ebreak,
    Unimp,
}

/// Decode the trap idiom at the start of `bytes`, if they are one.
fn trap_idiom(machine: Machine, bytes: &[u8]) -> Option<(TrapKind, &'static str)> {
    let h = |i: usize| -> Option<u16> {
        Some(u16::from_le_bytes([*bytes.get(i)?, *bytes.get(i + 1)?]))
    };
    match machine {
        Machine::Arm => {
            let h1 = h(0)?;
            if h1 & 0xFF00 == 0xDE00 {
                return Some((TrapKind::Udf, "udf (T1)"));
            }
            let h2 = h(2)?;
            if h1 & 0xFFF0 == 0xF7F0 && h2 & 0xF000 == 0xA000 {
                return Some((TrapKind::Udf, "udf.w (T2)"));
            }
            None
        }
        Machine::RiscV32 => {
            let h1 = h(0)?;
            if h1 == 0x9002 {
                return Some((TrapKind::Ebreak, "c.ebreak"));
            }
            if h1 == 0x0000 {
                return Some((TrapKind::Unimp, "c.unimp"));
            }
            let w = u32::from(h1) | (u32::from(h(2)?) << 16);
            match w {
                0x0010_0073 => Some((TrapKind::Ebreak, "ebreak")),
                0xC000_1073 => Some((TrapKind::Unimp, "unimp")),
                _ => None,
            }
        }
    }
}

/// Run `func` from `obj` with `args` under `cfg`.
pub fn run(
    obj: &CompiledObject,
    func: &str,
    sig: &Signature,
    args: &[WasmValue],
    cfg: &EmuConfig,
) -> Result<EmuRun, EmuError> {
    let machine = cfg.cpu.machine();
    if obj.machine != machine {
        return Err(EmuError::WrongMachine {
            object: obj.machine,
            cpu: cfg.cpu,
        });
    }
    let sym = obj
        .func(func)
        .ok_or_else(|| EmuError::NoSymbol(func.to_string()))?
        .clone();
    let relocs = obj.relocs_in(func);
    if relocs > 0 {
        return Err(EmuError::NeedsLink {
            func: func.to_string(),
            relocs,
        });
    }
    if machine == Machine::Arm && !sym.thumb {
        return Err(EmuError::NotThumb(func.to_string()));
    }
    if sig.results.len() > 1 {
        return Err(EmuError::Abi(
            "multi-value results are not read back".into(),
        ));
    }
    if args.len() != sig.params.len() || args.iter().zip(&sig.params).any(|(a, t)| a.ty() != *t) {
        return Err(EmuError::Abi(format!(
            "arguments {args:?} do not match params {:?}",
            sig.params
        )));
    }

    let (arch, mode) = match machine {
        // NOT `Mode::MCLASS`: unicorn 2.1.x forces any MCLASS-mode CPU to
        // Cortex-M33 whatever model is requested (unicorn-engine-sys 2.1.5,
        // qemu/target/arm/cpu.c:2113). The M-profile models carry
        // ARM_FEATURE_M themselves, so plain THUMB + the model is M-class.
        Machine::Arm => (Arch::ARM, Mode::THUMB),
        Machine::RiscV32 => (Arch::RISCV, Mode::RISCV32),
    };
    let mut emu = uc(Unicorn::new(arch, mode), "Unicorn::new")?;
    // BEFORE any mapping: the CPU is materialized on first use, after which a
    // model change is ignored.
    let requested = cfg.cpu.model_id();
    uc(emu.ctl_set_cpu_model(requested), "ctl_set_cpu_model")?;
    let readback = uc(emu.ctl_get_cpu_model(), "ctl_get_cpu_model")?;
    if readback != requested {
        return Err(EmuError::CpuModelMismatch {
            requested,
            readback,
        });
    }

    let text_len = (obj.text.len() as u64 + 0xFFF) & !0xFFF;
    uc(
        emu.mem_map(TEXT_BASE, text_len.max(0x1000), Prot::ALL),
        "map text",
    )?;
    uc(emu.mem_write(TEXT_BASE, &obj.text), "write text")?;
    uc(
        emu.mem_map(
            STACK_TOP - STACK_SIZE / 2,
            STACK_SIZE,
            Prot::READ | Prot::WRITE,
        ),
        "map stack",
    )?;
    uc(
        emu.mem_map(RETURN_ADDR, 0x1000, Prot::ALL),
        "map return page",
    )?;
    let lin_size = cfg.linear_memory.as_ref().map(|m| m.len() as u64);
    if let Some(mem) = &cfg.linear_memory {
        let sz = ((mem.len() as u64 + 0xFFF) & !0xFFF).max(0x1000);
        uc(
            emu.mem_map(LINEAR_BASE, sz, Prot::READ | Prot::WRITE),
            "map linear memory",
        )?;
        uc(emu.mem_write(LINEAR_BASE, mem), "write linear memory")?;
    }

    // The trap hook: record where the exception was raised and stop.
    let hit: Rc<Cell<Option<(u64, u32)>>> = Rc::new(Cell::new(None));
    let hit2 = Rc::clone(&hit);
    uc(
        emu.add_intr_hook(move |u, intno| {
            let pc = u.pc_read().unwrap_or(u64::MAX);
            hit2.set(Some((pc, intno)));
            let _ = u.emu_stop();
        }),
        "add_intr_hook",
    )?;

    // Argument registers, callee-saved seeds, SP, return address.
    let (arg_regs, callee): (Vec<i32>, Vec<(i32, String)>) = match machine {
        Machine::Arm => (
            (0..4).map(|i| RegisterARM::R0 as i32 + i).collect(),
            (4..12)
                .map(|i| (RegisterARM::R0 as i32 + i, format!("R{i}")))
                .collect(),
        ),
        Machine::RiscV32 => {
            let x = |n: i32| RegisterRISCV::X0 as i32 + n;
            let mut s = vec![(x(8), "s0".to_string()), (x(9), "s1".to_string())];
            s.extend((18..28).map(|n| (x(n), format!("s{}", n - 16))));
            ((10..18).map(x).collect(), s)
        }
    };
    let words = match machine {
        Machine::Arm => aapcs_words(&sig.params, args)?,
        Machine::RiscV32 => ilp32_words(args)?,
    };
    for (i, r) in arg_regs.iter().enumerate() {
        uc(
            emu.reg_write(*r, u64::from(*words.get(i).unwrap_or(&POISON))),
            "write arg",
        )?;
    }
    let mut seeds = Vec::new();
    for (k, (r, name)) in callee.iter().enumerate() {
        let v: u64 = match (machine, name.as_str(), lin_size) {
            (Machine::Arm, "R11", Some(_)) | (Machine::RiscV32, "s11", Some(_)) => LINEAR_BASE,
            (Machine::Arm, "R10", Some(sz)) => sz,
            _ => 0xC0DE_0000 | k as u64,
        };
        uc(emu.reg_write(*r, v), "seed callee-saved")?;
        seeds.push((*r, name.clone(), v));
    }
    let (sp_reg, pc_reg) = match machine {
        Machine::Arm => (RegisterARM::SP as i32, RegisterARM::PC as i32),
        Machine::RiscV32 => (RegisterRISCV::SP as i32, RegisterRISCV::PC as i32),
    };
    uc(emu.reg_write(sp_reg, STACK_TOP), "write SP")?;
    let entry = TEXT_BASE + sym.offset;
    let begin = match machine {
        Machine::Arm => {
            uc(
                emu.reg_write(RegisterARM::LR as i32, RETURN_ADDR | 1),
                "write LR",
            )?;
            entry | 1
        }
        Machine::RiscV32 => {
            uc(
                emu.reg_write(RegisterRISCV::RA as i32, RETURN_ADDR),
                "write RA",
            )?;
            entry
        }
    };

    let r = emu.emu_start(begin, RETURN_ADDR, cfg.timeout_us, cfg.budget);
    let pc_now = uc(emu.reg_read(pc_reg), "read PC")? & !1;

    let read_insn = |emu: &Unicorn<()>, pc: u64| -> Vec<u8> {
        let mut b = vec![0u8; 4];
        if emu.mem_read(pc, &mut b).is_ok() {
            return b;
        }
        let mut b = vec![0u8; 2];
        if emu.mem_read(pc, &mut b).is_ok() {
            b
        } else {
            vec![]
        }
    };
    // Which stops are traps. The STOP PATH and the bytes both have to say so, and
    // the PC each path reports is pinned by unicorn-engine-sys 2.1.5's source:
    //
    // * ARM UDF: no hook; `emu_start` returns UC_ERR_INSN_INVALID with the PC
    //   AT the instruction (measured, as is every row here, by the control
    //   leg of potency_planted_illegal_instruction_reds). Every other ARM
    //   exception (BKPT 7, NOCP 17, ...) reaches the hook and is ILLEGAL.
    // * RV32 `ebreak` / `c.ebreak`: RISCV_EXCP_BREAKPOINT is a "stop
    //   interrupt" (qemu/target/riscv/unicorn.c, riscv_stop_interrupt): no
    //   hook, PC AT the instruction, and `emu_start` returns
    //   UC_ERR_INSN_INVALID (measured; not the UC_ERR_EXCEPTION that
    //   riscv_stop_interrupt writes to `invalid_error`).
    // * RV32 `unimp` / `c.unimp`: an illegal-instruction exception (2),
    //   delivered to the hook AFTER unicorn's unconditional `env->pc += 4`
    //   (qemu/accel/tcg/cpu-exec.c, the TARGET_RISCV block), so the faulting
    //   instruction starts at the reported PC minus 4, whatever its length.
    const RISCV_EXCP_ILLEGAL_INST: u32 = 2;
    let judge = |emu: &Unicorn<()>, pc: u64, allowed: &[TrapKind], why: String| -> EmuOutcome {
        let bytes = read_insn(emu, pc);
        match trap_idiom(machine, &bytes) {
            Some((kind, insn)) if allowed.contains(&kind) => EmuOutcome::Trap {
                pc,
                insn: insn.to_string(),
            },
            _ => EmuOutcome::Illegal {
                pc,
                reason: format!("{why}; insn bytes {bytes:02x?}"),
            },
        }
    };

    let outcome = if let Some((raw_pc, intno)) = hit.get() {
        let why = format!("exception {intno}");
        match (machine, intno) {
            (Machine::Arm, _) => judge(&emu, raw_pc & !1, &[], why),
            (Machine::RiscV32, RISCV_EXCP_ILLEGAL_INST) => {
                judge(&emu, raw_pc.wrapping_sub(4), &[TrapKind::Unimp], why)
            }
            (Machine::RiscV32, _) => judge(&emu, raw_pc.wrapping_sub(4), &[], why),
        }
    } else if let Err(e) = r {
        let why = format!("unicorn error {e:?}");
        match (machine, e) {
            (Machine::RiscV32, unicorn_engine::uc_error::INSN_INVALID) => {
                judge(&emu, pc_now, &[TrapKind::Ebreak], why)
            }
            (Machine::Arm, unicorn_engine::uc_error::INSN_INVALID) => {
                judge(&emu, pc_now, &[TrapKind::Udf], why)
            }
            _ => judge(&emu, pc_now, &[], why),
        }
    } else if pc_now != RETURN_ADDR {
        EmuOutcome::Budget
    } else {
        let mut viol = Vec::new();
        for (r, name, v) in &seeds {
            if uc(emu.reg_read(*r), "read callee-saved")? & 0xFFFF_FFFF != *v {
                viol.push(format!("{name} clobbered"));
            }
        }
        if uc(emu.reg_read(sp_reg), "read SP")? & 0xFFFF_FFFF != STACK_TOP {
            viol.push("SP imbalance".into());
        }
        if !viol.is_empty() {
            EmuOutcome::Illegal {
                pc: pc_now,
                reason: format!("ABI violated: {}", viol.join(", ")),
            }
        } else {
            let mut out_words = Vec::new();
            for r in arg_regs
                .iter()
                .take(sig.results.iter().map(|t| t.words()).sum())
            {
                out_words.push(uc(emu.reg_read(*r), "read result")? as u32);
            }
            EmuOutcome::Values(
                sig.results
                    .first()
                    .map(|t| vec![WasmValue::from_words(*t, &out_words)])
                    .unwrap_or_default(),
            )
        }
    };
    Ok(EmuRun {
        outcome,
        cpu_model_readback: readback,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trap_idioms() {
        assert_eq!(
            trap_idiom(Machine::Arm, &[0x00, 0xDE]),
            Some((TrapKind::Udf, "udf (T1)"))
        );
        assert_eq!(
            trap_idiom(Machine::Arm, &[0xF0, 0xF7, 0x00, 0xA0]),
            Some((TrapKind::Udf, "udf.w (T2)"))
        );
        // BKPT (0xBE00) is not a trap idiom.
        assert_eq!(trap_idiom(Machine::Arm, &[0x00, 0xBE]), None);
        assert_eq!(
            trap_idiom(Machine::RiscV32, &0x0010_0073u32.to_le_bytes()),
            Some((TrapKind::Ebreak, "ebreak"))
        );
        assert_eq!(
            trap_idiom(Machine::RiscV32, &0xC000_1073u32.to_le_bytes()),
            Some((TrapKind::Unimp, "unimp"))
        );
        // ecall is not a trap idiom.
        assert_eq!(
            trap_idiom(Machine::RiscV32, &0x0000_0073u32.to_le_bytes()),
            None
        );
    }

    #[test]
    fn aapcs_aligns_i64_pairs() {
        let w = aapcs_words(
            &[ValType::I32, ValType::I64],
            &[WasmValue::I32(7), WasmValue::I64(0x1111_2222_3333_4444)],
        )
        .unwrap();
        assert_eq!(w, vec![7, POISON, 0x3333_4444, 0x1111_2222]);
        assert!(
            aapcs_words(
                &[ValType::I32, ValType::I64, ValType::I32],
                &[WasmValue::I32(0), WasmValue::I64(0), WasmValue::I32(0)]
            )
            .is_err()
        );
        let w = ilp32_words(&[WasmValue::I32(7), WasmValue::I64(0x1111_2222_3333_4444)]).unwrap();
        assert_eq!(w, vec![7, 0x3333_4444, 0x1111_2222]);
    }
}
