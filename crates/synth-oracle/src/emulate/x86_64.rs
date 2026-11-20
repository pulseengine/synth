//! The x86-64 runner (RQ-91-X86SKEL, RQ-91-X86ALU, #1741): one SysV AMD64
//! call under unicorn.
//!
//! THE CPU MODEL IS PINNED to QEMU64, the x86-64 baseline, and read back.
//! unicorn's default x86 model accepts instructions above the baseline
//! (`popcnt`, BMI, `roundss`) and runs `F3 0F BD` as `lzcnt` where a baseline
//! CPU runs it as `bsr` — a different value and no fault — so an unpinned
//! oracle could pass an above-baseline instruction (REVIEW_2 X2).
//!
//! THE CALL. Integer arguments go in `rdi, rsi, rdx, rcx, r8, r9`. The return
//! address is pushed, so at entry `rsp + 8` is 16-byte aligned, as after a
//! `call`. The result is read from `rax`: its low half for an i32.
//!
//! WHAT IS POISONED, so that reading something the ABI leaves undefined
//! cannot agree with wasm by accident:
//! - the UPPER HALF of every i32 argument register;
//! - every argument register the signature does not use, and the caller-saved
//!   scratch `rax, r10, r11`;
//! - the arithmetic flags (CF, PF, AF, ZF, SF, OF all set at entry), so a
//!   `setCC`/`cmovCC` with no compare before it does not read unicorn's zero;
//! - the WHOLE stack mapping. unicorn maps zeroed pages and wasm
//!   zero-initialises locals: on a zeroed stack a lowering that drops a
//!   local's zero-store would agree with wasm.
//!
//! WHAT IS CHECKED ON RETURN, each an ABI violation and never a value:
//! - `rbx, rbp, r12–r15` unchanged in all 64 bits (the seeds have a nonzero
//!   upper half, so a 32-bit write, which zeroes it, is caught);
//! - `rsp` balanced;
//! - the direction flag clear;
//! - the CALLER'S frame (every byte at and above the entry `rsp + 8`)
//!   unwritten.
//!
//! A TRAP is `ud2` (`0F 0B`) at RIP, inside the function, stopped as
//! UC_ERR_INSN_INVALID (see `trap_insn` in the parent module). Any other
//! fault — an undecodable byte, a `#DE` from `div`, an unmapped access — is
//! ILLEGAL.

use std::cell::Cell;
use std::rc::Rc;

use unicorn_engine::{Arch, Mode, Prot, RegisterX86, Unicorn};

use super::{
    EmuConfig, EmuError, EmuRun, Fault, RETURN_ADDR, STACK_SIZE, STACK_TOP, TEXT_BASE, fault_pc,
    judge, uc,
};
use crate::compare::EmuOutcome;
use crate::synth::{CompiledObject, FuncSym, Machine};
use crate::value::{Signature, ValType, WasmValue};

/// The poison in an unused or caller-saved 64-bit register, in the UPPER half
/// of every i32 argument register, and (repeated) in every stack byte.
const POISON64: u64 = 0xFEED_FACE_DEAD_BEEF;

/// CF, PF, AF, ZF, SF and OF set; bit 1 is always 1; DF (bit 10) CLEAR, as
/// the ABI requires at a call.
const POISON_FLAGS: u64 = 0x8D7;
const DF: u64 = 1 << 10;

/// The SysV AMD64 integer argument registers, in order.
const SYSV_ARGS: [RegisterX86; 6] = [
    RegisterX86::RDI,
    RegisterX86::RSI,
    RegisterX86::RDX,
    RegisterX86::RCX,
    RegisterX86::R8,
    RegisterX86::R9,
];

/// Caller-saved registers that never carry an argument: POISONED at entry so
/// code that reads one before writing it computes with garbage. `rax` is among
/// them (it is the result register, written by a correct callee).
const CALLER_SAVED_SCRATCH: [RegisterX86; 3] =
    [RegisterX86::RAX, RegisterX86::R10, RegisterX86::R11];

/// Checked preserved. `rsp` is checked separately (balanced, not seeded).
const CALLEE_SAVED: [(RegisterX86, &str); 6] = [
    (RegisterX86::RBX, "rbx"),
    (RegisterX86::RBP, "rbp"),
    (RegisterX86::R12, "r12"),
    (RegisterX86::R13, "r13"),
    (RegisterX86::R14, "r14"),
    (RegisterX86::R15, "r15"),
];

/// The register values of a SysV AMD64 call: an i32 argument occupies the low
/// half and the upper half is POISONED (the ABI does not define it, so code
/// that reads it is wrong); an i64 fills the register.
fn sysv_regs(params: &[ValType], args: &[WasmValue]) -> Result<Vec<u64>, EmuError> {
    if args.len() > SYSV_ARGS.len() {
        return Err(EmuError::Abi(format!(
            "SysV: {} integer arguments do not fit rdi..r9 (stack arguments are not set up)",
            args.len()
        )));
    }
    params
        .iter()
        .zip(args)
        .map(|(t, v)| match (t, v) {
            (ValType::I32, WasmValue::I32(x)) => Ok((POISON64 & !0xFFFF_FFFF) | u64::from(*x)),
            (ValType::I64, WasmValue::I64(x)) => Ok(*x),
            _ => Err(EmuError::Abi(format!("SysV: {t:?} argument {v:?}"))),
        })
        .collect()
}

/// The poisoned stack image: POISON64 in every 8-byte cell.
fn stack_image() -> Vec<u8> {
    POISON64
        .to_le_bytes()
        .iter()
        .copied()
        .cycle()
        .take(STACK_SIZE as usize)
        .collect()
}

/// Run an x86-64 function under SysV AMD64. The caller ([`super::run`]) has
/// checked the machine, the symbol, the relocations and the signature shape.
pub(super) fn run(
    obj: &CompiledObject,
    sym: &FuncSym,
    sig: &Signature,
    args: &[WasmValue],
    cfg: &EmuConfig,
) -> Result<EmuRun, EmuError> {
    let machine = Machine::X86_64;
    let arg_values = sysv_regs(&sig.params, args)?;

    let mut emu = uc(Unicorn::new(Arch::X86, Mode::MODE_64), "Unicorn::new")?;
    // BEFORE any mapping: the CPU is materialized on first use, after which a
    // model change is refused.
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
    let stack_base = STACK_TOP - STACK_SIZE / 2;
    uc(
        emu.mem_map(stack_base, STACK_SIZE, Prot::READ | Prot::WRITE),
        "map stack",
    )?;
    // The whole mapping is poison; then the return address is pushed.
    let mut stack = stack_image();
    let ret_slot = (STACK_TOP - 8 - stack_base) as usize;
    stack[ret_slot..ret_slot + 8].copy_from_slice(&RETURN_ADDR.to_le_bytes());
    uc(emu.mem_write(stack_base, &stack), "poison stack")?;
    uc(
        emu.mem_map(RETURN_ADDR, 0x1000, Prot::ALL),
        "map return page",
    )?;

    // The hook: record where the exception was raised and stop.
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

    for (i, r) in SYSV_ARGS.iter().enumerate() {
        let v = *arg_values.get(i).unwrap_or(&POISON64);
        uc(emu.reg_write(*r as i32, v), "write arg")?;
    }
    for r in CALLER_SAVED_SCRATCH {
        uc(emu.reg_write(r as i32, POISON64), "poison caller-saved")?;
    }
    uc(
        emu.reg_write(RegisterX86::EFLAGS as i32, POISON_FLAGS),
        "poison flags",
    )?;
    let mut seeds = Vec::new();
    for (k, (r, name)) in CALLEE_SAVED.into_iter().enumerate() {
        // All 64 bits, so a 32-bit write (which zeroes the upper half) to a
        // callee-saved register is caught too.
        let v = 0xC0DE_5AFE_0000_0000 | k as u64;
        uc(emu.reg_write(r as i32, v), "seed callee-saved")?;
        seeds.push((r, name, v));
    }
    // SysV: `call` pushed the return address, so at entry rsp + 8 is 16-byte
    // aligned (STACK_TOP is) and [rsp] is the sentinel. A balanced `ret`
    // leaves rsp == STACK_TOP.
    uc(
        emu.reg_write(RegisterX86::RSP as i32, STACK_TOP - 8),
        "write RSP",
    )?;
    let entry = TEXT_BASE + sym.offset;

    // timeout 0: no wall-clock thread (see the parent module doc).
    let r = emu.emu_start(entry, RETURN_ADDR, 0, cfg.budget);
    // x86-64 instructions are byte-aligned: RIP is used as read.
    let pc_now = uc(emu.reg_read(RegisterX86::RIP as i32), "read RIP")?;

    let fault = match (hit.get(), r) {
        (Some((reported_pc, intno)), _) => Some(Fault::Hook { reported_pc, intno }),
        (None, Err(err)) => Some(Fault::Error { pc: pc_now, err }),
        (None, Ok(())) => None,
    };
    let outcome = if let Some(fault) = fault {
        let pc = fault_pc(machine, fault);
        let mut bytes = vec![0u8; 2];
        if emu.mem_read(pc, &mut bytes).is_err() {
            bytes.clear();
        }
        judge(machine, fault, &bytes, &(entry..entry + sym.size))
    } else if pc_now != RETURN_ADDR {
        EmuOutcome::Budget
    } else {
        let mut viol = Vec::new();
        for (r, name, v) in &seeds {
            if uc(emu.reg_read(*r as i32), "read callee-saved")? != *v {
                viol.push(format!("{name} clobbered"));
            }
        }
        if uc(emu.reg_read(RegisterX86::RSP as i32), "read RSP")? != STACK_TOP {
            viol.push("SP imbalance".into());
        }
        if uc(emu.reg_read(RegisterX86::EFLAGS as i32), "read EFLAGS")? & DF != 0 {
            viol.push("direction flag set".into());
        }
        // The caller's frame: everything at and above the entry rsp + 8.
        let caller = (STACK_TOP - stack_base) as usize;
        let mut now = vec![0u8; STACK_SIZE as usize - caller];
        uc(emu.mem_read(STACK_TOP, &mut now), "read caller frame")?;
        if now != stack[caller..] {
            viol.push("caller frame written".into());
        }
        if !viol.is_empty() {
            EmuOutcome::Illegal {
                pc: pc_now,
                reason: format!("ABI violated: {}", viol.join(", ")),
            }
        } else {
            // SysV: the result is in rax; an i32 is its LOW half (the upper
            // half is not part of the value).
            let rax = uc(emu.reg_read(RegisterX86::RAX as i32), "read rax")?;
            EmuOutcome::Values(
                sig.results
                    .first()
                    .map(|t| match t {
                        ValType::I32 => Ok(vec![WasmValue::I32(rax as u32)]),
                        ValType::I64 => Ok(vec![WasmValue::I64(rax)]),
                        ValType::F32 | ValType::F64 => Err(EmuError::FloatAbi {
                            func: format!("offset {:#x}", sym.offset),
                            machine,
                        }),
                    })
                    .transpose()?
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

    /// SysV argument registers: an i32's upper half is the poison, an i64 is
    /// the whole register, and a seventh argument is refused.
    #[test]
    fn sysv_poisons_the_upper_half_of_i32_args() {
        let r = sysv_regs(
            &[ValType::I32, ValType::I64],
            &[WasmValue::I32(7), WasmValue::I64(0x1111_2222_3333_4444)],
        )
        .unwrap();
        assert_eq!(r, vec![0xFEED_FACE_0000_0007, 0x1111_2222_3333_4444]);
        assert!(sysv_regs(&[ValType::I32; 7], &[WasmValue::I32(0); 7]).is_err());
        assert!(sysv_regs(&[ValType::F32], &[WasmValue::F32(0)]).is_err());
    }

    /// The poisoned flags have every arithmetic flag set and DF clear.
    #[test]
    fn poisoned_flags_keep_the_direction_flag_clear() {
        assert_eq!(POISON_FLAGS & DF, 0);
        for bit in [0u64, 2, 4, 6, 7, 11] {
            assert_ne!(POISON_FLAGS & (1 << bit), 0, "flag bit {bit}");
        }
    }
}
