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
//!   refuses the run.
//! - A stop is a TRAP only when the way unicorn stopped AND the instruction
//!   bytes both say so, the bytes are exactly the trap synth emits (Thumb
//!   `udf` T1; RV32 32-bit `ebreak`; x86-64 `ud2`, `0F 0B`), and the PC lies
//!   inside the function. Any other fault is ILLEGAL.
//!
//! x86-64 (RQ-91-X86SKEL, RQ-91-X86ALU, #1741) has its own runner,
//! [`x86_64::run`]: SysV AMD64, the CPU model pinned to QEMU64, every
//! register outside the call and the whole stack poisoned, and `ud2` as the
//! trap.
//! - Running out of the instruction budget is its own outcome, never a trap.
//!
//! WHAT IS REFUSED, with a typed error, rather than run and judged wrongly:
//! floating-point signatures on ARM and RV32 (synth's hard-float targets pass
//! them in S registers and the soft-float convention is not shown on real
//! code), stack arguments, multi-value results, and (through [`run`]) any
//! function carrying a relocation.
//!
//! AArch64 (#1745) has its own runner, [`run_a64`]: AAPCS64, with float
//! arguments and results in V registers, and `brk` as the trap.
//!
//! WHAT IS POISONED, so that reading something uninitialised cannot agree
//! with wasm's zero: the whole stack mapping on every core, every unused
//! argument register, on AArch64 also x8-x18 and d16-d31, and on the two VFP
//! cores d0-d15.
//! [`run`] maps no linear memory: modules with a memory are refused one level
//! up ([`crate::run_case`]), because memory effects are not compared there.
//!
//! [`run_env`] (RV32; on AArch64 the memory half only, `x28` as the base)
//! adds an [`EmuEnv`]: linear memory 0's initial
//! image mapped at [`MEM_BASE`] with `s11` (synth's RV32 linear-memory base
//! register) pointing at it and the final image read back, and a LINK step
//! that resolves every `.text` relocation: a call to a function defined in
//! `.text` is patched to it, a call to an undefined symbol to a host stub.
//! Each stub is one `ret` under a code hook that reads the arguments per
//! ILP32, calls the host function, writes the result to `a0`/`a1` and then
//! CLOBBERS every other caller-saved register (`t0`-`t6`, `a0`-`a7`) with a
//! poison value, as the psABI lets any callee do. A relocation of any other
//! type is refused ([`EmuError::Env`]).
//!
//! There is NO wall-clock timeout. unicorn's timeout thread reads a
//! process-global clock that every engine init rewrites, and under concurrent
//! engines it stopped healthy runs (52 spurious Budget stops in 32,000 runs on
//! 8 threads, REVIEW_11 F2). The instruction count alone bounds a run.

use std::cell::Cell;
use std::ops::Range;
use std::rc::Rc;

use unicorn_engine::{
    Arch, Arm64CpuModel, ArmCpuModel, Mode, Prot, RegisterARM, RegisterARM64, RegisterRISCV,
    Riscv32CpuModel, Unicorn, X86CpuModel, uc_error,
};

use crate::compare::EmuOutcome;
use crate::reference::{HostCall, HostFn};
use crate::synth::{CompiledObject, Machine};
use crate::value::{Signature, ValType, WasmValue};

mod x86_64;

/// The emulated core.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cpu {
    /// ARMv6-M, Thumb.
    CortexM0,
    /// ARMv7-M, Thumb-2.
    CortexM3,
    /// ARMv7E-M, Thumb-2. Float signatures are refused (see the module doc).
    CortexM4,
    /// Cortex-M4 for synth's `cortex-m4f` target: CPACR CP10/CP11 and
    /// FPEXC.EN are written and d0-d15 poisoned. A float RESULT is read from
    /// s0/d0; a float PARAMETER is still refused. (unicorn 2.1.5 runs VFP
    /// instructions on its M4 model without the CPACR write too; the write is
    /// what silicon needs and costs nothing here.)
    CortexM4F,
    /// Cortex-M7 with its double-precision FPU enabled, likewise, for
    /// `cortex-m7dp`.
    CortexM7F,
    /// ARMv7E-M, Thumb-2 (synth's `cortex-m7dp`) with the VFP left as reset
    /// leaves it: float signatures are refused, as on `CortexM4`. The import
    /// boundary oracle's leg and the target record's `cortex-m7dp` row;
    /// `CortexM7F` is the float-result one.
    CortexM7,
    /// RV32IMAC: unicorn's SiFive E31, which is exactly RV32IMAC (+U), so an
    /// F/D instruction is undefined here as it is on the target.
    Rv32Imac,
    /// ARMv8-A, A64 (#1745). The only core on which float signatures run:
    /// see [`run_a64`] for the AAPCS64 set-up.
    CortexA53,
    /// x86-64 at the baseline ISA level: unicorn's QEMU64 model (SSE2, no
    /// POPCNT/LZCNT/BMI/SSE4.1). See the module doc for why it is pinned.
    X86_64Baseline,
}

impl Cpu {
    pub(crate) fn machine(self) -> Machine {
        match self {
            Cpu::Rv32Imac => Machine::RiscV32,
            Cpu::CortexA53 => Machine::AArch64,
            Cpu::X86_64Baseline => Machine::X86_64,
            Cpu::CortexM0
            | Cpu::CortexM3
            | Cpu::CortexM4
            | Cpu::CortexM4F
            | Cpu::CortexM7
            | Cpu::CortexM7F => Machine::Arm,
        }
    }

    /// The run enables the VFP and reads float results from it.
    fn vfp(self) -> bool {
        matches!(self, Cpu::CortexM4F | Cpu::CortexM7F)
    }

    /// The unicorn CPU-model id this core is emulated as.
    pub fn model_id(self) -> i32 {
        match self {
            Cpu::CortexM0 => ArmCpuModel::CORTEX_M0 as i32,
            Cpu::CortexM3 => ArmCpuModel::CORTEX_M3 as i32,
            Cpu::CortexM4 | Cpu::CortexM4F => ArmCpuModel::CORTEX_M4 as i32,
            Cpu::CortexM7 | Cpu::CortexM7F => ArmCpuModel::CORTEX_M7 as i32,
            Cpu::Rv32Imac => Riscv32CpuModel::SIFIVE_E31 as i32,
            Cpu::CortexA53 => Arm64CpuModel::A53 as i32,
            Cpu::X86_64Baseline => X86CpuModel::QEMU64 as i32,
        }
    }
}

/// Where the image lives. Fixed, so a run is reproducible.
pub const TEXT_BASE: u64 = 0x0001_0000;
pub const STACK_TOP: u64 = 0x0030_0000;
pub(crate) const STACK_SIZE: u64 = 0x0002_0000;
pub const RETURN_ADDR: u64 = 0x0040_0000;
pub(crate) const POISON: u32 = 0xFEED_FACE;
/// AArch64: what an unused argument register holds, and (its high half) the
/// upper 32 bits of a register carrying an i32 or f32 argument, which
/// AAPCS64 leaves unspecified.
const POISON64: u64 = 0xFEED_FACE_FEED_FACE;
/// Host stubs, one 4-byte `ret` each ([`EmuEnv::imports`] order).
pub const STUB_BASE: u64 = 0x0050_0000;
/// Linear memory 0 ([`EmuEnv::memory`]); `s11` holds this address.
pub const MEM_BASE: u64 = 0x1000_0000;
/// `jalr x0, 0(x1)`.
const RV_RET: u32 = 0x0000_8067;
/// R_RISCV_CALL_PLT, the only relocation [`run_env`] links.
const R_RISCV_CALL_PLT: u32 = 19;

/// What [`run_env`] maps and links beyond `.text`.
#[derive(Clone, Default)]
pub struct EmuEnv {
    /// Linear memory 0's initial image (`initial` pages, data applied).
    pub memory: Option<Vec<u8>>,
    /// The host functions the object's UNDEFINED call targets resolve to,
    /// by symbol name, with the import's signature.
    pub imports: Vec<(String, Signature, HostFn)>,
}

impl std::fmt::Debug for EmuEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EmuEnv")
            .field("memory", &self.memory.as_ref().map(Vec::len))
            .field(
                "imports",
                &self
                    .imports
                    .iter()
                    .map(|(n, s, _)| (n, s))
                    .collect::<Vec<_>>(),
            )
            .finish()
    }
}

/// Per-run configuration.
#[derive(Clone, Debug)]
pub struct EmuConfig {
    pub cpu: Cpu,
    /// Maximum instructions; reaching it is [`EmuOutcome::Budget`]. The only
    /// bound on a run (there is deliberately no wall-clock timeout).
    pub budget: usize,
}

impl EmuConfig {
    pub fn new(cpu: Cpu) -> Self {
        Self {
            cpu,
            budget: 1_000_000,
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
    /// The function carries relocations, so it cannot run without linking
    /// ([`run`]), or one of them is not linkable ([`run_env`]).
    NeedsLink {
        func: String,
        relocs: usize,
    },
    /// [`run_env`]: something the environment cannot set up (a memory or a
    /// stub on a non-RV32 core, an unresolved or ambiguous symbol, a
    /// relocation type other than R_RISCV_CALL_PLT).
    Env(String),
    NotThumb(String),
    /// An f32/f64 parameter or result. On a hard-float ARM target synth
    /// passes them in S/D registers, which this harness does not set up or
    /// read, so a wrong result could agree. Refused on every core until the
    /// float convention is set up and shown right on real code.
    FloatAbi {
        func: String,
        machine: Machine,
    },
    /// Argument or result shape the calling-convention setup does not carry.
    Abi(String),
    /// HOSTED: the object references a symbol that is neither defined in it
    /// nor one of the module's function imports (by bare field name), so no
    /// embedder contract says what a call to it does.
    UnresolvedSymbol(String),
    /// HOSTED: a relocation the harness does not resolve (anything other
    /// than `R_ARM_THM_CALL`), or one it could not apply.
    Reloc(String),
    /// HOSTED: the module needs instantiation state the harness does not
    /// materialize (data segments, globals, tables, a start function).
    Uninstantiated(&'static str),
}

pub(crate) fn uc<T>(r: Result<T, uc_error>, what: &str) -> Result<T, EmuError> {
    r.map_err(|e| EmuError::Unicorn(format!("{what}: {e:?}")))
}

/// One emulated call.
#[derive(Clone, Debug)]
pub struct EmuRun {
    pub outcome: EmuOutcome,
    /// What `ctl_get_cpu_model` returned (already asserted equal).
    pub cpu_model_readback: i32,
    /// [`run_env`]: linear memory after the run (`None` without a memory).
    pub memory: Option<Vec<u8>>,
    /// [`run_env`]: every host call, in order.
    pub calls: Vec<HostCall>,
}

/// The register words of an AAPCS call (i64 in an even pair).
pub(crate) fn aapcs_words(params: &[ValType], args: &[WasmValue]) -> Result<Vec<u32>, EmuError> {
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

/// The register words of an RV32 ILP32 call (pairs not aligned).
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

/// How a run stopped, other than by returning or running out of budget.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Fault {
    /// The interrupt hook fired. `reported_pc` is what `pc_read` gave inside
    /// the hook.
    Hook { reported_pc: u64, intno: u32 },
    /// `emu_start` returned an error, with the PC read afterwards.
    Error { pc: u64, err: uc_error },
}

/// The address of the faulting instruction.
///
/// On RV32 unicorn adds 4 to the PC before calling the interrupt hook, for
/// every exception it delivers there (unicorn-engine-sys 2.1.5,
/// qemu/accel/tcg/cpu-exec.c, the TARGET_RISCV block), whatever the
/// instruction's length.
///
/// On x86-64 the address is used as read: instructions are byte-aligned, so
/// there is no mode bit to clear.
pub(crate) fn fault_pc(machine: Machine, fault: Fault) -> u64 {
    match (machine, fault) {
        (Machine::RiscV32, Fault::Hook { reported_pc, .. }) => reported_pc.wrapping_sub(4),
        (Machine::Arm, Fault::Hook { reported_pc, .. }) => reported_pc & !1,
        (Machine::AArch64, Fault::Hook { reported_pc, .. }) => reported_pc,
        (Machine::X86_64, Fault::Hook { reported_pc, .. }) => reported_pc,
        (Machine::X86_64, Fault::Error { pc, .. }) => pc,
        (Machine::Arm | Machine::RiscV32 | Machine::AArch64, Fault::Error { pc, .. }) => pc & !1,
    }
}

/// The trap synth emits, if the stop path and the bytes both say this is it.
///
/// Matched EXACTLY against what synth emits, nothing wider:
/// - Thumb: `udf #imm8` T1 (`0xDExx`; `arm_encoder.rs`, the Thumb-2 `Udf`
///   arm and every inline guard). synth emits no `udf.w`. unicorn stops on it
///   with UC_ERR_INSN_INVALID, PC at the instruction, and no hook.
/// - RV32: the 32-bit `ebreak` (`0x00100073`; `RiscVOp::Ebreak`, the only trap
///   the RV32 selector emits; the encoder has no compressed forms). It is a
///   unicorn "stop interrupt" (riscv_stop_interrupt): no hook,
///   UC_ERR_INSN_INVALID, PC at the instruction.
/// - x86-64: `ud2` (`0F 0B`), the only trap the x86-64 backend may emit. It
///   stops unicorn with UC_ERR_INSN_INVALID, RIP at the instruction, and no
///   hook. Other undecodable bytes (`06`, `0F 0F FF`) stop the SAME way
///   (REVIEW_2 X3), so the bytes at RIP decide; a CPU exception such as the
///   `#DE` of `div` by zero is a hook stop or UC_ERR_EXCEPTION, never a trap.
///
/// On ARM, RV32 and x86-64 a hook stop is never a trap: BKPT, NOCP, ecall, an
/// illegal instruction (including `c.unimp` = `0x0000`, which zero padding
/// decodes as) are all ILLEGAL. AArch64 is the reverse, see [`a64_trap_insn`].
fn trap_insn(machine: Machine, fault: Fault, bytes: &[u8]) -> Option<&'static str> {
    let h = |i: usize| -> Option<u16> {
        Some(u16::from_le_bytes([*bytes.get(i)?, *bytes.get(i + 1)?]))
    };
    if machine == Machine::AArch64 {
        return a64_trap_insn(fault, u32::from(h(0)?) | (u32::from(h(2)?) << 16));
    }
    let Fault::Error {
        err: uc_error::INSN_INVALID,
        ..
    } = fault
    else {
        return None;
    };
    match machine {
        Machine::AArch64 => None,
        Machine::Arm => (h(0)? & 0xFF00 == 0xDE00).then_some("udf"),
        Machine::RiscV32 => {
            let w = u32::from(h(0)?) | (u32::from(h(2)?) << 16);
            (w == 0x0010_0073).then_some("ebreak")
        }
        Machine::X86_64 => (bytes.get(..2)? == [0x0F, 0x0B]).then_some("ud2"),
    }
}

/// AArch64: `brk #imm16` (`0xD4200000 | imm16 << 5`; `encoder::brk`, the
/// only trap the A64 selector emits). unicorn delivers it to the interrupt
/// hook as exception 7 (QEMU's EXCP_BKPT) with the PC AT the instruction.
/// Measured on unicorn 2.1.5: `udf` and `hlt` arrive as exception 1 and
/// `svc` as exception 2, so neither the hook alone nor the bytes alone
/// decide.
fn a64_trap_insn(fault: Fault, word: u32) -> Option<&'static str> {
    let Fault::Hook { intno: 7, .. } = fault else {
        return None;
    };
    (word & 0xFFE0_001F == 0xD420_0000).then_some("brk")
}

/// Judge a fault: a trap only per [`trap_insn`] AND with the PC inside the
/// function (`func` is its absolute address range).
pub(crate) fn judge(machine: Machine, fault: Fault, bytes: &[u8], func: &Range<u64>) -> EmuOutcome {
    let pc = fault_pc(machine, fault);
    match trap_insn(machine, fault, bytes) {
        Some(insn) if func.contains(&pc) => EmuOutcome::Trap {
            pc,
            insn: insn.to_string(),
        },
        Some(insn) => EmuOutcome::Illegal {
            pc,
            reason: format!("{insn} outside the function {func:x?}"),
        },
        None => EmuOutcome::Illegal {
            pc,
            reason: format!("{fault:?}; insn bytes {bytes:02x?}"),
        },
    }
}

/// Fill the whole stack mapping with POISON words. unicorn maps zeroed
/// pages, and wasm zero-initialises locals: on a zeroed stack a lowering that
/// DROPS the zero-store of a local's frame slot would agree with wasm.
fn poison_stack(emu: &mut Unicorn<'_, ()>) -> Result<(), EmuError> {
    let fill: Vec<u8> = POISON
        .to_le_bytes()
        .iter()
        .copied()
        .cycle()
        .take(STACK_SIZE as usize)
        .collect();
    uc(
        emu.mem_write(STACK_TOP - STACK_SIZE / 2, &fill),
        "poison stack",
    )
}

/// The registers a run checks preserved, by name.
fn callee_saved(machine: Machine) -> Vec<(i32, String)> {
    match machine {
        Machine::Arm => (4..12)
            .map(|i| (RegisterARM::R0 as i32 + i, format!("R{i}")))
            .collect(),
        Machine::RiscV32 => {
            let x = |n: i32| RegisterRISCV::X0 as i32 + n;
            // gp and tp are not callee-saved in the ILP32 sense: no function
            // may change them at all.
            let mut s = vec![
                (x(3), "gp".to_string()),
                (x(4), "tp".to_string()),
                (x(8), "s0".to_string()),
                (x(9), "s1".to_string()),
            ];
            s.extend((18..28).map(|n| (x(n), format!("s{}", n - 16))));
            s
        }
        // AAPCS64: x19-x28, the frame pointer x29, and the low 64 bits of
        // v8-v15 (read as d8-d15).
        // unicorn numbers x0-x28 and d0-d31 contiguously; x29 is NOT
        // `X0 + 29` (that id is another register), so it is named.
        Machine::AArch64 => (19..29)
            .map(|n| (RegisterARM64::X0 as i32 + n, format!("x{n}")))
            .chain([(RegisterARM64::X29 as i32, "x29".to_string())])
            .chain((8..16).map(|n| (RegisterARM64::D0 as i32 + n, format!("d{n}"))))
            .collect(),
        Machine::X86_64 => unreachable!("x86-64 has its own runner"),
    }
}

/// The AAPCS64 argument registers for `args`: `(x0.., v0..)`. Integers and
/// floats count independently. An i32 or f32 argument's upper 32 bits are
/// POISON: the convention leaves them unspecified, so code that reads them
/// is wrong and must show.
fn aapcs64_regs(args: &[WasmValue]) -> Result<(Vec<u64>, Vec<u64>), EmuError> {
    let hi = POISON64 & !0xFFFF_FFFF;
    let (mut gp, mut fp) = (Vec::new(), Vec::new());
    for a in args {
        match *a {
            WasmValue::I32(v) => gp.push(hi | u64::from(v)),
            WasmValue::I64(v) => gp.push(v),
            WasmValue::F32(v) => fp.push(hi | u64::from(v)),
            WasmValue::F64(v) => fp.push(v),
        }
    }
    if gp.len() > 8 || fp.len() > 8 {
        return Err(EmuError::Abi(format!(
            "AAPCS64: {} integer and {} float arguments do not fit x0-x7 / v0-v7 \
             (stack arguments are not set up)",
            gp.len(),
            fp.len()
        )));
    }
    Ok((gp, fp))
}

/// Run an A64 function under AAPCS64.
///
/// Integer arguments go in x0-x7 and float arguments in v0-v7 (written as
/// d0-d7), see [`aapcs64_regs`]; every unused argument register holds
/// POISON. x19-x29 and d8-d15 are seeded and checked preserved over all 64
/// bits, SP is checked balanced, and x30 returns to the sentinel. The result
/// is read from x0 (the low 32 bits for an i32) or d0 (the low 32 bits for
/// an f32).
///
/// With `memory` (v0.92), that image is mapped at [`MEM_BASE`] — exactly its
/// length rounded up to a page, so an unguarded access past a page-sized
/// memory FAULTS (Illegal) instead of landing in a neighbour — `x28` is set
/// to [`MEM_BASE`] instead of a seed and still checked preserved, and the
/// image is read back after the run, a trap included.
fn run_a64(
    obj: &CompiledObject,
    sym: &crate::synth::FuncSym,
    sig: &Signature,
    args: &[WasmValue],
    cfg: &EmuConfig,
    memory: Option<&[u8]>,
) -> Result<EmuRun, EmuError> {
    let machine = Machine::AArch64;
    let (gp, fp) = aapcs64_regs(args)?;
    let mut emu = uc(Unicorn::new(Arch::ARM64, Mode::ARM), "Unicorn::new")?;
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
    poison_stack(&mut emu)?;
    uc(
        emu.mem_map(RETURN_ADDR, 0x1000, Prot::ALL),
        "map return page",
    )?;
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
    for i in 0..8usize {
        uc(
            emu.reg_write(
                RegisterARM64::X0 as i32 + i as i32,
                *gp.get(i).unwrap_or(&POISON64),
            ),
            "write x arg",
        )?;
        uc(
            emu.reg_write(
                RegisterARM64::D0 as i32 + i as i32,
                *fp.get(i).unwrap_or(&POISON64),
            ),
            "write v arg",
        )?;
    }
    // Every other caller-saved register a function may use as scratch: an
    // uninitialised read of one must not look like wasm's zero.
    for n in 8..19 {
        uc(
            emu.reg_write(RegisterARM64::X0 as i32 + n, POISON64),
            "poison x8-x18",
        )?;
    }
    for n in 16..32 {
        uc(
            emu.reg_write(RegisterARM64::D0 as i32 + n, POISON64),
            "poison d16-d31",
        )?;
    }
    let mem_len = memory.map_or(0, |m| m.len() as u64);
    if let Some(img) = memory {
        let mapped = ((mem_len + 0xFFF) & !0xFFF).max(0x1000);
        uc(
            emu.mem_map(MEM_BASE, mapped, Prot::READ | Prot::WRITE),
            "map memory",
        )?;
        uc(emu.mem_write(MEM_BASE, img), "write memory")?;
    }
    let x28 = RegisterARM64::X0 as i32 + 28;
    let mut seeds = Vec::new();
    for (k, (r, name)) in callee_saved(machine).into_iter().enumerate() {
        let v = if memory.is_some() && r == x28 {
            MEM_BASE
        } else {
            0xC0DE_0000_C0DE_0000 | k as u64
        };
        uc(emu.reg_write(r, v), "seed callee-saved")?;
        seeds.push((r, name, v));
    }
    uc(emu.reg_write(RegisterARM64::SP, STACK_TOP), "write SP")?;
    uc(emu.reg_write(RegisterARM64::X30, RETURN_ADDR), "write x30")?;
    let entry = TEXT_BASE + sym.offset;

    let r = emu.emu_start(entry, RETURN_ADDR, 0, cfg.budget);
    let pc_now = uc(emu.reg_read(RegisterARM64::PC), "read PC")?;
    let fault = match (hit.get(), r) {
        (Some((reported_pc, intno)), _) => Some(Fault::Hook { reported_pc, intno }),
        (None, Err(err)) => Some(Fault::Error { pc: pc_now, err }),
        (None, Ok(())) => None,
    };
    let outcome = if let Some(fault) = fault {
        let pc = fault_pc(machine, fault);
        let mut bytes = vec![0u8; 4];
        if emu.mem_read(pc, &mut bytes).is_err() {
            bytes.clear();
        }
        judge(machine, fault, &bytes, &(entry..entry + sym.size))
    } else if pc_now != RETURN_ADDR {
        EmuOutcome::Budget
    } else {
        let mut viol = Vec::new();
        for (r, name, v) in &seeds {
            if uc(emu.reg_read(*r), "read callee-saved")? != *v {
                viol.push(format!("{name} clobbered"));
            }
        }
        if uc(emu.reg_read(RegisterARM64::SP), "read SP")? != STACK_TOP {
            viol.push("SP imbalance".into());
        }
        if !viol.is_empty() {
            EmuOutcome::Illegal {
                pc: pc_now,
                reason: format!("ABI violated: {}", viol.join(", ")),
            }
        } else {
            let x0 = uc(emu.reg_read(RegisterARM64::X0), "read x0")?;
            let d0 = uc(emu.reg_read(RegisterARM64::D0), "read d0")?;
            EmuOutcome::Values(
                sig.results
                    .first()
                    .map(|t| {
                        vec![match t {
                            ValType::I32 => WasmValue::I32(x0 as u32),
                            ValType::I64 => WasmValue::I64(x0),
                            ValType::F32 => WasmValue::F32(d0 as u32),
                            ValType::F64 => WasmValue::F64(d0),
                        }]
                    })
                    .unwrap_or_default(),
            )
        }
    };
    Ok(EmuRun {
        outcome,
        cpu_model_readback: readback,
        memory: read_memory(&emu, mem_len)?,
        calls: Vec::new(),
    })
}

/// Run `func` from `obj` with `args` under `cfg`.
/// The `.text` image with every relocation resolved: a call to a defined
/// function to that function, a call to an undefined symbol to the stub of
/// the [`EmuEnv::imports`] entry of that name.
fn link_text(obj: &CompiledObject, env: &EmuEnv) -> Result<Vec<u8>, EmuError> {
    let mut text = obj.text.clone();
    for r in &obj.relocs {
        if r.r_type != R_RISCV_CALL_PLT || r.addend != 0 {
            return Err(EmuError::Env(format!(
                "relocation type {} addend {} at {:#x} is not linked",
                r.r_type, r.addend, r.offset
            )));
        }
        let target = match (r.target, r.undefined) {
            (Some(off), false) => TEXT_BASE + off,
            (None, true) => {
                let mut hits = env
                    .imports
                    .iter()
                    .enumerate()
                    .filter(|(_, (n, _, _))| *n == r.symbol);
                let (k, _) = hits.next().ok_or_else(|| {
                    EmuError::Env(format!(
                        "undefined symbol `{}` has no host function",
                        r.symbol
                    ))
                })?;
                if hits.next().is_some() {
                    return Err(EmuError::Env(format!("symbol `{}` is ambiguous", r.symbol)));
                }
                STUB_BASE + 4 * k as u64
            }
            _ => {
                return Err(EmuError::Env(format!(
                    "relocation at {:#x} names `{}`, neither in .text nor undefined",
                    r.offset, r.symbol
                )));
            }
        };
        let o = r.offset as usize;
        let word = |t: &[u8], at: usize| -> Result<u32, EmuError> {
            t.get(at..at + 4)
                .map(|b| u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
                .ok_or_else(|| EmuError::Env(format!("relocation at {at:#x} leaves .text")))
        };
        let (auipc, jalr) = (word(&text, o)?, word(&text, o + 4)?);
        if auipc & 0x7F != 0x17 || jalr & 0x707F != 0x67 {
            return Err(EmuError::Env(format!(
                "R_RISCV_CALL_PLT at {o:#x} is not on auipc+jalr ({auipc:#010x} {jalr:#010x})"
            )));
        }
        let v = target.wrapping_sub(TEXT_BASE + r.offset) as i64 as i32;
        let hi = (v.wrapping_add(0x800) >> 12) as u32;
        let lo = (v as u32).wrapping_sub(hi << 12) & 0xFFF;
        let auipc = (auipc & 0xFFF) | (hi << 12);
        let jalr = (jalr & 0x000F_FFFF) | (lo << 20);
        text[o..o + 4].copy_from_slice(&auipc.to_le_bytes());
        text[o + 4..o + 8].copy_from_slice(&jalr.to_le_bytes());
    }
    Ok(text)
}

/// Run `func` from `obj` with `args` under `cfg`. No memory is mapped and a
/// function carrying a relocation is refused; see [`run_env`].
pub fn run(
    obj: &CompiledObject,
    func: &str,
    sig: &Signature,
    args: &[WasmValue],
    cfg: &EmuConfig,
) -> Result<EmuRun, EmuError> {
    let relocs = obj.relocs_in(func);
    if relocs > 0 {
        return Err(EmuError::NeedsLink {
            func: func.to_string(),
            relocs,
        });
    }
    run_inner(obj, func, sig, args, cfg, None)
}

/// [`run`] with `env` mapped and the whole `.text` linked.
///
/// RV32: memory and host stubs. AArch64 (v0.92): memory ONLY — linear memory
/// 0 mapped at [`MEM_BASE`] with `x28` (the backend's base register,
/// `docs/embedder-abi-relocatable-aarch64.md`) pointing at it. An AArch64
/// object carrying any relocation, or an env with host functions, is refused:
/// nothing here links A64 relocations.
pub fn run_env(
    obj: &CompiledObject,
    func: &str,
    sig: &Signature,
    args: &[WasmValue],
    cfg: &EmuConfig,
    env: &EmuEnv,
) -> Result<EmuRun, EmuError> {
    match cfg.cpu.machine() {
        Machine::RiscV32 => {}
        Machine::AArch64 if env.imports.is_empty() && obj.relocs.is_empty() => {}
        Machine::AArch64 => {
            return Err(EmuError::Env(
                "AArch64: only a linear memory is set up (no host stubs, no \
                 relocations)"
                    .into(),
            ));
        }
        _ => {
            return Err(EmuError::Env(
                "a memory or host stubs are set up for RV32 and AArch64 only".into(),
            ));
        }
    }
    run_inner(obj, func, sig, args, cfg, Some(env))
}

fn run_inner(
    obj: &CompiledObject,
    func: &str,
    sig: &Signature,
    args: &[WasmValue],
    cfg: &EmuConfig,
    env: Option<&EmuEnv>,
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
    let text = match env {
        Some(env) if machine == Machine::RiscV32 => link_text(obj, env)?,
        _ => obj.text.clone(),
    };
    if machine == Machine::Arm && !sym.thumb {
        return Err(EmuError::NotThumb(func.to_string()));
    }
    let is_float = |t: &ValType| matches!(t, ValType::F32 | ValType::F64);
    let float_refused = match machine {
        Machine::AArch64 => false,
        // A VFP core reads a float result from s0/d0. Float PARAMETERS are
        // not set up (AAPCS-VFP back-filling is not implemented).
        Machine::Arm if cfg.cpu.vfp() => sig.params.iter().any(is_float),
        _ => sig.params.iter().chain(&sig.results).any(is_float),
    };
    if float_refused {
        return Err(EmuError::FloatAbi {
            func: func.to_string(),
            machine,
        });
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
    let words = match machine {
        Machine::Arm => aapcs_words(&sig.params, args)?,
        Machine::RiscV32 => ilp32_words(args)?,
        Machine::AArch64 => {
            let memory = env.and_then(|e| e.memory.as_deref());
            return run_a64(obj, &sym, sig, args, cfg, memory);
        }
        Machine::X86_64 => return x86_64::run(obj, &sym, sig, args, cfg),
    };

    let (arch, mode) = match machine {
        // NOT `Mode::MCLASS`: unicorn 2.1.x forces any MCLASS-mode CPU to
        // Cortex-M33 whatever model is requested (unicorn-engine-sys 2.1.5,
        // qemu/target/arm/cpu.c:2113). The M-profile models carry
        // ARM_FEATURE_M themselves, so plain THUMB + the model is M-class.
        Machine::Arm => (Arch::ARM, Mode::THUMB),
        Machine::RiscV32 => (Arch::RISCV, Mode::RISCV32),
        Machine::AArch64 => unreachable!("dispatched to run_a64 above"),
        Machine::X86_64 => unreachable!("dispatched to x86_64::run above"),
    };
    let mut emu = uc(Unicorn::new(arch, mode), "Unicorn::new")?;
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
    uc(emu.mem_write(TEXT_BASE, &text), "write text")?;
    uc(
        emu.mem_map(
            STACK_TOP - STACK_SIZE / 2,
            STACK_SIZE,
            Prot::READ | Prot::WRITE,
        ),
        "map stack",
    )?;
    poison_stack(&mut emu)?;
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

    let arg_regs: Vec<i32> = match machine {
        Machine::Arm => (0..4).map(|i| RegisterARM::R0 as i32 + i).collect(),
        Machine::RiscV32 => (10..18).map(|n| RegisterRISCV::X0 as i32 + n).collect(),
        Machine::AArch64 => unreachable!("dispatched to run_a64 above"),
        Machine::X86_64 => unreachable!("dispatched to x86_64::run above"),
    };

    // The environment: linear memory and host stubs.
    let calls: Rc<std::cell::RefCell<Vec<HostCall>>> = Rc::default();
    let host_trap: Rc<Cell<Option<u64>>> = Rc::new(Cell::new(None));
    let mut mem_len = 0u64;
    if let Some(env) = env {
        if let Some(img) = &env.memory {
            mem_len = img.len() as u64;
            let mapped = ((mem_len + 0xFFF) & !0xFFF).max(0x1000);
            uc(
                emu.mem_map(MEM_BASE, mapped, Prot::READ | Prot::WRITE),
                "map memory",
            )?;
            uc(emu.mem_write(MEM_BASE, img), "write memory")?;
        }
        if !env.imports.is_empty() {
            let n = env.imports.len() as u64;
            uc(
                emu.mem_map(STUB_BASE, ((4 * n + 0xFFF) & !0xFFF).max(0x1000), Prot::ALL),
                "map stubs",
            )?;
            for k in 0..n {
                uc(
                    emu.mem_write(STUB_BASE + 4 * k, &RV_RET.to_le_bytes()),
                    "write stub",
                )?;
            }
            let imports = env.imports.clone();
            let regs = arg_regs.clone();
            let calls2 = Rc::clone(&calls);
            let trap2 = Rc::clone(&host_trap);
            uc(
                emu.add_code_hook(STUB_BASE, STUB_BASE + 4 * n - 1, move |u, addr, _| {
                    let (name, sig, f) = &imports[((addr - STUB_BASE) / 4) as usize];
                    let mut words = Vec::new();
                    for r in &regs {
                        words.push(u.reg_read(*r).unwrap_or(0) as u32);
                    }
                    let mut at = 0;
                    let mut args = Vec::new();
                    for t in &sig.params {
                        let w = t.words();
                        args.push(WasmValue::from_words(
                            *t,
                            &words[at.min(8)..(at + w).min(8)],
                        ));
                        at += w;
                    }
                    let r = if at > 8 {
                        Err("stack arguments are not read".to_string())
                    } else {
                        f(&args)
                    };
                    calls2.borrow_mut().push(HostCall {
                        module: String::new(),
                        field: name.clone(),
                        args,
                        results: r.as_ref().ok().cloned(),
                    });
                    let results = match r {
                        Ok(v) if v.len() == sig.results.len() => v,
                        _ => {
                            trap2.set(Some(addr));
                            let _ = u.emu_stop();
                            return;
                        }
                    };
                    let out: Vec<u32> = results.iter().flat_map(|v| v.to_words()).collect();
                    // The psABI lets a callee change every caller-saved
                    // register: do so, so a value kept in one is caught.
                    for (k, r) in regs.iter().enumerate() {
                        let v = out.get(k).copied().unwrap_or(0xBAD0_0A00 | k as u32);
                        let _ = u.reg_write(*r, u64::from(v));
                    }
                    for (k, n) in [5, 6, 7, 28, 29, 30, 31].into_iter().enumerate() {
                        let _ = u.reg_write(
                            RegisterRISCV::X0 as i32 + n,
                            u64::from(0xBAD0_0700 | k as u32),
                        );
                    }
                }),
                "add stub hook",
            )?;
        }
    }
    for (i, r) in arg_regs.iter().enumerate() {
        uc(
            emu.reg_write(*r, u64::from(*words.get(i).unwrap_or(&POISON))),
            "write arg",
        )?;
    }
    if cfg.cpu.vfp() {
        // CPACR CP10/CP11 full access, then FPEXC.EN (off at reset on
        // silicon). Every D register is POISON, so an uninitialised VFP home
        // does not read as wasm's zero.
        uc(
            emu.reg_write(RegisterARM::C1_C0_2, 0x00F0_0000),
            "enable CPACR",
        )?;
        uc(
            emu.reg_write(RegisterARM::FPEXC, 0x4000_0000),
            "enable FPEXC",
        )?;
        for n in 0..16 {
            uc(
                emu.reg_write(RegisterARM::D0 as i32 + n, POISON64),
                "poison d0-d15",
            )?;
        }
    }
    let mut seeds = Vec::new();
    let s11 = RegisterRISCV::X0 as i32 + 27;
    for (k, (r, name)) in callee_saved(machine).into_iter().enumerate() {
        let v = if mem_len > 0 && machine == Machine::RiscV32 && r == s11 {
            MEM_BASE
        } else {
            0xC0DE_0000 | k as u64
        };
        uc(emu.reg_write(r, v), "seed callee-saved")?;
        seeds.push((r, name, v));
    }
    let (sp_reg, pc_reg) = match machine {
        Machine::Arm => (RegisterARM::SP as i32, RegisterARM::PC as i32),
        Machine::RiscV32 => (RegisterRISCV::SP as i32, RegisterRISCV::PC as i32),
        Machine::AArch64 => unreachable!("dispatched to run_a64 above"),
        Machine::X86_64 => unreachable!("dispatched to x86_64::run above"),
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
        Machine::AArch64 => unreachable!("dispatched to run_a64 above"),
        Machine::X86_64 => unreachable!("dispatched to x86_64::run above"),
    };

    // timeout 0: no wall-clock thread (see the module doc).
    let r = emu.emu_start(begin, RETURN_ADDR, 0, cfg.budget);
    let pc_now = uc(emu.reg_read(pc_reg), "read PC")? & !1;

    if let Some(pc) = host_trap.get() {
        let memory = read_memory(&emu, mem_len)?;
        return Ok(EmuRun {
            outcome: EmuOutcome::Trap {
                pc,
                insn: "host".into(),
            },
            cpu_model_readback: readback,
            memory,
            calls: calls.borrow().clone(),
        });
    }
    let fault = match (hit.get(), r) {
        (Some((reported_pc, intno)), _) => Some(Fault::Hook { reported_pc, intno }),
        (None, Err(err)) => Some(Fault::Error { pc: pc_now, err }),
        (None, Ok(())) => None,
    };
    let outcome = if let Some(fault) = fault {
        let pc = fault_pc(machine, fault);
        let mut bytes = vec![0u8; 4];
        if emu.mem_read(pc, &mut bytes).is_err() {
            bytes.truncate(2);
            if emu.mem_read(pc, &mut bytes).is_err() {
                bytes.clear();
            }
        }
        judge(machine, fault, &bytes, &(entry..entry + sym.size))
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
            // A float result on a VFP core is in d0 (s0 is its low half);
            // every other core was refused a float signature above.
            if sig.results.first().is_some_and(is_float) {
                let d0 = uc(emu.reg_read(RegisterARM::D0), "read d0")?;
                out_words = vec![d0 as u32, (d0 >> 32) as u32];
            }
            EmuOutcome::Values(
                sig.results
                    .first()
                    .map(|t| vec![WasmValue::from_words(*t, &out_words)])
                    .unwrap_or_default(),
            )
        }
    };
    let memory = read_memory(&emu, mem_len)?;
    Ok(EmuRun {
        outcome,
        cpu_model_readback: readback,
        memory,
        calls: calls.borrow().clone(),
    })
}

fn read_memory(emu: &Unicorn<'_, ()>, len: u64) -> Result<Option<Vec<u8>>, EmuError> {
    if len == 0 {
        return Ok(None);
    }
    let mut m = vec![0u8; len as usize];
    uc(emu.mem_read(MEM_BASE, &mut m), "read memory")?;
    Ok(Some(m))
}

#[cfg(test)]
mod tests {
    use super::*;

    const UDF: [u8; 2] = [0x00, 0xDE];
    const EBREAK: [u8; 4] = 0x0010_0073u32.to_le_bytes();
    const F: Range<u64> = 0x1000..0x1100;

    fn err(pc: u64, err: uc_error) -> Fault {
        Fault::Error { pc, err }
    }

    #[test]
    fn trap_needs_the_stop_path_and_the_bytes() {
        // The two real traps.
        assert_eq!(
            judge(Machine::Arm, err(0x1010, uc_error::INSN_INVALID), &UDF, &F),
            EmuOutcome::Trap {
                pc: 0x1010,
                insn: "udf".into()
            }
        );
        assert!(matches!(
            judge(
                Machine::RiscV32,
                err(0x1010, uc_error::INSN_INVALID),
                &EBREAK,
                &F
            ),
            EmuOutcome::Trap { pc: 0x1010, .. }
        ));
        // Right bytes, wrong stop path: ILLEGAL. (A bytes-only rule reds here.)
        for fault in [
            Fault::Hook {
                reported_pc: 0x1010,
                intno: 7,
            },
            err(0x1010, uc_error::EXCEPTION),
            err(0x1010, uc_error::READ_UNMAPPED),
        ] {
            assert!(
                matches!(
                    judge(Machine::Arm, fault, &UDF, &F),
                    EmuOutcome::Illegal { .. }
                ),
                "{fault:?}"
            );
        }
        let rv_hook = Fault::Hook {
            reported_pc: 0x1014,
            intno: 2,
        };
        assert!(matches!(
            judge(Machine::RiscV32, rv_hook, &EBREAK, &F),
            EmuOutcome::Illegal { pc: 0x1010, .. }
        ));
        // Right path, wrong bytes: ILLEGAL. Includes what synth never emits.
        for bytes in [
            vec![0x00u8, 0xBE],           // bkpt
            vec![0xF0, 0xF7, 0x00, 0xA0], // udf.w
            vec![0xFF, 0xFF, 0xFF, 0xFF], // undefined
        ] {
            assert!(matches!(
                judge(
                    Machine::Arm,
                    err(0x1010, uc_error::INSN_INVALID),
                    &bytes,
                    &F
                ),
                EmuOutcome::Illegal { .. }
            ));
        }
        for bytes in [
            vec![0x00u8, 0x00, 0x00, 0x00],        // c.unimp (zero padding)
            vec![0x02, 0x90, 0x00, 0x00],          // c.ebreak
            0xC000_1073u32.to_le_bytes().to_vec(), // unimp
            0x0000_0073u32.to_le_bytes().to_vec(), // ecall
        ] {
            assert!(matches!(
                judge(
                    Machine::RiscV32,
                    err(0x1010, uc_error::INSN_INVALID),
                    &bytes,
                    &F
                ),
                EmuOutcome::Illegal { .. }
            ));
        }
        // A real trap instruction OUTSIDE the function: ILLEGAL.
        assert!(matches!(
            judge(Machine::Arm, err(0x2000, uc_error::INSN_INVALID), &UDF, &F),
            EmuOutcome::Illegal { .. }
        ));
    }

    /// RQ-91-X86SKEL: an x86-64 trap is `ud2` (`0F 0B`) at RIP, stopped as
    /// UC_ERR_INSN_INVALID, inside the function — and nothing else. Garbage
    /// bytes stop the same way (REVIEW_2 X3), so a rule on the error class
    /// alone reds here; so does a rule on the bytes alone.
    #[test]
    fn x86_trap_needs_ud2_at_rip_and_the_stop_path() {
        const UD2: [u8; 2] = [0x0F, 0x0B];
        assert_eq!(
            judge(
                Machine::X86_64,
                err(0x1011, uc_error::INSN_INVALID),
                &UD2,
                &F
            ),
            EmuOutcome::Trap {
                pc: 0x1011,
                insn: "ud2".into()
            }
        );
        // An ODD address is not masked on x86-64 (it would be on ARM).
        assert_eq!(fault_pc(Machine::X86_64, err(0x1011, uc_error::OK)), 0x1011);
        for bytes in [
            vec![0x06u8],           // invalid in 64-bit mode
            vec![0x0F, 0x0F, 0xFF], // 3DNow! escape
            vec![0x0F, 0xFF],       // ud0
            vec![0x0F, 0xB9],       // ud1
            vec![0x0F],             // truncated
        ] {
            assert!(
                matches!(
                    judge(
                        Machine::X86_64,
                        err(0x1010, uc_error::INSN_INVALID),
                        &bytes,
                        &F
                    ),
                    EmuOutcome::Illegal { .. }
                ),
                "{bytes:02x?}"
            );
        }
        for fault in [
            Fault::Hook {
                reported_pc: 0x1010,
                intno: 6,
            },
            err(0x1010, uc_error::EXCEPTION),
        ] {
            assert!(matches!(
                judge(Machine::X86_64, fault, &UD2, &F),
                EmuOutcome::Illegal { .. }
            ));
        }
        assert!(matches!(
            judge(
                Machine::X86_64,
                err(0x2000, uc_error::INSN_INVALID),
                &UD2,
                &F
            ),
            EmuOutcome::Illegal { .. }
        ));
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
