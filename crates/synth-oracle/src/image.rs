//! The LINKED image: run functions of a self-contained Cortex-M ELF, as linked.
//!
//! [`crate::emulate`] maps one relocatable `.text` at a fixed base and calls a
//! function in it. That is a code-level check: it never sees the image synth
//! ships. Here the ELF's `PT_LOAD` segments are mapped AT THEIR LINKED
//! ADDRESSES, the image is booted through its OWN `Reset_Handler` up to the
//! `blx r0` into the entry function (so R9/R10/R11 hold what the shipped
//! startup put there), and each export is then called at its linked address.
//! This follows `scripts/repro/spec_exec_1636_differential.py`'s `Image`, with
//! these differences:
//!
//! - The CPU model is the TARGET's (Cortex-M4 for `cortex-m4`, Cortex-M7 for
//!   `cortex-m7dp`), set before anything is mapped and READ BACK, never the
//!   permissive "max" core. An instruction the core lacks is then a fault.
//! - A stop is a trap only when the PC reaches the image's `Trap_Handler`, or
//!   by [`crate::emulate::judge`]'s rule (the stop path AND the bytes say
//!   `udf`, inside the function). Any other fault or interrupt is ILLEGAL.
//! - R4-R8 are seeded and checked preserved, R9-R11 must still hold the boot
//!   values, and SP must balance, as in `emulate`.
//!
//! WHAT IS REFUSED, as in `emulate`: float signatures, stack arguments and
//! multi-value results. Memory effects are not compared; callers refuse
//! modules with a linear memory.

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::path::Path;
use std::rc::Rc;

use object::read::elf::{ElfFile32, FileHeader, ProgramHeader, Sym};
use object::{Object as _, ObjectSymbol as _};
use unicorn_engine::{Arch, Mode, Prot, RegisterARM, Unicorn};

use crate::compare::EmuOutcome;
use crate::emulate::{Cpu, EmuError, Fault, POISON, aapcs_words, judge};
use crate::synth::Machine;
use crate::value::{Signature, ValType, WasmValue};

/// Where a call returns to. Outside any address synth links to.
pub const RETURN_ADDR: u64 = 0x7FF0_0000;
/// The SCB page (CPACR lives at 0xE000ED88); the FPU targets' startup does an
/// RMW of CPACR, so the page is mapped.
const SCB_PAGE: u64 = 0xE000_E000;
/// Boot budget: the startup copies `.data` and zeroes `.bss`.
const BOOT_BUDGET: usize = 2_000_000;

fn uc<T>(r: Result<T, unicorn_engine::uc_error>, what: &str) -> Result<T, EmuError> {
    r.map_err(|e| EmuError::Unicorn(format!("{what}: {e:?}")))
}

fn page_down(a: u64) -> u64 {
    a & !0xFFF
}

fn page_up(a: u64) -> u64 {
    (a + 0xFFF) & !0xFFF
}

/// One call on the booted image.
#[derive(Clone, Debug)]
pub struct ImageRun {
    pub outcome: EmuOutcome,
    /// Instructions executed by this call, INCLUDING the `IT` and
    /// condition-failed instructions unicorn's code hook does not report.
    pub instructions: u64,
    /// The call's cost in Cortex-M4 worst-case cycles ([`crate::cycles`]),
    /// or why it could not be priced.
    pub cycles: Result<u64, String>,
}

/// Trace entries kept per call; a longer call is not priced.
const TRACE_CAP: usize = 100_000;

/// What the shipped startup must have established at its `blx r0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BootContract {
    /// R11: the linear-memory base, `__linear_memory_base`'s value.
    pub r11_linear_memory_base: u32,
    /// R10: the linear-memory size, `__linear_memory_base`'s size.
    pub r10_linear_memory_size: u32,
    /// SP: the vector table's initial SP.
    pub sp: u32,
    /// R0, the `blx r0` target: a function symbol (Thumb bit set).
    pub entry: (String, u32),
}

/// A self-contained image, booted.
pub struct BootedImage {
    emu: Unicorn<'static, ()>,
    cpu: Cpu,
    /// Function symbols by name: linked address (Thumb bit cleared), size.
    funcs: BTreeMap<String, (u64, u64)>,
    sp0: u64,
    /// R9, R10, R11 after the shipped startup ran.
    pub boot_r9_r11: [u32; 3],
    /// The boot contract, each register ASSERTED against the ELF.
    pub contract: BootContract,
    text: (u64, Vec<u8>),
    /// What `ctl_get_cpu_model` returned (asserted equal to the request).
    pub cpu_model_readback: i32,
    ram: (u64, Vec<u8>),
    trapped: Rc<Cell<bool>>,
    intr: Rc<Cell<Option<(u64, u32)>>>,
    trace: Rc<RefCell<Vec<(u64, u32)>>>,
}

impl BootedImage {
    /// Load `path` as linked and boot it on `cpu`. `fpu` enables the
    /// coprocessor access the FPU targets' startup expects.
    pub fn boot(path: &Path, cpu: Cpu, fpu: bool) -> Result<Self, EmuError> {
        let data =
            std::fs::read(path).map_err(|e| EmuError::Abi(format!("{}: {e}", path.display())))?;
        Self::boot_bytes(&data, cpu, fpu)
    }

    pub fn boot_bytes(data: &[u8], cpu: Cpu, fpu: bool) -> Result<Self, EmuError> {
        if cpu.machine() != Machine::Arm {
            return Err(EmuError::Abi(
                "a linked image is a Cortex-M image; RISC-V has none".into(),
            ));
        }
        let bad = |m: String| EmuError::Abi(m);
        let file = ElfFile32::<object::Endianness>::parse(data)
            .map_err(|e| bad(format!("not an ELF32 file: {e}")))?;
        let endian = file.endian();
        if file.elf_header().e_machine(endian) != object::elf::EM_ARM {
            return Err(bad("not an ARM ELF".into()));
        }
        if file.elf_header().e_type(endian) != object::elf::ET_EXEC {
            return Err(bad(
                "not a linked executable (ET_EXEC); a relocatable object is code-level only".into(),
            ));
        }
        // PT_LOAD segments: (vaddr, memsz, file bytes).
        let mut segs: Vec<(u64, u64, Vec<u8>)> = Vec::new();
        for ph in file
            .elf_program_headers()
            .iter()
            .filter(|p| p.p_type(endian) == object::elf::PT_LOAD)
        {
            let bytes = ph
                .data(endian, data)
                .map_err(|_| bad("PT_LOAD data out of range".into()))?
                .to_vec();
            segs.push((
                u64::from(ph.p_vaddr(endian)),
                u64::from(ph.p_memsz(endian)),
                bytes,
            ));
        }
        segs.sort_by_key(|s| s.0);
        let (text_va, text_sz, text) = segs
            .first()
            .cloned()
            .ok_or_else(|| bad("no PT_LOAD segment".into()))?;
        if text.len() < 8 {
            return Err(bad("first segment has no vector table".into()));
        }
        let word = |o: usize| u32::from_le_bytes([text[o], text[o + 1], text[o + 2], text[o + 3]]);
        let sp0 = u64::from(word(0));
        let reset = u64::from(word(4)) & !1;

        let mut funcs = BTreeMap::new();
        for sym in file.symbols() {
            if sym.kind() != object::SymbolKind::Text {
                continue;
            }
            let Ok(name) = sym.name() else { continue };
            if name.is_empty() || name.starts_with('$') {
                continue;
            }
            let raw = u64::from(sym.elf_symbol().st_value(endian));
            let size = u64::from(sym.elf_symbol().st_size(endian));
            funcs.insert(name.to_string(), (raw & !1, size));
        }

        let mut emu = uc(Unicorn::new(Arch::ARM, Mode::THUMB), "Unicorn::new")?;
        // BEFORE any mapping (see emulate.rs: not Mode::MCLASS, which forces
        // Cortex-M33 in unicorn 2.1.x).
        let requested = cpu.model_id();
        uc(emu.ctl_set_cpu_model(requested), "ctl_set_cpu_model")?;
        let readback = uc(emu.ctl_get_cpu_model(), "ctl_get_cpu_model")?;
        if readback != requested {
            return Err(EmuError::CpuModelMismatch {
                requested,
                readback,
            });
        }

        // Text, as linked.
        let tlo = page_down(text_va);
        let thi = page_up(text_va + text_sz.max(text.len() as u64));
        uc(emu.mem_map(tlo, thi - tlo, Prot::ALL), "map text")?;
        uc(emu.mem_write(text_va, &text), "write text")?;
        // RAM: every other segment, up to the initial SP.
        let others: Vec<_> = segs.iter().skip(1).collect();
        let ram_lo = page_down(
            others
                .iter()
                .map(|s| s.0)
                .min()
                .unwrap_or(sp0.saturating_sub(0x2_0000)),
        );
        let ram_hi = page_up(
            others
                .iter()
                .map(|s| s.0 + s.1)
                .chain([sp0])
                .max()
                .unwrap_or(sp0),
        );
        if ram_lo < thi && tlo < ram_hi {
            return Err(bad(format!(
                "RAM {ram_lo:#x}..{ram_hi:#x} overlaps text {tlo:#x}..{thi:#x}"
            )));
        }
        uc(
            emu.mem_map(ram_lo, ram_hi - ram_lo, Prot::READ | Prot::WRITE),
            "map RAM",
        )?;
        for (va, _, bytes) in &others {
            if !bytes.is_empty() {
                uc(emu.mem_write(*va, bytes), "write segment")?;
            }
        }
        uc(
            emu.mem_map(page_down(RETURN_ADDR), 0x1000, Prot::ALL),
            "map return page",
        )?;
        uc(
            emu.mem_map(SCB_PAGE, 0x1000, Prot::READ | Prot::WRITE),
            "map SCB",
        )?;
        if fpu {
            uc(
                emu.reg_write(RegisterARM::C1_C0_2 as i32, 0x00F0_0000),
                "CPACR",
            )?;
            uc(
                emu.reg_write(RegisterARM::FPEXC as i32, 0x4000_0000),
                "FPEXC",
            )?;
        }

        // Boot: run the shipped Reset_Handler up to its `blx r0` (0x4780).
        let mut pc = reset;
        let blx = loop {
            let off = pc
                .checked_sub(text_va)
                .ok_or_else(|| bad("Reset_Handler below text".into()))?
                as usize;
            let hw = text
                .get(off..off + 2)
                .map(|b| u16::from_le_bytes([b[0], b[1]]))
                .ok_or_else(|| bad("no `blx r0` in Reset_Handler".into()))?;
            if hw == 0x4780 {
                break pc;
            }
            pc += if matches!(hw >> 11, 0b11101..=0b11111) {
                4
            } else {
                2
            };
            if pc - reset > 0x400 {
                return Err(bad("no `blx r0` within 1 KiB of Reset_Handler".into()));
            }
        };
        uc(emu.reg_write(RegisterARM::SP as i32, sp0), "boot SP")?;
        uc(
            emu.emu_start(reset | 1, blx, 0, BOOT_BUDGET),
            "boot through Reset_Handler",
        )?;
        let now = uc(emu.reg_read(RegisterARM::PC as i32), "boot PC")? & !1;
        if now != blx {
            return Err(bad(format!(
                "boot stopped at {now:#x}, not the `blx r0` at {blx:#x}"
            )));
        }
        let r = |reg: RegisterARM, emu: &Unicorn<()>| {
            emu.reg_read(reg as i32).map(|v| v as u32).unwrap_or(0)
        };
        let boot_r9_r11 = [
            r(RegisterARM::R9, &emu),
            r(RegisterARM::R10, &emu),
            r(RegisterARM::R11, &emu),
        ];
        // The boot is LOAD-BEARING: what the startup established is checked
        // against the ELF, not just recorded (REVIEW_17 finding 4). A startup
        // that skips or corrupts the memory contract, or would jump to
        // anything but a function, is refused here.
        let mem = file
            .symbols()
            .find(|s| s.name() == Ok("__linear_memory_base"))
            .ok_or_else(|| {
                bad("no __linear_memory_base symbol: the boot contract cannot be checked".into())
            })?;
        let want_r11 = mem.elf_symbol().st_value(endian);
        let want_r10 = mem.elf_symbol().st_size(endian);
        let r0 = r(RegisterARM::R0, &emu);
        let sp = r(RegisterARM::SP, &emu);
        let mut broken = Vec::new();
        if boot_r9_r11[2] != want_r11 {
            broken.push(format!(
                "R11 = {:#x}, __linear_memory_base = {want_r11:#x}",
                boot_r9_r11[2]
            ));
        }
        if boot_r9_r11[1] != want_r10 {
            broken.push(format!(
                "R10 = {:#x}, linear memory size = {want_r10:#x}",
                boot_r9_r11[1]
            ));
        }
        if u64::from(sp) != sp0 {
            broken.push(format!("SP = {sp:#x}, vector table SP = {sp0:#x}"));
        }
        let entry = funcs
            .iter()
            .find(|(n, (a, _))| {
                *a == u64::from(r0 & !1)
                    && !matches!(
                        n.as_str(),
                        "Reset_Handler" | "Default_Handler" | "Trap_Handler"
                    )
            })
            .map(|(n, _)| n.clone());
        match &entry {
            Some(_) if r0 & 1 == 1 => {}
            Some(_) => broken.push(format!("entry R0 = {r0:#x} has no Thumb bit")),
            None => broken.push(format!("entry R0 = {r0:#x} is not a function symbol")),
        }
        if !broken.is_empty() {
            return Err(bad(format!("boot contract broken: {}", broken.join("; "))));
        }
        let contract = BootContract {
            r11_linear_memory_base: want_r11,
            r10_linear_memory_size: want_r10,
            sp,
            entry: (entry.unwrap_or_default(), r0),
        };

        // Hooks: Trap_Handler reached = trap; any interrupt = recorded; every
        // instruction counted.
        let trapped = Rc::new(Cell::new(false));
        if let Some(&(trap, _)) = funcs.get("Trap_Handler") {
            let t = Rc::clone(&trapped);
            uc(
                emu.add_code_hook(trap, trap + 1, move |u, _, _| {
                    t.set(true);
                    let _ = u.emu_stop();
                }),
                "Trap_Handler hook",
            )?;
        }
        let intr: Rc<Cell<Option<(u64, u32)>>> = Rc::new(Cell::new(None));
        let i2 = Rc::clone(&intr);
        uc(
            emu.add_intr_hook(move |u, intno| {
                i2.set(Some((u.pc_read().unwrap_or(u64::MAX), intno)));
                let _ = u.emu_stop();
            }),
            "intr hook",
        )?;
        let trace: Rc<RefCell<Vec<(u64, u32)>>> = Rc::new(RefCell::new(Vec::new()));
        let t2 = Rc::clone(&trace);
        uc(
            emu.add_code_hook(1, 0, move |_, addr, size| {
                let mut t = t2.borrow_mut();
                if t.len() <= TRACE_CAP {
                    t.push((addr, size));
                }
            }),
            "trace hook",
        )?;

        let mut ram = vec![0u8; (ram_hi - ram_lo) as usize];
        uc(emu.mem_read(ram_lo, &mut ram), "snapshot RAM")?;

        Ok(Self {
            emu,
            cpu,
            funcs,
            sp0,
            boot_r9_r11,
            contract,
            text: (text_va, text.clone()),
            cpu_model_readback: readback,
            ram: (ram_lo, ram),
            trapped,
            intr,
            trace,
        })
    }

    pub fn cpu(&self) -> Cpu {
        self.cpu
    }

    /// The linked function symbols (name -> (address, size)).
    pub fn funcs(&self) -> &BTreeMap<String, (u64, u64)> {
        &self.funcs
    }

    /// Overwrite bytes of the mapped image (for planted negative controls).
    pub fn patch(&mut self, addr: u64, bytes: &[u8]) -> Result<(), EmuError> {
        uc(self.emu.mem_write(addr, bytes), "patch")
    }

    /// Call `func(args)` from the post-boot state, with `budget` instructions.
    pub fn call(
        &mut self,
        func: &str,
        sig: &Signature,
        args: &[WasmValue],
        budget: usize,
    ) -> Result<ImageRun, EmuError> {
        let &(entry, size) = self
            .funcs
            .get(func)
            .ok_or_else(|| EmuError::NoSymbol(func.to_string()))?;
        if sig
            .params
            .iter()
            .chain(&sig.results)
            .any(|t| matches!(t, ValType::F32 | ValType::F64))
        {
            return Err(EmuError::FloatAbi {
                func: func.to_string(),
                machine: Machine::Arm,
            });
        }
        if sig.results.len() > 1 {
            return Err(EmuError::Abi(
                "multi-value results are not read back".into(),
            ));
        }
        if args.len() != sig.params.len() || args.iter().zip(&sig.params).any(|(a, t)| a.ty() != *t)
        {
            return Err(EmuError::Abi(format!(
                "arguments {args:?} do not match params {:?}",
                sig.params
            )));
        }
        let words = aapcs_words(&sig.params, args)?;
        let emu = &mut self.emu;
        // Every call starts from the post-boot RAM image.
        uc(emu.mem_write(self.ram.0, &self.ram.1), "restore RAM")?;
        let reg = |i: i32| RegisterARM::R0 as i32 + i;
        for i in 0..4 {
            uc(
                emu.reg_write(reg(i), u64::from(*words.get(i as usize).unwrap_or(&POISON))),
                "arg",
            )?;
        }
        let mut keep: Vec<(i32, String, u32)> = Vec::new();
        for i in 4..9 {
            let v = 0xC0DE_0000 | i as u32;
            uc(emu.reg_write(reg(i), u64::from(v)), "seed")?;
            keep.push((reg(i), format!("R{i}"), v));
        }
        for (k, i) in (9..12).enumerate() {
            let v = self.boot_r9_r11[k];
            uc(emu.reg_write(reg(i), u64::from(v)), "contract")?;
            keep.push((reg(i), format!("R{i} (boot contract)"), v));
        }
        uc(emu.reg_write(reg(12), u64::from(POISON)), "R12")?;
        uc(emu.reg_write(RegisterARM::SP as i32, self.sp0), "SP")?;
        uc(emu.reg_write(RegisterARM::LR as i32, RETURN_ADDR | 1), "LR")?;
        self.trapped.set(false);
        self.intr.set(None);
        self.trace.borrow_mut().clear();

        let r = emu.emu_start(entry | 1, RETURN_ADDR, 0, budget);
        let pc_now = uc(emu.reg_read(RegisterARM::PC as i32), "PC")? & !1;
        let trace = std::mem::take(&mut *self.trace.borrow_mut());
        let func_range = entry..entry + size;

        let outcome = if self.trapped.get() {
            EmuOutcome::Trap {
                pc: pc_now,
                insn: "Trap_Handler".into(),
            }
        } else if let Some((reported_pc, intno)) = self.intr.get() {
            EmuOutcome::Illegal {
                pc: reported_pc & !1,
                reason: format!("interrupt {intno}"),
            }
        } else if let Err(err) = r {
            let mut bytes = vec![0u8; 4];
            if emu.mem_read(pc_now, &mut bytes).is_err() {
                bytes.truncate(2);
                if emu.mem_read(pc_now, &mut bytes).is_err() {
                    bytes.clear();
                }
            }
            judge(
                Machine::Arm,
                Fault::Error { pc: pc_now, err },
                &bytes,
                &func_range,
            )
        } else if pc_now != RETURN_ADDR {
            EmuOutcome::Budget
        } else {
            let mut viol = Vec::new();
            for (r, name, v) in &keep {
                if uc(emu.reg_read(*r), "read")? as u32 != *v {
                    viol.push(format!("{name} clobbered"));
                }
            }
            if uc(emu.reg_read(RegisterARM::SP as i32), "SP")? as u32 != self.sp0 as u32 {
                viol.push("SP imbalance".into());
            }
            if !viol.is_empty() {
                EmuOutcome::Illegal {
                    pc: pc_now,
                    reason: format!("ABI violated: {}", viol.join(", ")),
                }
            } else {
                let n: usize = sig.results.iter().map(|t| t.words()).sum();
                let mut out = Vec::new();
                for i in 0..n as i32 {
                    out.push(uc(emu.reg_read(reg(i)), "result")? as u32);
                }
                EmuOutcome::Values(
                    sig.results
                        .first()
                        .map(|t| vec![WasmValue::from_words(*t, &out)])
                        .unwrap_or_default(),
                )
            }
        };
        let trapped = matches!(
            outcome,
            EmuOutcome::Trap { .. } | EmuOutcome::Illegal { .. }
        );
        let (tva, text) = (&self.text.0, &self.text.1);
        let fetch = |a: u64| -> Option<u16> {
            let o = a.checked_sub(*tva)? as usize;
            Some(u16::from_le_bytes([*text.get(o)?, *text.get(o + 1)?]))
        };
        let priced = if trace.len() > TRACE_CAP {
            Err(format!("more than {TRACE_CAP} instructions; not priced"))
        } else {
            crate::cycles::price(&trace, pc_now, trapped, &fetch)
        };
        let instructions = priced.as_ref().map_or(trace.len() as u64, |p| p.1);
        Ok(ImageRun {
            outcome,
            instructions,
            cycles: priced.map(|p| p.0),
        })
    }
}
