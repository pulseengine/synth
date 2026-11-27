//! The HOSTED emulator: run exports of a host-linked ARM object the way an
//! embedder does, under unicorn.
//!
//! [`crate::emulate`] runs one call-free function and refuses relocations and
//! linear memory. A module that calls a function import is a different artifact: an
//! `ET_REL` object the embedder links, whose import calls are `bl <field>`
//! against undefined symbols and whose linear memory is wherever the embedder
//! put it (`docs/embedder-abi-relocatable-arm.md`). This module plays that
//! embedder:
//!
//! - **Linking.** Every `.text` relocation must be `R_ARM_THM_CALL`. One
//!   against a symbol defined in `.text` is resolved in place. One against an
//!   undefined symbol must name a FUNCTION IMPORT of the module by its bare
//!   wasm field name; it is resolved to a host stub. Any other symbol is
//!   [`EmuError::UnresolvedSymbol`] unless the test supplied a raw stub for it
//!   ([`HostConfig::raw_symbol`]): no embedder contract says what a call to it
//!   does, so it is not guessed.
//! - **Host stubs.** A stub reads its arguments per AAPCS (R0-R3, then the stack) and the
//!   import's own signature, calls the SAME host function the reference was
//!   given, logs the call, writes the result, and then CLOBBERS every
//!   caller-saved register that does not carry the result (R0-R3, R12) with
//!   [`CLOBBER`] values. AAPCS lets a callee do exactly that, so code that
//!   keeps a live value in one of them across the call reads the clobber.
//! - **The register contract.** R11 = memory 0's base (the test chooses the
//!   address), R10 = its size in bytes, R9 = an UNMAPPED address (no globals
//!   table is materialized, so a global access faults instead of reading
//!   zeros). All three, R4-R8 and SP are checked unchanged when the export
//!   returns.
//! - **Internal calls.** Every call that enters a function of the object
//!   (through its symbol, from anywhere in `.text`) is held to AAPCS too:
//!   when it returns, R4-R11 must be what they were at its entry, and R2, R3
//!   and R12 are then overwritten with [`CLOBBER`] values, as after a host
//!   call. Without this a callee that loses R4 is invisible whenever its
//!   caller keeps nothing in R4 across the call (the caller's own epilogue
//!   restores the export-level seed), and a value wrongly kept in R2/R3
//!   across a call to a leaf that does not touch them reads back intact.
//!   R0 and R1 are left alone: they may carry the callee's result.
//! - **Sequences.** One image runs several calls; linear memory persists
//!   between them, so a store through one export is read through another.
//!
//! - **The start function** (Refs #1046, #1786). A module with a `(start
//!   ...)` section is linked only when the object defines the GLOBAL
//!   `__synth_start` (`synth compile --embedder-runs-start`). Then [`Hosted::link`]
//!   plays the embedder's instantiation step: it calls `__synth_start` once,
//!   under the same register contract as an export, before any export can
//!   run, and fails the link unless it returns cleanly. kiln runs the start
//!   function at instantiation, so the two engines start every sequence from
//!   the same state. Without the symbol the module is refused as before.
//!
//! A stub reads stack-passed arguments too (Refs #1785: the full base-AAPCS
//! layout, 8-aligned i64 slots, no register back-fill) and fails the run when
//! SP is not 8-byte aligned at the call.
//!
//! REFUSED with a typed error rather than run: A32 code, float arguments at
//! an import boundary, and any module that needs instantiation state this
//! harness does not write ([`crate::value::uninstantiated_state`]).

use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

use unicorn_engine::{Arch, Mode, Prot, RegisterARM, Unicorn};

use crate::compare::EmuOutcome;
use crate::emulate::{
    Cpu, EmuError, Fault, POISON, RETURN_ADDR, STACK_SIZE, STACK_TOP, TEXT_BASE, aapcs_words,
    fault_pc, judge, uc,
};
use crate::reference::{HostCall, HostFn, Imports};
use crate::synth::{CompiledObject, Machine, R_ARM_THM_CALL, patch_thm_call};
use crate::value::{
    FuncImport, Signature, ValType, WasmValue, export_signature, function_imports,
    memory0_initial_bytes, start_function, uninstantiated_state_with,
};

/// The symbol `synth compile --embedder-runs-start` defines for the module's
/// start function, which the embedder calls once before any export (#1046).
pub const START_SYMBOL: &str = "__synth_start";

/// Where the host stubs live: one `bx lr` every [`STUB_STRIDE`] bytes.
pub const STUB_BASE: u64 = 0x0050_0000;
const STUB_STRIDE: u64 = 4;
/// What a host stub leaves in a caller-saved register that carries no
/// result: `CLOBBER | register number`.
pub const CLOBBER: u32 = 0xBAD0_0000;
/// R9 on entry: unmapped, so a globals-table access faults.
pub const GLOBALS_UNMAPPED: u32 = 0x7000_0000;
/// R11 on entry for a module with no memory: unmapped.
pub const LINMEM_UNMAPPED: u32 = 0x6000_0000;

/// A stub for a symbol that is NOT a function import: it sees R0-R3 as they
/// arrive and returns what R0 holds afterwards.
pub type RawStub = Arc<dyn Fn([u32; 4]) -> u32 + Send + Sync>;

/// How the embedder is set up.
#[derive(Clone)]
pub struct HostConfig {
    pub cpu: Cpu,
    /// Maximum instructions per call.
    pub budget: usize,
    /// R11: where memory 0 is mapped. Must be 4 KiB aligned.
    pub linmem_base: u32,
    /// Extra zero-filled RAM `(base, len)`, both 4 KiB aligned: memory an
    /// embedder's board has that is NOT the module's linear memory.
    pub ram: Vec<(u32, u32)>,
    raw: Vec<(String, RawStub)>,
}

impl HostConfig {
    pub fn new(cpu: Cpu, linmem_base: u32) -> Self {
        Self {
            cpu,
            budget: 1_000_000,
            linmem_base,
            ram: Vec::new(),
            raw: Vec::new(),
        }
    }

    /// Also map `len` bytes of zero-filled RAM at `base`.
    pub fn ram(mut self, base: u32, len: u32) -> Self {
        self.ram.push((base, len));
        self
    }

    /// Serve the non-import symbol `name` with `f` (see [`RawStub`]).
    pub fn raw_symbol<F>(mut self, name: &str, f: F) -> Self
    where
        F: Fn([u32; 4]) -> u32 + Send + Sync + 'static,
    {
        self.raw.push((name.to_string(), Arc::new(f)));
        self
    }
}

enum Stub {
    Import { imp: FuncImport, f: HostFn },
    Raw { name: String, f: RawStub },
}

#[derive(Default)]
struct Shared {
    log: Vec<HostCall>,
    failure: Option<String>,
    /// Internal calls in progress, innermost last.
    frames: Vec<Frame>,
    /// Internal calls checked on return, over the image's lifetime.
    internal_returns: usize,
}

/// One internal call in progress: where it returns, SP at its entry, and the
/// registers the callee must preserve (R4-R11).
struct Frame {
    callee: u64,
    ret: u64,
    sp: u64,
    saved: [u64; 8],
}

/// One emulated call into the hosted image.
#[derive(Clone, Debug)]
pub struct HostedRun {
    pub outcome: EmuOutcome,
    /// Every host call the machine code made during this call, in order.
    pub calls: Vec<HostCall>,
}

/// A linked, mapped object. Linear memory persists across [`Hosted::call`]s.
pub struct Hosted {
    emu: Unicorn<'static, ()>,
    wasm: Vec<u8>,
    obj: CompiledObject,
    shared: Rc<RefCell<Shared>>,
    hit: Rc<RefCell<Option<(u64, u32)>>>,
    r10: u32,
    r11: u32,
    budget: usize,
    pub cpu_model_readback: i32,
}

/// Read an import's arguments per base AAPCS (Refs #1785): an i64 takes the
/// next EVEN register pair (an odd NCRN is skipped and never back-filled);
/// one that does not fit sets NCRN to 4 and is read from the next 8-aligned
/// stacked-argument address, and every later argument is read from the stack
/// too. `stack(off)` reads the word at `SP + off` as the stub sees it.
fn args_from_aapcs(sig: &Signature, regs: [u32; 4], stack: &dyn Fn(u32) -> u32) -> Vec<WasmValue> {
    let (mut ncrn, mut nsaa) = (0usize, 0u32);
    let mut out = Vec::new();
    for t in &sig.params {
        let n = t.words();
        if n == 2 && ncrn % 2 == 1 {
            ncrn += 1;
        }
        let words: Vec<u32> = if ncrn + n <= 4 {
            ncrn += n;
            regs[ncrn - n..ncrn].to_vec()
        } else {
            ncrn = 4;
            if n == 2 && !nsaa.is_multiple_of(8) {
                nsaa += 4;
            }
            nsaa += 4 * n as u32;
            (0..n as u32)
                .map(|w| stack(nsaa - 4 * n as u32 + 4 * w))
                .collect()
        };
        out.push(WasmValue::from_words(*t, &words));
    }
    out
}

/// The boundary shapes a host stub can carry: integer arguments (in R0-R3
/// and on the stack, per AAPCS) and at most one integer result.
fn check_import_abi(imp: &FuncImport) -> Result<(), EmuError> {
    let name = format!("{}::{}", imp.module, imp.field);
    if imp
        .sig
        .params
        .iter()
        .chain(&imp.sig.results)
        .any(|t| matches!(t, ValType::F32 | ValType::F64))
    {
        return Err(EmuError::Abi(format!(
            "import {name} has a float in its signature (the VFP boundary is not set up)"
        )));
    }
    if imp.sig.results.len() > 1 {
        return Err(EmuError::Abi(format!(
            "import {name} returns more than one value"
        )));
    }
    Ok(())
}

fn page_up(n: u64) -> u64 {
    (n + 0xFFF) & !0xFFF
}

impl Hosted {
    /// Link `obj` (compiled from `wasm`) against host stubs for `imports` and
    /// map it with linear memory per `cfg`.
    pub fn link(
        obj: &CompiledObject,
        wasm: &[u8],
        imports: &Imports,
        cfg: &HostConfig,
    ) -> Result<Self, EmuError> {
        if obj.machine != Machine::Arm || cfg.cpu == Cpu::Rv32Imac {
            return Err(EmuError::WrongMachine {
                object: obj.machine,
                cpu: cfg.cpu,
            });
        }
        // A start function is instantiation state the harness CAN set up,
        // but only through the symbol the embedder contract names.
        let start = start_function(wasm).map_err(EmuError::Abi)?;
        let runs_start = start.is_some() && obj.func(START_SYMBOL).is_some_and(|f| f.global);
        if let Some(what) = uninstantiated_state_with(wasm, runs_start).map_err(EmuError::Abi)? {
            return Err(EmuError::Uninstantiated(what));
        }
        let func_imports = function_imports(wasm).map_err(EmuError::Abi)?;

        // Resolve every relocation, allocating a stub per external symbol.
        let mut stubs: Vec<Stub> = Vec::new();
        let mut stub_of: Vec<(String, usize)> = Vec::new();
        let mut text = obj.text.clone();
        for r in &obj.relocs {
            if r.r_type != R_ARM_THM_CALL {
                return Err(EmuError::Reloc(format!(
                    "relocation type {} at {:#x} against `{}` (only R_ARM_THM_CALL is resolved)",
                    r.r_type, r.offset, r.symbol
                )));
            }
            let dest = match r.target {
                Some(off) => TEXT_BASE + off,
                None => {
                    let idx = match stub_of.iter().find(|(n, _)| *n == r.symbol) {
                        Some((_, i)) => *i,
                        None => {
                            let matches: Vec<&FuncImport> = func_imports
                                .iter()
                                .filter(|i| i.field == r.symbol)
                                .collect();
                            let stub = if let Some((_, f)) =
                                cfg.raw.iter().find(|(n, _)| *n == r.symbol)
                            {
                                Stub::Raw {
                                    name: r.symbol.clone(),
                                    f: Arc::clone(f),
                                }
                            } else {
                                // The symbol IS the bare field name. Two
                                // imports sharing a field (different modules)
                                // cannot be told apart by it.
                                let [imp] = matches[..] else {
                                    return Err(EmuError::UnresolvedSymbol(r.symbol.clone()));
                                };
                                check_import_abi(imp)?;
                                let f = imports.get(&imp.module, &imp.field).ok_or_else(|| {
                                    EmuError::UnresolvedSymbol(format!(
                                        "{} (import {}::{} has no host function)",
                                        r.symbol, imp.module, imp.field
                                    ))
                                })?;
                                Stub::Import {
                                    imp: imp.clone(),
                                    f: Arc::clone(f),
                                }
                            };
                            stubs.push(stub);
                            stub_of.push((r.symbol.clone(), stubs.len() - 1));
                            stubs.len() - 1
                        }
                    };
                    STUB_BASE + idx as u64 * STUB_STRIDE
                }
            };
            patch_thm_call(&mut text, r.offset, TEXT_BASE + r.offset, dest)
                .map_err(EmuError::Reloc)?;
        }

        // NOT `Mode::MCLASS`: see `emulate::run`.
        let mut emu = uc(Unicorn::new(Arch::ARM, Mode::THUMB), "Unicorn::new")?;
        let requested = cfg.cpu.model_id();
        uc(emu.ctl_set_cpu_model(requested), "ctl_set_cpu_model")?;
        let readback = uc(emu.ctl_get_cpu_model(), "ctl_get_cpu_model")?;
        if readback != requested {
            return Err(EmuError::CpuModelMismatch {
                requested,
                readback,
            });
        }

        uc(
            emu.mem_map(TEXT_BASE, page_up(text.len() as u64).max(0x1000), Prot::ALL),
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
        uc(
            emu.mem_map(RETURN_ADDR, 0x1000, Prot::ALL),
            "map return page",
        )?;
        let stub_len = page_up((stubs.len() as u64 * STUB_STRIDE).max(1));
        uc(emu.mem_map(STUB_BASE, stub_len, Prot::ALL), "map stubs")?;
        // `bx lr` at every stub; `udf #0xfe` between them, so a branch that
        // lands off a stub start does not slide into the next one.
        let mut page = Vec::with_capacity(stub_len as usize);
        while (page.len() as u64) < stub_len {
            page.extend_from_slice(&[0x70, 0x47, 0xFE, 0xDE]);
        }
        uc(emu.mem_write(STUB_BASE, &page), "write stubs")?;

        let linmem = memory0_initial_bytes(wasm).map_err(EmuError::Abi)?;
        let (r10, r11) = match linmem {
            Some(bytes) => {
                let bytes32 = u32::try_from(bytes)
                    .map_err(|_| EmuError::Abi(format!("memory 0 is {bytes} bytes")))?;
                if cfg.linmem_base & 0xFFF != 0 {
                    return Err(EmuError::Abi(format!(
                        "linmem base {:#x} is not 4 KiB aligned",
                        cfg.linmem_base
                    )));
                }
                if bytes > 0 {
                    uc(
                        emu.mem_map(
                            u64::from(cfg.linmem_base),
                            page_up(bytes),
                            Prot::READ | Prot::WRITE,
                        ),
                        "map linear memory",
                    )?;
                }
                (bytes32, cfg.linmem_base)
            }
            None => (0, LINMEM_UNMAPPED),
        };
        for (base, len) in &cfg.ram {
            uc(
                emu.mem_map(u64::from(*base), u64::from(*len), Prot::READ | Prot::WRITE),
                "map extra RAM",
            )?;
        }

        let shared = Rc::new(RefCell::new(Shared::default()));
        let sh = Rc::clone(&shared);
        let n_stubs = stubs.len() as u64;
        uc(
            emu.add_code_hook(STUB_BASE, STUB_BASE + stub_len - 1, move |u, addr, _| {
                let off = addr - STUB_BASE;
                if !off.is_multiple_of(STUB_STRIDE) || off / STUB_STRIDE >= n_stubs {
                    return;
                }
                let reg = |u: &Unicorn<'_, ()>, i: i32| {
                    u.reg_read(RegisterARM::R0 as i32 + i).unwrap_or(0) as u32
                };
                let regs = [reg(u, 0), reg(u, 1), reg(u, 2), reg(u, 3)];
                let sp = u.reg_read(RegisterARM::SP as i32).unwrap_or(0) as u32;
                let stack = |off: u32| {
                    let mut b = [0u8; 4];
                    match u.mem_read(u64::from(sp.wrapping_add(off)), &mut b) {
                        Ok(()) => u32::from_le_bytes(b),
                        Err(_) => POISON,
                    }
                };
                // What R0-R3 hold on return: the result words, then clobber.
                let mut out = [CLOBBER, CLOBBER | 1, CLOBBER | 2, CLOBBER | 3];
                match &stubs[(off / STUB_STRIDE) as usize] {
                    Stub::Import { imp, f } => {
                        let args = args_from_aapcs(&imp.sig, regs, &stack);
                        let r = f(&args);
                        let mut s = sh.borrow_mut();
                        // AAPCS 5.2.1.2: SP is 8-byte aligned at a public
                        // interface, so an 8-aligned NSAA is 8-aligned in memory.
                        if !sp.is_multiple_of(8) {
                            s.failure = Some(format!(
                                "call to {}::{} with SP {sp:#x}, not 8-byte aligned",
                                imp.module, imp.field
                            ));
                            let _ = u.emu_stop();
                        }
                        s.log.push(HostCall {
                            module: imp.module.clone(),
                            field: imp.field.clone(),
                            args,
                            results: r.as_ref().ok().cloned(),
                        });
                        match r {
                            Ok(vals) => {
                                let want: Vec<ValType> = vals.iter().map(|v| v.ty()).collect();
                                if want != imp.sig.results {
                                    s.failure = Some(format!(
                                        "host function {}::{} returned {vals:?}, signature says {:?}",
                                        imp.module, imp.field, imp.sig.results
                                    ));
                                    let _ = u.emu_stop();
                                }
                                for (i, w) in
                                    vals.iter().flat_map(|v| v.to_words()).enumerate().take(4)
                                {
                                    out[i] = w;
                                }
                            }
                            Err(e) => {
                                s.failure = Some(format!(
                                    "host function {}::{} trapped: {e}",
                                    imp.module, imp.field
                                ));
                                let _ = u.emu_stop();
                            }
                        }
                    }
                    Stub::Raw { name, f } => {
                        let v = f(regs);
                        sh.borrow_mut().log.push(HostCall {
                            module: "<raw symbol>".into(),
                            field: name.clone(),
                            args: regs.iter().map(|w| WasmValue::I32(*w)).collect(),
                            results: Some(vec![WasmValue::I32(v)]),
                        });
                        out[0] = v;
                    }
                }
                for (i, w) in out.iter().enumerate() {
                    let _ = u.reg_write(RegisterARM::R0 as i32 + i as i32, u64::from(*w));
                }
                let _ = u.reg_write(RegisterARM::R12 as i32, u64::from(CLOBBER | 12));
            }),
            "add stub hook",
        )?;

        // Internal calls: see the module doc. A frame opens when execution
        // reaches a function symbol with LR pointing into `.text`, and closes
        // at that return address with SP back at its entry value.
        let entries: std::collections::BTreeMap<u64, String> = obj
            .funcs
            .iter()
            .map(|(name, f)| (TEXT_BASE + f.offset, name.clone()))
            .collect();
        let text_end = TEXT_BASE + obj.text.len() as u64;
        let sh = Rc::clone(&shared);
        uc(
            emu.add_code_hook(TEXT_BASE, text_end.max(TEXT_BASE + 1) - 1, move |u, addr, _| {
                let rd = |u: &Unicorn<'_, ()>, r: i32| u.reg_read(r).unwrap_or(0) & 0xFFFF_FFFF;
                let callee_saved = |u: &Unicorn<'_, ()>| {
                    let mut v = [0u64; 8];
                    for (k, slot) in v.iter_mut().enumerate() {
                        *slot = rd(u, RegisterARM::R4 as i32 + k as i32);
                    }
                    v
                };
                let sp = rd(u, RegisterARM::SP as i32);
                let mut s = sh.borrow_mut();
                if let Some(f) = s.frames.pop_if(|f| f.ret == addr && f.sp == sp) {
                    s.internal_returns += 1;
                    let now = callee_saved(u);
                    let lost: Vec<String> = (0..8)
                        .filter(|&k| now[k] != f.saved[k])
                        .map(|k| format!("R{}", k + 4))
                        .collect();
                    if !lost.is_empty() {
                        let name = entries.get(&f.callee).cloned().unwrap_or_default();
                        s.failure = Some(format!(
                            "ABI violated: internal call to `{name}` returned with {} clobbered",
                            lost.join(", ")
                        ));
                        let _ = u.emu_stop();
                        return;
                    }
                    for r in [2, 3, 12] {
                        let _ = u.reg_write(RegisterARM::R0 as i32 + r, u64::from(CLOBBER | r as u32));
                    }
                }
                if entries.contains_key(&addr) {
                    let ret = rd(u, RegisterARM::LR as i32) & !1;
                    // The export's own frame returns to RETURN_ADDR and is
                    // judged by `call`. A branch back to a function's first
                    // instruction re-enters with the same LR and SP: one frame.
                    let inside = (TEXT_BASE..text_end).contains(&ret);
                    let same = s
                        .frames
                        .last()
                        .is_some_and(|f| f.callee == addr && f.ret == ret && f.sp == sp);
                    if inside && !same {
                        let saved = callee_saved(u);
                        s.frames.push(Frame { callee: addr, ret, sp, saved });
                    }
                }
            }),
            "add internal-call hook",
        )?;

        let hit: Rc<RefCell<Option<(u64, u32)>>> = Rc::new(RefCell::new(None));
        let hit2 = Rc::clone(&hit);
        uc(
            emu.add_intr_hook(move |u, intno| {
                let pc = u.pc_read().unwrap_or(u64::MAX);
                *hit2.borrow_mut() = Some((pc, intno));
                let _ = u.emu_stop();
            }),
            "add_intr_hook",
        )?;

        let mut image = Self {
            emu,
            wasm: wasm.to_vec(),
            obj: obj.clone(),
            shared,
            hit,
            r10,
            r11,
            budget: cfg.budget,
            cpu_model_readback: readback,
        };
        // The embedder's instantiation step (docs/embedder-abi-relocatable-arm.md):
        // `__synth_start` once, after R11/R10/R9 and before any export.
        if runs_start {
            let void = Signature {
                params: vec![],
                results: vec![],
            };
            let run = image.call_symbol(START_SYMBOL, &void, &[])?;
            if run.outcome != EmuOutcome::Values(vec![]) {
                return Err(EmuError::Abi(format!(
                    "the start function ({START_SYMBOL}, function {}) did not return \
                     cleanly: {:?}",
                    start.unwrap_or(0),
                    run.outcome
                )));
            }
        }
        Ok(image)
    }

    /// How many internal calls have returned, and been checked, on this
    /// image so far (see the module doc).
    pub fn internal_returns(&self) -> usize {
        self.shared.borrow().internal_returns
    }

    /// Read `len` bytes of linear memory at wasm address `addr`.
    pub fn read_linmem(&self, addr: u32, len: usize) -> Result<Vec<u8>, EmuError> {
        let mut b = vec![0u8; len];
        uc(
            self.emu
                .mem_read(u64::from(self.r11) + u64::from(addr), &mut b),
            "read linear memory",
        )?;
        Ok(b)
    }

    /// Call `export(args)`. Registers are re-seeded for every call; mapped
    /// memory is left as the previous call left it.
    pub fn call(&mut self, export: &str, args: &[WasmValue]) -> Result<HostedRun, EmuError> {
        let sig = export_signature(&self.wasm, export).map_err(EmuError::Abi)?;
        self.call_symbol(export, &sig, args)
    }

    /// Call the object's function symbol `export` with signature `sig`: an
    /// export by its name, or [`START_SYMBOL`], which is no wasm export.
    fn call_symbol(
        &mut self,
        export: &str,
        sig: &Signature,
        args: &[WasmValue],
    ) -> Result<HostedRun, EmuError> {
        let sym = self
            .obj
            .func(export)
            .ok_or_else(|| EmuError::NoSymbol(export.to_string()))?
            .clone();
        if !sym.thumb {
            return Err(EmuError::NotThumb(export.to_string()));
        }
        if sig
            .params
            .iter()
            .chain(&sig.results)
            .any(|t| matches!(t, ValType::F32 | ValType::F64))
        {
            return Err(EmuError::FloatAbi {
                func: export.to_string(),
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
        let r = |i: i32| RegisterARM::R0 as i32 + i;
        let emu = &mut self.emu;
        for i in 0..4 {
            let v = *words.get(i).unwrap_or(&POISON);
            uc(emu.reg_write(r(i as i32), u64::from(v)), "write arg")?;
        }
        let mut seeds = Vec::new();
        for i in 4..9 {
            let v = 0xC0DE_0000u64 | i as u64;
            uc(emu.reg_write(r(i), v), "seed callee-saved")?;
            seeds.push((r(i), format!("R{i}"), v));
        }
        for (i, v) in [(9, GLOBALS_UNMAPPED), (10, self.r10), (11, self.r11)] {
            uc(emu.reg_write(r(i), u64::from(v)), "write R9-R11")?;
            seeds.push((r(i), format!("R{i} (embedder contract)"), u64::from(v)));
        }
        uc(emu.reg_write(r(12), u64::from(POISON)), "write R12")?;
        uc(emu.reg_write(RegisterARM::SP as i32, STACK_TOP), "write SP")?;
        uc(
            emu.reg_write(RegisterARM::LR as i32, RETURN_ADDR | 1),
            "write LR",
        )?;
        *self.hit.borrow_mut() = None;
        self.shared.borrow_mut().frames.clear();
        let logged = self.shared.borrow().log.len();

        let entry = TEXT_BASE + sym.offset;
        let res = emu.emu_start(entry | 1, RETURN_ADDR, 0, self.budget);
        let pc_now = uc(emu.reg_read(RegisterARM::PC as i32), "read PC")? & !1;
        let calls = self.shared.borrow().log[logged..].to_vec();
        if let Some(reason) = self.shared.borrow_mut().failure.take() {
            return Ok(HostedRun {
                outcome: EmuOutcome::Illegal { pc: pc_now, reason },
                calls,
            });
        }

        let fault = match (*self.hit.borrow(), res) {
            (Some((reported_pc, intno)), _) => Some(Fault::Hook { reported_pc, intno }),
            (None, Err(err)) => Some(Fault::Error { pc: pc_now, err }),
            (None, Ok(())) => None,
        };
        let outcome = if let Some(fault) = fault {
            let pc = fault_pc(Machine::Arm, fault);
            let mut bytes = vec![0u8; 4];
            if emu.mem_read(pc, &mut bytes).is_err() {
                bytes.truncate(2);
                if emu.mem_read(pc, &mut bytes).is_err() {
                    bytes.clear();
                }
            }
            // A trap may be raised in a callee: anywhere in `.text`.
            let text = TEXT_BASE..TEXT_BASE + self.obj.text.len() as u64;
            judge(Machine::Arm, fault, &bytes, &text)
        } else if pc_now != RETURN_ADDR {
            EmuOutcome::Budget
        } else {
            let mut viol = Vec::new();
            for (reg, name, v) in &seeds {
                if uc(emu.reg_read(*reg), "read callee-saved")? & 0xFFFF_FFFF != *v {
                    viol.push(format!("{name} clobbered"));
                }
            }
            if uc(emu.reg_read(RegisterARM::SP as i32), "read SP")? & 0xFFFF_FFFF != STACK_TOP {
                viol.push("SP imbalance".into());
            }
            if !viol.is_empty() {
                EmuOutcome::Illegal {
                    pc: pc_now,
                    reason: format!("ABI violated: {}", viol.join(", ")),
                }
            } else {
                let n: usize = sig.results.iter().map(|t| t.words()).sum();
                let mut out_words = Vec::new();
                for i in 0..n {
                    out_words.push(uc(emu.reg_read(r(i as i32)), "read result")? as u32);
                }
                EmuOutcome::Values(
                    sig.results
                        .first()
                        .map(|t| vec![WasmValue::from_words(*t, &out_words)])
                        .unwrap_or_default(),
                )
            }
        };
        Ok(HostedRun { outcome, calls })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn import_arguments_are_read_per_aapcs() {
        let sig = |p: &[ValType]| Signature {
            params: p.to_vec(),
            results: vec![],
        };
        let regs = [1, 2, 3, 4];
        // The stack word at SP+off reads as 0x100 + off.
        let st = |off: u32| 0x100 + off;
        let args = |p: &[ValType]| args_from_aapcs(&sig(p), regs, &st);
        use ValType::{I32, I64};
        assert_eq!(
            args(&[I32, I32]),
            vec![WasmValue::I32(1), WasmValue::I32(2)]
        );
        // An i64 after an i32 skips R1 and takes R2:R3.
        assert_eq!(
            args(&[I32, I64]),
            vec![WasmValue::I32(1), WasmValue::I64(0x0000_0004_0000_0003)]
        );
        assert_eq!(
            args(&[I64, I32]),
            vec![WasmValue::I64(0x0000_0002_0000_0001), WasmValue::I32(3)]
        );
        // Refs #1785: an i64 that does not fit goes to the stack, and so does
        // every later argument (no back-fill of R3); an 8-aligned NSAA.
        assert_eq!(
            args(&[I32, I32, I32, I64]),
            vec![
                WasmValue::I32(1),
                WasmValue::I32(2),
                WasmValue::I32(3),
                WasmValue::I64(0x0000_0104_0000_0100)
            ]
        );
        assert_eq!(
            args(&[I64, I32, I64, I32]),
            vec![
                WasmValue::I64(0x0000_0002_0000_0001),
                WasmValue::I32(3),
                WasmValue::I64(0x0000_0104_0000_0100),
                WasmValue::I32(0x108)
            ]
        );
        assert_eq!(
            args(&[I32, I32, I32, I32, I32, I64]),
            vec![
                WasmValue::I32(1),
                WasmValue::I32(2),
                WasmValue::I32(3),
                WasmValue::I32(4),
                WasmValue::I32(0x100),
                WasmValue::I64(0x0000_010C_0000_0108)
            ]
        );
        // Refused boundaries.
        let imp = |p: &[ValType], r: &[ValType]| FuncImport {
            module: "m".into(),
            field: "f".into(),
            sig: Signature {
                params: p.to_vec(),
                results: r.to_vec(),
            },
        };
        assert!(check_import_abi(&imp(&[ValType::I32; 4], &[ValType::I64])).is_ok());
        assert!(check_import_abi(&imp(&[ValType::I32; 5], &[])).is_ok());
        assert!(check_import_abi(&imp(&[ValType::F32], &[])).is_err());
        assert!(check_import_abi(&imp(&[], &[ValType::F64])).is_err());
        assert!(check_import_abi(&imp(&[], &[ValType::I32, ValType::I32])).is_err());
    }
}
