#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 38
"""#970 — RV32: a CONDITIONALLY-written parameter must keep its incoming argument.

`count_params` (the RISC-V backend's `effective_num_params`) counted only local
indices READ BEFORE WRITTEN in LINEAR op order. A parameter written on ONE arm
of an `if` is "written first" in that order, so it was demoted to a NON-PARAM
local — and because its first access is a write, the #457 read-before-write
zero-init skipped it too. The fall-through path then read an **uninitialised
frame slot**:

    addi sp, sp, -16
    mv   t0, a0
    beqz t0, +12       ; -> the `lw`, skipping BOTH stores below
    li   t0, 5
    sw   t0, 0(sp)
    lw   t0, 0(sp)     ; <- on the taken path this slot was NEVER written
    mv   a0, t0

That is worse than a deterministic wrong value: the slot holds whatever the
PREVIOUS frame left there, so the function LEAKS caller/callee stack bytes —
an information-disclosure shape on top of the miscompile.

This oracle makes that visible instead of accidentally benign. Every stack word
BELOW the entry stack pointer is pre-filled with 0xDEADBEEF before each run, so
an uninitialised-slot read returns POISON rather than unicorn's zero fill —
without it the leak would read as aarch64's deterministic `0` and the finding
would be lost. Argument registers the signature does not use carry a SECOND,
distinct poison (0xFEEDFACE), so "read an uninitialised slot" and "read the
wrong argument register" cannot be mistaken for one another. Measured RED on
cb80e60c (before the fix):

    BUG cond_write_param(0, 0x2a): want=0x2a got=0xdeadbeef   <- POISON
    ok  cond_write_param(1, 0x2a): want=0x5  got=0x5

Ground truth is wasmtime on the same `.wat`. Symbols come from the ELF
`.symtab` (SHT_SYMTAB), never `synth disasm` text — the disassembler decodes RV
bytes with whatever target it defaults to, so its text is host-dependent.

The two `R_RISCV_CALL` (type 19) relocations to the in-module callees are
resolved IN-PROCESS by patching the `auipc`/`jalr` pair, exactly as a linker
would; no external toolchain is needed.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/cond_write_param_970_riscv_differential.py
"""
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_A2,
    UC_RISCV_REG_A3,
    UC_RISCV_REG_A4,
    UC_RISCV_REG_A5,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = Path(__file__).with_name("cond_write_param_970.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, LIN, RET = 0x100000, 0x40000, 0x200000
STACK_BASE, STACK_SIZE = 0x80000, 0x10000
SP0 = STACK_BASE + 0xC000  # entry SP: 48 KiB of poison below it, 16 KiB above

# The word written into every stack slot BELOW the entry SP. An uninitialised
# frame-slot read returns THIS, which is what makes the leak legible; without
# it unicorn's zero fill would make the RV32 bug look like aarch64's
# deterministic `0` and the finding would be lost.
MEM_POISON = 0xDEADBEEF   # every stack word below the entry SP
REG_POISON = 0xFEEDFACE   # every argument register the signature does not use

A_REGS = [
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_A2,
    UC_RISCV_REG_A3,
    UC_RISCV_REG_A4,
    UC_RISCV_REG_A5,
]

R_RISCV_CALL = 19
M32 = 0xFFFFFFFF

# (export, args). The `cw_*` cases each have their HIGHEST referenced local
# index written before it is read in linear op order — the shape the read-first
# heuristic undercounts. Vectors always include a fall-through (cond = 0) run,
# which is the one that reads the never-written slot, plus a taken run so a
# lowering that broke the WRITE path would be caught too.
CASES = [
    # THE canonical shape.
    ("cond_write_param", [0, 0x2A]),
    ("cond_write_param", [1, 0x2A]),
    ("cond_write_param", [0, 0x07]),
    ("cond_write_param", [0, 0x11112222]),
    ("cond_write_param", [0, 0xFFFFFFFF]),
    ("cond_write_param", [0, 0]),  # the arg IS 0: only the poison tells them apart
    # The write is a CALL result — the argument registers are caller-saved.
    ("cw_call", [0, 0x2A]),
    ("cw_call", [1, 0x2A]),
    ("cw_call", [0, 0xABCDEF01]),
    ("cw_call_arg", [0, 0x2A]),
    ("cw_call_arg", [1, 0x2A]),
    ("cw_call_arg", [0, 0x7FFFFFFF]),
    # local.tee instead of local.set.
    ("cw_tee", [0, 0x2A]),
    ("cw_tee", [1, 0x2A]),
    ("cw_tee", [0, 0x80000000]),
    # br_if out of a block rather than `if`.
    ("cw_brif", [0, 0x2A]),
    ("cw_brif", [1, 0x2A]),
    ("cw_brif", [0, 0xDEADBEEF]),  # the arg equals the poison: must still match
    # A loop whose zero-trip case leaves the param untouched.
    ("cw_loop", [0, 0x2A]),
    ("cw_loop", [3, 0x2A]),
    ("cw_loop", [0, 0xFFFFFFFF]),
    # Three params, the highest one conditionally written.
    ("cw_last_of_three", [0, 3, 4]),
    ("cw_last_of_three", [1, 3, 4]),
    ("cw_last_of_three", [0, 0x10, 0xFFFF]),
    # Six params (all register-passed on RV32; ARM stack-passes 4 and 5).
    ("cw_high_param", [0, 1, 2, 3, 4, 5]),
    ("cw_high_param", [1, 1, 2, 3, 4, 5]),
    ("cw_high_param", [0, 9, 9, 9, 0x1000, 0x2000]),
    # ── guards: the shapes the fix must NOT change ────────────────────────────
    ("guard_rbw_local", [7]),  # #457: non-param local reads the mandated 0
    ("guard_rbw_local", [0]),
    ("guard_rbw_local", [0xFFFFFFFF]),
    ("guard_rbw_local_mixed", [0, 0x2A]),
    ("guard_rbw_local_mixed", [1, 0x2A]),
    ("guard_both_arms", [0, 0x2A]),
    ("guard_both_arms", [1, 0x2A]),
    ("guard_write_then_read", [3, 0x2A]),
    ("guard_write_then_read", [0, 0]),
    ("guard_plain_params", [11, 31]),
    ("guard_plain_params", [0xFFFFFFFF, 1]),
]


def die(msg):
    print(f"FATAL: {msg}")
    sys.exit(1)


def compile_fixture(out):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-b", "riscv", "--target", "riscv32imac",
         "--relocatable", "--all-exports", "-o", out],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        die(f"synth compile failed (rc={r.returncode}):\n{r.stdout}\n{r.stderr}")
    return out


def load(path):
    """Return (symbols, .text with R_RISCV_CALL relocations applied)."""
    e = ELFFile(open(path, "rb"))
    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: s["st_value"] for s in symtab.iter_symbols()
            if s.name and s["st_info"]["type"] == "STT_FUNC"}
    text = bytearray(e.get_section_by_name(".text").data())

    nrel = 0
    for sec in e.iter_sections():
        if sec["sh_type"] not in ("SHT_REL", "SHT_RELA"):
            continue
        for r in sec.iter_relocations():
            if r["r_info_type"] != R_RISCV_CALL:
                die(f"unexpected reloc type {r['r_info_type']}; "
                    f"this harness only resolves R_RISCV_CALL (19)")
            name = symtab.get_symbol(r["r_info_sym"]).name
            if name not in syms:
                die(f"reloc names {name!r}, which is not a defined function symbol")
            off = r["r_offset"]
            disp = (CODE + syms[name]) - (CODE + off) + (r.entry.get("r_addend") or 0)
            hi = ((disp + 0x800) >> 12) & 0xFFFFF
            lo = disp & 0xFFF
            (auipc,) = struct.unpack_from("<I", text, off)
            (jalr,) = struct.unpack_from("<I", text, off + 4)
            if auipc & 0x7F != 0x17 or jalr & 0x7F != 0x67:
                die(f"reloc site {off:#x} is not an auipc/jalr pair "
                    f"({auipc:#010x}/{jalr:#010x})")
            struct.pack_into("<I", text, off, (auipc & 0xFFF) | (hi << 12))
            struct.pack_into("<I", text, off + 4, (jalr & 0x000FFFFF) | (lo << 20))
            nrel += 1
    return syms, bytes(text), nrel


def run(syms, text, name, args):
    """Execute one export under unicorn with the sub-SP stack POISONED."""
    addr = syms.get(name)
    if addr is None:
        return None, f"symbol {name} missing from .symtab"
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, text)
    # POISON everything the callee's frame can occupy. Without this an
    # uninitialised-slot read returns unicorn's zero fill and the RV32 defect
    # would read as a benign `0` rather than as a leak of previous-frame bytes.
    mu.mem_write(STACK_BASE, struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    mu.reg_write(UC_RISCV_REG_SP, SP0)
    mu.reg_write(UC_RISCV_REG_S11, LIN)  # linear-memory base
    for i, a in enumerate(args):
        mu.reg_write(A_REGS[i], a & M32)
    # Argument registers the signature does NOT use also carry poison, so a
    # lowering that read the wrong a-register is caught as well.
    for i in range(len(args), len(A_REGS)):
        mu.reg_write(A_REGS[i], REG_POISON)
    mu.reg_write(UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(CODE + addr, RET, count=20000)
    except UcError as ex:
        return None, str(ex)
    return mu.reg_read(UC_RISCV_REG_A0) & M32, ""


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))

    with tempfile.TemporaryDirectory() as td:
        obj = compile_fixture(os.path.join(td, "cw970_rv.o"))
        syms, text, nrel = load(obj)
    print(f"resolved {nrel} R_RISCV_CALL relocation(s) in-process")

    fails = 0
    leaks = 0
    for name, args in CASES:
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        want = inst.exports(store)[name](store, *[a - (1 << 32) if a >> 31 else a
                                                  for a in args]) & M32
        got, err = run(syms, text, name, args)
        ok = got == want
        fails += 0 if ok else 1
        tag = ""
        if got == MEM_POISON and not ok:
            leaks += 1
            tag = "   <- POISON (uninitialised stack slot)"
        shown = f"0x{got:08x}" if got is not None else f"ERR({err})"
        argstr = ", ".join(f"0x{a:x}" for a in args)
        print(f"{'ok ' if ok else 'BUG'} {name}({argstr}): "
              f"want=0x{want:08x} got={shown}{tag}")

    print(f"\n#970 RV32 CHECKS={len(CASES) - fails}/{len(CASES)}"
          f"  poison-leaks={leaks}")
    if fails:
        print("#970 RV32 conditional-param-write ORACLE: FAIL")
    else:
        print("#970 RV32 conditional-param-write ORACLE: PASS")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
