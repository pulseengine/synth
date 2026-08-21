#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 34
"""#990 — RV32: a plain local written on only ONE arm of a `br_if` must read 0.

The classifier is SHARED: `synth_synthesis::read_before_write_locals` drives
the #457 frame-slot zero-init on BOTH the ARM `select_with_stack` path and the
RV32 selector, and it walks the op stream in LINEAR order — so a write on a
conditionally-skipped path suppresses the zero-init on RV32 exactly as on ARM,
and the skipping path reads an uninitialised frame slot (previous-frame bytes:
information disclosure). The RV32 local-promotion path is NOT a rescue: it
requires every access at control-flow depth 0, so this shape always lands on
the frame path. Same fixture, same case matrix as the ARM leg
(`brif_local_zeroinit_990_arm_differential.py`) — independent evidence per
backend, per the #970 two-leg precedent.

Every stack word below the entry SP is poisoned with 0xDEADBEEF and unused
argument registers with 0xFEEDFACE, so the leak is provable rather than
inferred. The i64 case reads BOTH return words (a0/a1).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/brif_local_zeroinit_990_riscv_differential.py
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
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = Path(__file__).with_name("brif_local_zeroinit_990.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, LIN, RET = 0x100000, 0x40000, 0x200000
STACK_BASE, STACK_SIZE = 0x80000, 0x10000
SP0 = STACK_BASE + 0xC000  # entry SP: 48 KiB of poison below it, 16 KiB above

MEM_POISON = 0xDEADBEEF   # every stack word below the entry SP
REG_POISON = 0xFEEDFACE   # every argument register the signature does not use

A_REGS = [UC_RISCV_REG_A0, UC_RISCV_REG_A1, UC_RISCV_REG_A2, UC_RISCV_REG_A3]

R_RISCV_CALL = 19
M32 = 0xFFFFFFFF
M64 = 0xFFFFFFFFFFFFFFFF

# Exports returning i64 (read a0 = low, a1 = high per the RV32 psABI).
RET_I64 = {"bl_brif_i64"}

# Same matrix as the ARM leg — see brif_local_zeroinit_990_arm_differential.py
# for the per-case rationale.
CASES = [
    ("bl_brif", [0]),
    ("bl_brif", [1]),
    ("bl_brif", [5]),
    ("bl_brif", [0xFFFFFFFF]),
    ("bl_brif", [0xFFFFFFFB]),
    ("bl_brif", [0x80000000]),
    ("bl_if_no_else", [0]),
    ("bl_if_no_else", [1]),
    ("bl_if_no_else", [0xFFFFFFFF]),
    ("bl_if_else_one_arm", [0]),
    ("bl_if_else_one_arm", [1]),
    ("bl_if_else_one_arm", [2]),
    ("bl_br_table", [0]),
    ("bl_br_table", [1]),
    ("bl_br_table", [2]),
    ("bl_br_table", [0xFFFFFFFF]),
    ("bl_brif_i64", [0]),
    ("bl_brif_i64", [1]),
    ("bl_brif_i64", [0xFFFFFFFF]),
    ("bl_brif_i64", [0xFFFFFFFB]),
    ("guard_straightline", [0]),
    ("guard_straightline", [4]),
    ("guard_straightline", [0xFFFFFFFF]),
    ("guard_rbw", [7]),
    ("guard_rbw", [0]),
    ("guard_both_arms", [0]),
    ("guard_both_arms", [1]),
    ("guard_same_block", [0]),
    ("guard_same_block", [9]),
    ("guard_cond_param_970", [0, 0x2A]),
    ("guard_cond_param_970", [1, 0x2A]),
    ("guard_cond_param_970", [0, 0xDEADBEEF]),
    ("guard_loop_acc", [0]),
    ("guard_loop_acc", [3]),
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
    """Return (symbols, .text with R_RISCV_CALL relocations applied, count)."""
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
    mu.mem_write(STACK_BASE, struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    mu.reg_write(UC_RISCV_REG_SP, SP0)
    mu.reg_write(UC_RISCV_REG_S11, LIN)  # linear-memory base
    for i, a in enumerate(args):
        mu.reg_write(A_REGS[i], a & M32)
    for i in range(len(args), len(A_REGS)):
        mu.reg_write(A_REGS[i], REG_POISON)
    mu.reg_write(UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(CODE + addr, RET, count=20000)
    except UcError as ex:
        return None, str(ex)
    a0 = mu.reg_read(UC_RISCV_REG_A0) & M32
    if name in RET_I64:
        a1 = mu.reg_read(UC_RISCV_REG_A1) & M32
        return (a1 << 32) | a0, ""
    return a0, ""


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))

    with tempfile.TemporaryDirectory() as td:
        obj = compile_fixture(os.path.join(td, "bl990_rv32.o"))
        syms, text, nrel = load(obj)
    print(f"resolved {nrel} R_RISCV_CALL relocation(s) in-process")

    fails = 0
    leaks = 0
    for name, args in CASES:
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        signed = [a - (1 << 32) if a >> 31 else a for a in args]
        mask = M64 if name in RET_I64 else M32
        want = inst.exports(store)[name](store, *signed) & mask
        got, err = run(syms, text, name, args)
        ok = got == want
        fails += 0 if ok else 1
        tag = ""
        if not ok and got is not None and (got & M32) in (
            MEM_POISON, (MEM_POISON + 1) & M32, (MEM_POISON - 1) & M32,
        ):
            leaks += 1
            tag = "   <- POISON (uninitialised stack slot)"
        width = 16 if name in RET_I64 else 8
        shown = f"0x{got:0{width}x}" if got is not None else f"ERR({err})"
        argstr = ", ".join(f"0x{a:x}" for a in args)
        print(f"{'ok ' if ok else 'BUG'} {name}({argstr}): "
              f"want=0x{want:0{width}x} got={shown}{tag}")

    print(f"\n#990 RV32 CHECKS={len(CASES) - fails}/{len(CASES)}"
          f"  poison-leaks={leaks}")
    if fails:
        print("#990 RV32 br_if-local zero-init ORACLE: FAIL")
    else:
        print("#990 RV32 br_if-local zero-init ORACLE: PASS")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
