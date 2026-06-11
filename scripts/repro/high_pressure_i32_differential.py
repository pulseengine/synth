#!/usr/bin/env python3
"""VCR-RA-001 step 3b-lite (#242) — spill-on-exhaustion differential oracle.

`high_pressure_i32.wat` keeps 10 i32 constants simultaneously live (plus both
params reserved in r0/r1), exhausting the R0-R8 pool. Pre-3b the selector
hard-failed ("register exhaustion: all allocatable registers are live on the
stack"); with the spill-on-exhaustion retry the deepest stack values spill to
the frame and reload on pop. wasmtime is ground truth; unicorn runs synth's ARM
(`--relocatable` / select_with_stack path). The fold mixes non-commutative ops
(sub/xor) so an operand-order or reload bug changes the result.

Run:
  synth compile scripts/repro/high_pressure_i32.wat -o /tmp/hp.elf \
        --target cortex-m4 --relocatable
  /tmp/armv/bin/python scripts/repro/high_pressure_i32_differential.py /tmp/hp.elf

Exits nonzero on any mismatch so it can gate a release.
"""
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_SP,
)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/hp.elf"
WAT = Path(__file__).with_name("high_pressure_i32.wat")

# Ground truth: wasmtime.
eng = wasmtime.Engine()
mod = wasmtime.Module(eng, WAT.read_bytes())
st = wasmtime.Store(eng)
inst = wasmtime.Instance(st, mod, [])
gt = inst.exports(st)["high_pressure"]

# synth's ARM under unicorn.
e = ELFFile(open(ELF, "rb"))
text = e.get_section_by_name(".text").data()
symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] for s in symtab.iter_symbols()}

CODE, STK = 0x10000, 0x90000
mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
mu.mem_map(CODE, 0x10000)
mu.mem_write(CODE, text)
mu.mem_map(STK, 0x10000)
RET = CODE + 0xFF00
mu.mem_write(RET, b"\x00\xbf\x00\xbf")

ok = True
for a, b in (
    (0, 0),
    (1, 2),
    (3000, 50),
    (0x7FFFFFFF, 1),
    (0xFFFFFFFF, 0x80000000),
    (12345, 0xDEADBEEF),
):
    exp = gt(st, a - (1 << 32) if a >= 1 << 31 else a,
             b - (1 << 32) if b >= 1 << 31 else b) & 0xFFFFFFFF
    mu.reg_write(UC_ARM_REG_R0, a)
    mu.reg_write(UC_ARM_REG_R1, b)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x8000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.emu_start((CODE + syms["high_pressure"]) | 1, RET, timeout=5_000_000)
    got = mu.reg_read(UC_ARM_REG_R0)
    m = "OK  " if got == exp else "FAIL"
    if got != exp:
        ok = False
    print(f"{m} high_pressure({a:#x},{b:#x}) = {got:#010x} expect {exp:#010x}")

print("ORACLE:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
