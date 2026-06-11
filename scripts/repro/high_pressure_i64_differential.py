#!/usr/bin/env python3
"""VCR-RA-001 acceptance increment (#242) — i64 pair-spill differential oracle.

`high_pressure_i64.wat` keeps 4 i64 constants simultaneously live (4 register
pairs) while all four i32 params are reserved in r0-r3: at the first i64.add
the popped operand pairs + pinned params leave no free consecutive pair and
nothing register-resident to spill, so pre-acceptance the selector hard-failed
("register exhaustion: no consecutive pair of free registers for i64"). With
the param-backing retry the params frame-back at entry (#204 machinery) and
the function compiles. wasmtime is ground truth; unicorn runs synth's ARM
(`--relocatable` / select_with_stack path). The fold mixes non-commutative ops
(sub/xor) so an operand-order, reload, or i64 half-swap bug changes the
result; the i64 result returns in r0 (lo) : r1 (hi).

Run:
  synth compile scripts/repro/high_pressure_i64.wat -o /tmp/hp64.elf \
        --target cortex-m4 --relocatable
  /tmp/armv/bin/python scripts/repro/high_pressure_i64_differential.py /tmp/hp64.elf

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
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_SP,
)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/hp64.elf"
WAT = Path(__file__).with_name("high_pressure_i64.wat")

# Ground truth: wasmtime.
eng = wasmtime.Engine()
mod = wasmtime.Module(eng, WAT.read_bytes())
st = wasmtime.Store(eng)
inst = wasmtime.Instance(st, mod, [])
gt = inst.exports(st)["high_pressure64"]

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


def signed32(v):
    return v - (1 << 32) if v >= 1 << 31 else v


ok = True
for a, b, c, d in (
    (0, 0, 0, 0),
    (1, 2, 3, 4),
    (3000, 50, 7, 11),
    (0x7FFFFFFF, 1, 0x7FFFFFFF, 2),
    (0xFFFFFFFF, 0x80000000, 0xFFFFFFFF, 0x80000000),
    (12345, 0xDEADBEEF, 0xCAFEBABE, 54321),
):
    exp = gt(st, signed32(a), signed32(b), signed32(c), signed32(d)) & (
        (1 << 64) - 1
    )
    mu.reg_write(UC_ARM_REG_R0, a)
    mu.reg_write(UC_ARM_REG_R1, b)
    mu.reg_write(UC_ARM_REG_R2, c)
    mu.reg_write(UC_ARM_REG_R3, d)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x8000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.emu_start((CODE + syms["high_pressure64"]) | 1, RET, timeout=5_000_000)
    got = mu.reg_read(UC_ARM_REG_R0) | (mu.reg_read(UC_ARM_REG_R1) << 32)
    m = "OK  " if got == exp else "FAIL"
    if got != exp:
        ok = False
    print(
        f"{m} high_pressure64({a:#x},{b:#x},{c:#x},{d:#x}) = "
        f"{got:#018x} expect {exp:#018x}"
    )

print("ORACLE:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
