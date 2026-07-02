#!/usr/bin/env python3
"""VCR-RA-001 (#242) — allocation-time spill-on-exhaustion differential oracle.

`spill_on_exhaust_242.wat` keeps 10 param-derived i32 values simultaneously
live, exhausting the optimized path's R4-R8 scratch pool. Flag-off the
function DECLINES to the direct selector (#496); with
`SYNTH_SPILL_ON_EXHAUST=1` it stays on the optimized path by spilling the
farthest-next-use value (Belady) to a frame slot at allocation time. wasmtime
is ground truth; unicorn runs synth's ARM. The fold mixes non-commutative ops
(sub/xor) so any operand-order or reload bug changes the result.

Run:
  SYNTH_SPILL_ON_EXHAUST=1 synth compile scripts/repro/spill_on_exhaust_242.wat \
        -o /tmp/soe.elf --target cortex-m4
  python scripts/repro/spill_on_exhaust_242_differential.py /tmp/soe.elf

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

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/soe.elf"
WAT = Path(__file__).with_name("spill_on_exhaust_242.wat")

# Ground truth: wasmtime.
eng = wasmtime.Engine()
mod = wasmtime.Module(eng, WAT.read_bytes())
st = wasmtime.Store(eng)
inst = wasmtime.Instance(st, mod, [])
gt = inst.exports(st)["hp"]

# synth's ARM under unicorn. Resolve the entry from the symtab (host-portable,
# see the #489 lesson), relative to the .text load address.
e = ELFFile(open(ELF, "rb"))
text_sec = e.get_section_by_name(".text")
text = text_sec.data()
symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] for s in symtab.iter_symbols()}
entry_off = (syms["hp"] & ~1) - text_sec["sh_addr"]

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
    (7, 3),
    (0x12345678, 0x9ABCDEF0),
):
    exp = gt(
        st,
        a - (1 << 32) if a >= 1 << 31 else a,
        b - (1 << 32) if b >= 1 << 31 else b,
    ) & 0xFFFFFFFF
    mu.reg_write(UC_ARM_REG_R0, a)
    mu.reg_write(UC_ARM_REG_R1, b)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x8000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.emu_start((CODE + entry_off) | 1, RET, timeout=5_000_000)
    got = mu.reg_read(UC_ARM_REG_R0)
    m = "OK  " if got == exp else "FAIL"
    if got != exp:
        ok = False
    print(f"{m} hp({a:#x},{b:#x}) = {got:#010x} expect {exp:#010x}")

print("ORACLE:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
