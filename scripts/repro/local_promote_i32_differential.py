#!/usr/bin/env python3
"""VCR-RA local-promotion validation oracle (#390, epic #242).

`local_promote_i32.wat` is built to defeat the #193 non-vacuity trap: 7
concurrent-live i32 locals (forces overflow past the 5-reg r4..r8 promotion pool
→ 2 spill to frame) and a closing fold that demands operand-stack temps while
those locals are live (reservation-under-pressure). All locals are written before
read (straight-line, so each set dominates every read) — the case promotion v1
accepts.

wasmtime is ground truth; unicorn runs synth's ARM (`--relocatable` /
select_with_stack path). The harness runs the SAME elf twice per vector:

  * clean  — r4..r8 and the frame window left as the caller found them
  * dirty  — r4..r8 and the frame window PRE-LOADED with non-zero sentinels

The dirty pass is the read-before-write-guard gate. unicorn `mem_map` zero-fills
memory, so a promoted local read before its write would read 0 by luck and hide a
wrong write-before-read analysis. Pre-dirtying r4..r8 (and the frame window) makes
such a premature read leak a non-zero sentinel into the result. Both passes must
equal wasmtime, AND clean must equal dirty (a correct callee is insensitive to
incoming callee-saved garbage — it saves/restores or overwrites every reg it uses).
(True zero-init of a NEVER-written local is a separate pre-existing miscompile —
read_before_write_local_zeroinit.wat — that promotion v1 declines by construction.)

Run (flag-off frame path, then flag-on promotion):
  synth compile scripts/repro/local_promote_i32.wat -o /tmp/lp.elf \
        --target cortex-m4 --relocatable
  /tmp/armv/bin/python scripts/repro/local_promote_i32_differential.py /tmp/lp.elf
  SYNTH_LOCAL_PROMOTE=1 synth compile ... -o /tmp/lp_on.elf ...
  /tmp/armv/bin/python scripts/repro/local_promote_i32_differential.py /tmp/lp_on.elf

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
    UC_ARM_REG_R4,
    UC_ARM_REG_R5,
    UC_ARM_REG_R6,
    UC_ARM_REG_R7,
    UC_ARM_REG_R8,
    UC_ARM_REG_SP,
)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/lp.elf"
WAT = Path(__file__).with_name("local_promote_i32.wat")

# Ground truth: wasmtime.
eng = wasmtime.Engine()
mod = wasmtime.Module(eng, WAT.read_bytes())
st = wasmtime.Store(eng)
inst = wasmtime.Instance(st, mod, [])
gt = inst.exports(st)["local_promote"]

# synth's ARM under unicorn.
e = ELFFile(open(ELF, "rb"))
text = e.get_section_by_name(".text").data()
symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] for s in symtab.iter_symbols()}

CODE, STK = 0x10000, 0x90000
SP0 = STK + 0x8000
RET = CODE + 0xFF00

# Non-zero callee-saved sentinels — a correct callee that promotes a local into
# one of these must overwrite it (compute) or zero-init it; if it leaks one into
# the result the dirty pass diverges from wasmtime.
CALLEE_SAVED = [
    (UC_ARM_REG_R4, 0xDEAD0004),
    (UC_ARM_REG_R5, 0xDEAD0005),
    (UC_ARM_REG_R6, 0xDEAD0006),
    (UC_ARM_REG_R7, 0xDEAD0007),
    (UC_ARM_REG_R8, 0xDEAD0008),
]


def run(a, b, dirty):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_write(CODE, text)
    mu.mem_map(STK, 0x10000)
    mu.mem_write(RET, b"\x00\xbf\x00\xbf")
    if dirty:
        # Dirty the frame window the prologue will carve out below SP, so a
        # read-before-write frame slot can't read a coincidental 0.
        mu.mem_write(SP0 - 0x400, b"\xa5" * 0x400)
        for reg, val in CALLEE_SAVED:
            mu.reg_write(reg, val)
    mu.reg_write(UC_ARM_REG_R0, a)
    mu.reg_write(UC_ARM_REG_R1, b)
    mu.reg_write(UC_ARM_REG_SP, SP0)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.emu_start((CODE + syms["local_promote"]) | 1, RET, timeout=5_000_000)
    return mu.reg_read(UC_ARM_REG_R0)


ok = True
for a, b in (
    (0, 0),
    (1, 2),
    (3000, 50),
    (0x7FFFFFFF, 1),
    (0xFFFFFFFF, 0x80000000),
    (12345, 0xDEADBEEF),
    (0xCAFEBABE, 0x0BADF00D),
):
    sa = a - (1 << 32) if a >= 1 << 31 else a
    sb = b - (1 << 32) if b >= 1 << 31 else b
    exp = gt(st, sa, sb) & 0xFFFFFFFF
    clean = run(a, b, dirty=False)
    dirty = run(a, b, dirty=True)
    good = clean == exp and dirty == exp
    if not good:
        ok = False
    m = "OK  " if good else "FAIL"
    print(
        f"{m} local_promote({a:#010x},{b:#010x}) "
        f"clean={clean:#010x} dirty={dirty:#010x} expect={exp:#010x}"
    )

print("ORACLE:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
