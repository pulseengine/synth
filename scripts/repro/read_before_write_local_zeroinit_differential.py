#!/usr/bin/env python3
"""#457 read-before-write local zero-init oracle (ARM direct + optimized, RV32).

`read_before_write_local_zeroinit.wat` declares ONE i32 param and ONE never-
written i32 local, and returns `p0 + local1`. WASM zero-initializes non-param
locals, so `rbw(p0)` must return `p0 + 0 = p0`. The pre-#457 backends inferred
the param count from access patterns (`count_params`: first-access-is-a-read ⇒
param), so the read-before-write local was homed in the SECOND parameter
register and the function returned `p0 + <caller garbage>`.

wasmtime is ground truth; unicorn runs synth's output. The harness dispatches
on the ELF machine (EM_ARM Thumb vs EM_RISCV RV32) so the same script gates all
three lowering paths:

  synth compile scripts/repro/read_before_write_local_zeroinit.wat \
        -o /tmp/rbw_reloc.elf --target cortex-m4 --relocatable   # ARM direct
  synth compile scripts/repro/read_before_write_local_zeroinit.wat \
        -o /tmp/rbw_opt.elf --target cortex-m4                   # ARM optimized*
  synth compile scripts/repro/read_before_write_local_zeroinit.wat \
        -o /tmp/rbw_rv.elf -b riscv                              # RV32
  /tmp/venv/bin/python scripts/repro/read_before_write_local_zeroinit_differential.py <elf>

(*with the #457 fix the optimized path detect-and-declines the shape to the
direct selector — the gate holds whichever selector emitted the bytes.)

Every vector runs twice: CLEAN (registers/stack as unicorn zero-fills them) and
DIRTY (r1..r3 / a1..a3 loaded with non-zero sentinels and the frame window below
SP pre-filled with 0xA5). The dirty pass is the load-bearing one: unicorn's
zero-filled memory and registers would let a garbage read return a coincidental
0 and hide the bug; the sentinels make a mis-homed local or an un-zeroed frame
slot leak visibly into the result. Symbols come from the ELF symtab, never from
disassembly text (host-independent — the PR #489 lesson).

Exits nonzero on any mismatch so it can gate a release.
"""

import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import (
    UC_ARCH_ARM,
    UC_ARCH_RISCV,
    UC_MODE_RISCV32,
    UC_MODE_THUMB,
    Uc,
)
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_SP,
)
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_A2,
    UC_RISCV_REG_A3,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_SP,
)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/rbw_reloc.elf"
WAT = Path(__file__).with_name("read_before_write_local_zeroinit.wat")

# Ground truth: wasmtime. rbw(p0) must be p0 (the local reads 0); rbw0() — the
# 0-declared-params edge — must be 0.
eng = wasmtime.Engine()
mod = wasmtime.Module(eng, WAT.read_bytes())
st = wasmtime.Store(eng)
inst = wasmtime.Instance(st, mod, [])
gt = inst.exports(st)["rbw"]
gt0 = inst.exports(st)["rbw0"]

e = ELFFile(open(ELF, "rb"))
text_sec = e.get_section_by_name(".text")
text, text_addr = text_sec.data(), text_sec["sh_addr"]
symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] for s in symtab.iter_symbols()}
is_riscv = e["e_machine"] == "EM_RISCV"

CODE, STK = 0x10000, 0x90000
SP0 = STK + 0x8000
RET = CODE + 0xFF00  # a mapped nop pad — unicorn stops when PC reaches it

# Non-zero sentinels for the registers a second/third/fourth param WOULD occupy
# — exactly what the pre-#457 misclassification read for the rbw local.
SENTINEL = 0xDEADBEEF


def run_arm(sym, args, dirty):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_write(CODE + text_addr, text)
    mu.mem_map(STK, 0x10000)
    mu.mem_write(RET, b"\x00\xbf\x00\xbf")  # nop; nop
    arg_regs = (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)
    if dirty:
        mu.mem_write(SP0 - 0x400, b"\xa5" * 0x400)
        for reg in arg_regs[len(args) :]:
            mu.reg_write(reg, SENTINEL)
    for reg, val in zip(arg_regs, args):
        mu.reg_write(reg, val)
    mu.reg_write(UC_ARM_REG_SP, SP0)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    # Thumb symbols carry bit 0 in the symtab already on ET_REL; mask + re-set
    # so both ET_REL (rbw=0x1) and ET_EXEC (rbw=0xa1) resolve identically.
    entry = CODE + text_addr + (syms[sym] & ~1)
    mu.emu_start(entry | 1, RET, timeout=5_000_000)
    return mu.reg_read(UC_ARM_REG_R0)


def run_rv32(sym, args, dirty):
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x10000)
    mu.mem_write(CODE + text_addr, text)
    mu.mem_map(STK, 0x10000)
    arg_regs = (UC_RISCV_REG_A0, UC_RISCV_REG_A1, UC_RISCV_REG_A2, UC_RISCV_REG_A3)
    if dirty:
        mu.mem_write(SP0 - 0x400, b"\xa5" * 0x400)
        for reg in arg_regs[len(args) :]:
            mu.reg_write(reg, SENTINEL)
    for reg, val in zip(arg_regs, args):
        mu.reg_write(reg, val)
    mu.reg_write(UC_RISCV_REG_SP, SP0)
    # RA must land on a MAPPED pad (the #220 unicorn gotcha).
    mu.reg_write(UC_RISCV_REG_RA, RET)
    mu.emu_start(CODE + text_addr + syms[sym], RET, timeout=5_000_000)
    return mu.reg_read(UC_RISCV_REG_A0)


run = run_rv32 if is_riscv else run_arm

ok = True
for p0 in (0, 1, 12345, 0x7FFFFFFF, 0xDEADBEEF, 0xFFFFFFFF):
    sp0 = p0 - (1 << 32) if p0 >= 1 << 31 else p0
    exp = gt(st, sp0) & 0xFFFFFFFF
    clean = run("rbw", (p0,), dirty=False) & 0xFFFFFFFF
    dirty = run("rbw", (p0,), dirty=True) & 0xFFFFFFFF
    good = clean == exp and dirty == exp
    if not good:
        ok = False
    m = "OK  " if good else "FAIL"
    print(
        f"{m} rbw({p0:#010x}) clean={clean:#010x} dirty={dirty:#010x} "
        f"expect={exp:#010x}"
    )

# The 0-declared-params edge: every argument register is garbage; result must
# still be the zero-inited local (0).
exp0 = gt0(st) & 0xFFFFFFFF
clean0 = run("rbw0", (), dirty=False) & 0xFFFFFFFF
dirty0 = run("rbw0", (), dirty=True) & 0xFFFFFFFF
good0 = clean0 == exp0 and dirty0 == exp0
if not good0:
    ok = False
print(
    f"{'OK  ' if good0 else 'FAIL'} rbw0() clean={clean0:#010x} "
    f"dirty={dirty0:#010x} expect={exp0:#010x}"
)

print("ORACLE:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
