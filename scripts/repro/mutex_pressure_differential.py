#!/usr/bin/env python3
"""#326 — arg-move-cycle-under-pressure differential oracle.

`mutex_pressure.wat` reproduces the shape that stopped gale's dissolved
`z_impl_k_mutex_unlock` from compiling on v0.11.36+: three i64 values pin the
callee-saved pairs (r3,r4)/(r5,r6)/(r7,r8) across two calls, and the second
call's argument marshalling is a genuine r0/r1 SWAP — the old emit_arg_moves
demanded a free callee-saved cycle scratch and `Err`ed ("register exhaustion:
no free callee-saved register to hold a call result while reloading a
preserved param"). The #326 fix routes the marshal through the parallel-move
resolver, breaking the cycle via one stack slot (str/mov/ldr) instead.

This harness proves the fixed output is numerically correct, not just
compilable: wasmtime is ground truth; unicorn runs synth's ARM (`--relocatable`
path) with internal `BL func_N` relocations resolved in-image (same approach
as u64_unpack_differential.py). `main` returns i64 — checked as the full
r1:r0 pair, so a swapped/clobbered marshal (swap2(a,b) = 2a-b is
argument-order-sensitive) or a corrupted live i64 shows up immediately.

Run:
  synth compile scripts/repro/mutex_pressure.wat -o /tmp/mp.elf \
        --target cortex-m4 --all-exports --relocatable
  /tmp/armv/bin/python scripts/repro/mutex_pressure_differential.py /tmp/mp.elf

Exits nonzero on any mismatch.
"""

import struct
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/mp.elf"
WAT = sys.argv[2] if len(sys.argv) > 2 else "scripts/repro/mutex_pressure.wat"

# ── ground truth ──
eng = wasmtime.Engine()
mod = wasmtime.Module(eng, open(WAT, "rb").read())
st = wasmtime.Store(eng)
inst = wasmtime.Instance(st, mod, [])
gt_main = inst.exports(st)["main"]

# ── synth ELF: text + internal BL reloc resolution (R_ARM_THM_CALL = 10) ──
e = ELFFile(open(ELF, "rb"))
text = bytearray(e.get_section_by_name(".text").data())
symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] for s in symtab.iter_symbols()}
rel = e.get_section_by_name(".rel.text")
if rel:
    for r in rel.iter_relocations():
        if r["r_info_type"] == 10:
            s = symtab.get_symbol(r["r_info_sym"])
            if s.name in syms:
                off, target = r["r_offset"], syms[s.name]
                dd = target - (off + 4)
                S_ = (dd >> 24) & 1
                i1 = (dd >> 23) & 1
                i2 = (dd >> 22) & 1
                j1 = (~(i1 ^ S_)) & 1
                j2 = (~(i2 ^ S_)) & 1
                imm10 = (dd >> 12) & 0x3FF
                imm11 = (dd >> 1) & 0x7FF
                hw1 = 0xF000 | (S_ << 10) | imm10
                hw2 = 0xD000 | (j1 << 13) | (j2 << 11) | imm11
                struct.pack_into("<HH", text, off, hw1, hw2)

CODE, STK = 0x10000, 0x90000
mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
mu.mem_map(CODE, 0x10000)
mu.mem_write(CODE, bytes(text))
mu.mem_map(STK, 0x10000)
RET = CODE + 0xFF00
mu.mem_write(RET, b"\x00\xbf\x00\xbf")

ok = True
for x in (0, 1, 5, 19, 1000, 0x7FFFFFFF, 0xDEADBEEF):
    exp = gt_main(st, x & 0xFFFFFFFF) & 0xFFFFFFFFFFFFFFFF
    mu.reg_write(UC_ARM_REG_R0, x & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R11, 0)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x8000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.emu_start((CODE + syms["main"]) | 1, RET, timeout=5_000_000)
    got = mu.reg_read(UC_ARM_REG_R0) | (mu.reg_read(UC_ARM_REG_R1) << 32)
    m = "OK " if got == exp else "FAIL"
    if got != exp:
        ok = False
    print(f"{m} main({x:#x}) = {got:#018x} expect {exp:#018x}")
print("ORACLE:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
