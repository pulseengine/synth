#!/usr/bin/env python3
"""#212 — inlined-callee-after-opaque-call differential oracle.

gale's loom-inlined `flight_algo` calls the opaque `filter_step` (which writes
the flight_state via `i32.div_s /1000`), then runs the inlined `controller_step`
body that reads those just-written fields back. wasmtime is ground truth; unicorn
runs synth's ARM (the `--relocatable` / select_with_stack path) for the same
memory image, including the internal `bl filter_step` (hooked, since the
relocatable ELF leaves it unresolved).

Bug (pre-fix): the const-0 negation base of `0 - (mdeg>>6 + rate>>7)` was
allocated to R12/IP, which the very next indexed load's `ADD ip, addr, #off`
(encoder scratch) clobbered — turning `0 - sum` into `(addr+off) - sum`. Only the
divided fields (st[0], st[4]) used that pattern under enough pressure to reach
R12, so aileron/elevator saturated to 127 while rudder/updates read correctly.
Fix: reserve R12 as scratch (remove it from ALLOCATABLE_REGS).

Run:
  synth compile scripts/repro/flight_seam.wasm -o /tmp/fs.elf \
        --target cortex-m4 --all-exports --relocatable
  /tmp/armv/bin/python scripts/repro/flight_seam_differential.py /tmp/fs.elf

Exits nonzero on mismatch so it can gate a release.
"""
import re
import struct
import subprocess
import sys

import wasmtime
from capstone import CS_ARCH_ARM, CS_MODE_THUMB, Cs
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WASM = "scripts/repro/flight_seam.wasm"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/fs.elf"
SYNTH = "./target/debug/synth"

ST_OFF, S_OFF = 0x1000, 0x2000


def st_init():
    b = bytearray(64)
    struct.pack_into("<i", b, 0, 1000)   # pitch accumulator
    struct.pack_into("<i", b, 4, -500)   # roll accumulator
    struct.pack_into("<i", b, 8, 200)    # yaw accumulator (no division)
    struct.pack_into("<i", b, 24, 7)     # updates
    return bytes(b)


def s_init():
    b = bytearray(32)
    for i, v in enumerate([100, -50, 30, 300, -200]):  # gyro x/y/z, accel x/y
        struct.pack_into("<h", b, i * 2, v)
    return bytes(b)


def main():
    # wasmtime ground truth
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    mem = inst.exports(store)["memory"]
    mem.write(store, st_init(), ST_OFF)
    mem.write(store, s_init(), S_OFF)
    gt = inst.exports(store)["flight_algo"](store, ST_OFF, S_OFF) & 0xFFFFFFFF

    # synth ARM under unicorn (full flight_algo incl. internal bl filter_step)
    dis = subprocess.run([SYNTH, "disasm", ELF], capture_output=True, text=True).stdout
    syms = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r'^([0-9a-f]{8}) <(\w+)>:', dis, re.M)}
    text = ELFFile(open(ELF, "rb")).get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    fa, fs = syms["func_0"], syms["func_1"]
    md = Cs(CS_ARCH_ARM, CS_MODE_THUMB)
    bl_addr = next(i.address for i in md.disasm(bytes(code[fa:syms["func_1"]]), fa)
                   if i.mnemonic == "bl")

    CODE, LIN, STK = 0x10000, 0x40000, 0x90000
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN, 0x10000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_write(CODE, code)
    mu.mem_write(LIN + ST_OFF, st_init())
    mu.mem_write(LIN + S_OFF, s_init())
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, LIN)   # linear-memory base
    mu.reg_write(UC_ARM_REG_R0, ST_OFF)
    mu.reg_write(UC_ARM_REG_R1, S_OFF)
    RET = 0x9F00 | 1
    mu.reg_write(UC_ARM_REG_LR, RET)

    def hook(mu, a, sz, u):
        if a == CODE + (bl_addr - base):   # redirect the unresolved BL -> filter_step
            mu.reg_write(UC_ARM_REG_LR, (a + 4) | 1)
            mu.reg_write(UC_ARM_REG_PC, (CODE + (fs - base)) | 1)
    mu.hook_add(UC_HOOK_CODE, hook)
    try:
        mu.emu_start((CODE + fa - base) | 1, RET & ~1, count=2000)
        got = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
    except UcError as e:
        got = f"ERR:{e}"

    print(f"wasmtime (ground truth): 0x{gt:08X}")
    g = f"0x{got:08X}" if isinstance(got, int) else got
    print(f"synth ARM             : {g}")
    ok = isinstance(got, int) and got == gt
    print("MATCH" if ok else "MISMATCH  <-- #212")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
