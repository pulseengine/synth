#!/usr/bin/env python3
"""#209 — control_step_decide reciprocal-multiply register-pressure regression.

gale's `control_step_decide` (loom-lowered, 4× unsigned constant `div_u`:
`/500 /5 /80 /1000`) stopped compiling on v0.11.19: the UMULL reciprocal-multiply
needs more live scratch than `udiv`, and four of them on the R0–R8 pool (after
the #212 R12 reserve) exhausted the allocator, which hard-failed instead of
spilling. The v0.11.20 fix cost-gates the reciprocal-multiply (falls back to a
guard-elided `udiv` when scratch can't be allocated) and shrinks the common
`a == false` path to two temps (reusing `dst` as UMULL's throwaway low word).

This harness confirms the function both **compiles** and is **numerically
correct**: wasmtime is ground truth; unicorn runs synth's ARM (the `--relocatable`
path) with the `.rodata` table loaded into linear memory. gale's reference vector
`control_step_decide(3000,50,40,0)` must give `0x00210A55`.

Run:
  synth compile scripts/repro/control_step.wasm -o /tmp/cs.elf \
        --target cortex-m4 --all-exports --relocatable
  /tmp/armv/bin/python scripts/repro/control_step_differential.py /tmp/cs.elf

Exits nonzero on any mismatch.
"""
import re
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WASM = "scripts/repro/control_step.wasm"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/cs.elf"
SYNTH = "./target/debug/synth"

# The `.rodata` data segment lives at linear-memory offset 0x10000 (2 pages).
RODATA_BASE, RODATA_END = 0x10000, 0x20000
CODE, LIN, STK, RET = 0x200000, 0x40000, 0x90000, 0x300000

VECTORS = [
    (3000, 50, 40, 0),   # gale's reference -> 0x00210A55
    (0, 0, 0, 0), (1500, 0, 0, 0), (3000, 50, 40, 1), (2000, 100, 200, 5),
    (500, 5, 80, 1000), (65535, 127, 127, 3), (1, 1, 1, 1), (2645, 10, 20, 0),
    (4000, 200, 30, 7), (123, 45, 67, 89), (3000, 50, 40, 255), (0xFFFFFFFF, 0, 0, 0),
]


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())

    def wt(args):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        r = inst.exports(store)["control_step_decide"](store, *args) & 0xFFFFFFFF
        # wasmtime Memory.read(store, start, stop) — stop is an offset, not a size.
        rodata = bytes(inst.exports(store)["memory"].read(store, RODATA_BASE, RODATA_END))
        return r, rodata

    dis = subprocess.run([SYNTH, "disasm", ELF], capture_output=True, text=True).stdout
    syms = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r'^([0-9a-f]{8}) <(\w+)>:', dis, re.M)}
    fa = syms["func_0"] if "func_0" in syms else syms["control_step_decide"]
    text = ELFFile(open(ELF, "rb")).get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]

    def arm(args, rodata):
        mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        mu.mem_map(CODE, 0x10000)
        mu.mem_map(LIN, 0x20000)
        mu.mem_map(STK - 0x8000, 0x10000)
        mu.mem_map(RET, 0x1000)
        mu.mem_write(CODE, code)
        mu.mem_write(LIN + RODATA_BASE, rodata)
        mu.reg_write(UC_ARM_REG_SP, STK)
        mu.reg_write(UC_ARM_REG_R11, LIN)
        for i, v in enumerate((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)):
            mu.reg_write(v, args[i] & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            mu.emu_start((CODE + fa - base) | 1, RET, count=10000)
        except UcError as e:
            return f"ERR:{e}"
        return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF

    fails = 0
    for v in VECTORS:
        gt, rodata = wt(v)
        got = arm(v, rodata)
        ok = isinstance(got, int) and got == gt
        fails += 0 if ok else 1
        shown = f"0x{got:08X}" if isinstance(got, int) else got
        print(f"control_step_decide{v} = {shown}  (wasmtime 0x{gt:08X})"
              f"{'' if ok else '  <-- MISMATCH'}")
    print(f"\n{len(VECTORS) - fails}/{len(VECTORS)} match")
    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
