#!/usr/bin/env python3
"""#350 — out-of-range `ADD #imm` lowering (MOVW/MOVT + ADD instead of erroring).

A static store with `offset=70000` (> 0xFFF) forces the indexed-address path
`ADD ip, base, #70000`. Before the fix, `encode_thumb32_add_imm` returned
`Err("ADD immediate too large for single instruction")`, so the whole function
failed to compile (empty object) — exactly the breakage that blocked gale's
`gale_k_stack_push_decide`. The encoder now lowers it to
`MOVW ip,#0x1170; MOVT ip,#0x0001; ADD.W ip, base, ip` (ip = base + 70000).

This harness proves the lowered sequence computes the address **correctly**:
wasmtime is ground truth; unicorn runs synth's ARM (`--relocatable` path) with a
linear-memory region large enough to hold offset 70000. The function stores its
param at mem[70000] and reads it back, so a 16-bit-truncated address (the failure
mode if MOVT were dropped) would land at a different page and diverge.

Run:
  synth compile scripts/repro/add_imm_large.wat -o /tmp/ail.elf \
        --target cortex-m4f --all-exports --relocatable
  /tmp/armv/bin/python scripts/repro/add_imm_large_differential.py /tmp/ail.elf

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
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = "scripts/repro/add_imm_large.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/ail.elf"
SYNTH = "./target/debug/synth"

CODE, LIN, STK, RET = 0x200000, 0x40000, 0x180000, 0x300000
# Linear memory must cover offset 70000 (0x11170) -> map 0x20000 (128 KiB).
LIN_SIZE = 0x20000

VECTORS = [0, 1, 0xABCD, 99, 0x7FFFFFFF, 0xFFFFFFFF, 0x12345678, 70000]


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, wasmtime.wat2wasm(open(WAT).read()))

    def wt(arg):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)["store_load_large"](store, arg) & 0xFFFFFFFF

    dis = subprocess.run([SYNTH, "disasm", ELF], capture_output=True, text=True).stdout
    syms = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r'^([0-9a-f]{8}) <(\w+)>:', dis, re.M)}
    fa = syms.get("func_0") or syms.get("store_load_large")
    text = ELFFile(open(ELF, "rb")).get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]

    def arm(arg):
        mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        mu.mem_map(CODE, 0x10000)
        mu.mem_map(LIN, LIN_SIZE)
        mu.mem_map(STK - 0x8000, 0x10000)
        mu.mem_map(RET, 0x1000)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_ARM_REG_SP, STK)
        mu.reg_write(UC_ARM_REG_R11, LIN)
        mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            mu.emu_start((CODE + fa - base) | 1, RET, count=10000)
        except UcError as e:
            return f"ERR:{e}"
        return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF

    fails = 0
    for v in VECTORS:
        gt = wt(v)
        got = arm(v)
        ok = isinstance(got, int) and got == gt
        fails += 0 if ok else 1
        shown = f"0x{got:08X}" if isinstance(got, int) else got
        print(f"store_load_large(0x{v:08X}) = {shown}  (wasmtime 0x{gt:08X})"
              f"{'' if ok else '  <-- MISMATCH'}")
    print(f"\n{len(VECTORS) - fails}/{len(VECTORS)} match")
    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
