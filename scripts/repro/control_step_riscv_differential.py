#!/usr/bin/env python3
"""#223 — control_step on RISC-V: correctness + ABI differential.

After #218 (reachable) + #220 (callee-saved ABI) + #223 (Select, non-param
locals, sign-extend), gale's `control_step_decide` compiles to RV32. This checks
it computes the SAME result as wasmtime (and the ARM backend — gale's reference
`(3000,50,40,0) = 0x00210a55`), reads its `.rodata` table via s11 (the linmem
base), and preserves the caller's callee-saved registers.

Run:
  synth compile scripts/repro/control_step.wasm -b riscv -t rv32imac \
        --all-exports --relocatable -o /tmp/cs_rv.o
  /tmp/armv/bin/python scripts/repro/control_step_riscv_differential.py /tmp/cs_rv.o
"""
import re
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_A2,
    UC_RISCV_REG_A3,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S1,
    UC_RISCV_REG_S2,
    UC_RISCV_REG_S7,
    UC_RISCV_REG_S8,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WASM = "scripts/repro/control_step.wasm"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/cs_rv.o"
SYNTH = "./target/debug/synth"
CODE, LIN, STK, RET = 0x100000, 0x40000, 0x90000, 0x200000
SENTINELS = {
    UC_RISCV_REG_S1: 0x1111_1111,
    UC_RISCV_REG_S2: 0x2222_2222,
    UC_RISCV_REG_S7: 0x7777_7777,  # non-param locals land in s7/s8 region
    UC_RISCV_REG_S8: 0x8888_8888,
}
VECTORS = [(3000, 50, 40, 0), (0, 0, 0, 0), (1500, 0, 0, 0), (2645, 10, 20, 0), (4000, 200, 30, 7)]


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())

    def wt(args):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        r = inst.exports(store)["control_step_decide"](store, *args) & 0xFFFFFFFF
        rod = bytes(inst.exports(store)["memory"].read(store, 0x10000, 0x20000))
        return r, rod

    dis = subprocess.run([SYNTH, "disasm", ELF], capture_output=True, text=True).stdout
    syms = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r'^([0-9a-f]{8}) <(\w+)>:', dis, re.M)}
    fa = syms["func_0"] if "func_0" in syms else syms["control_step_decide"]
    code = ELFFile(open(ELF, "rb")).get_section_by_name(".text").data()

    def run(args, rodata):
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        mu.mem_map(CODE, 0x20000)
        mu.mem_map(LIN, 0x20000)
        mu.mem_map(STK - 0x8000, 0x10000)
        mu.mem_map(RET, 0x1000)
        mu.mem_write(CODE, code)
        mu.mem_write(LIN + 0x10000, rodata)
        mu.reg_write(UC_RISCV_REG_SP, STK)
        mu.reg_write(UC_RISCV_REG_S11, LIN)  # s11 = __linear_memory_base
        for r, v in zip((UC_RISCV_REG_A0, UC_RISCV_REG_A1, UC_RISCV_REG_A2, UC_RISCV_REG_A3), args):
            mu.reg_write(r, v & 0xFFFFFFFF)
        for r, v in SENTINELS.items():
            mu.reg_write(r, v)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(CODE + fa, RET, count=2000)
        except UcError as e:
            return None, False, str(e)
        res = mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF
        preserved = all((mu.reg_read(r) & 0xFFFFFFFF) == v for r, v in SENTINELS.items())
        return res, preserved, ""

    fails = 0
    for v in VECTORS:
        gt, rodata = wt(v)
        res, preserved, err = run(v, rodata)
        ok = res == gt and preserved
        fails += 0 if ok else 1
        shown = f"0x{res:08x}" if res is not None else f"ERR({err})"
        print(f"control_step{v} = {shown}  wasmtime=0x{gt:08x}  s-regs-preserved={preserved}"
              f"  {'OK' if ok else 'FAIL'}")
    print("\nRISC-V control_step ORACLE: PASS (correct + ABI-compliant)" if not fails
          else f"RISC-V control_step ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
