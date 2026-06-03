#!/usr/bin/env python3
"""#226 — controller_step on RISC-V: the regalloc live-range clobber.

In v0.11.23 the RV32 temp allocator was round-robin and blind to the operand
stack: an `updates<<24` value kept live across three `select`-clamps got its
register re-handed-out as comparison scratch, losing the updates byte
(`controller_step_decide` returned the wrong result on qemu_riscv32).

This runs synth's RV32 output under unicorn and checks it computes the SAME
result as wasmtime across several vectors (no memory reads — pure arithmetic),
and that the caller's callee-saved registers survive (#220 still holds).

Run:
  synth compile scripts/repro/controller_step.wat -b riscv -t rv32imac \
        --all-exports --relocatable -o /tmp/ctrl_rv.o
  /tmp/armv/bin/python scripts/repro/controller_step_riscv_differential.py /tmp/ctrl_rv.o
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
    UC_RISCV_REG_A4,
    UC_RISCV_REG_A5,
    UC_RISCV_REG_A6,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S1,
    UC_RISCV_REG_S2,
    UC_RISCV_REG_S7,
    UC_RISCV_REG_S8,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = "scripts/repro/controller_step.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/ctrl_rv.o"
SYNTH = "./target/debug/synth"
CODE, LIN, STK, RET = 0x100000, 0x40000, 0x90000, 0x200000
ARG_REGS = (
    UC_RISCV_REG_A0, UC_RISCV_REG_A1, UC_RISCV_REG_A2, UC_RISCV_REG_A3,
    UC_RISCV_REG_A4, UC_RISCV_REG_A5, UC_RISCV_REG_A6,
)
SENTINELS = {
    UC_RISCV_REG_S1: 0x1111_1111,
    UC_RISCV_REG_S2: 0x2222_2222,
    UC_RISCV_REG_S7: 0x7777_7777,
    UC_RISCV_REG_S8: 0x8888_8888,
}
# gale's exact repro first, then a spread.
VECTORS = [
    (6400, 0, -12800, 0, 3200, 0, 5),
    (0, 0, 0, 0, 0, 0, 0),
    (100, 0, 50, 0, 200, 0, 1),
    (-5000, 0, 9000, 0, -300, 0, 255),
    (127, 0, 128, 0, 256, 0, 42),
]


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, WAT)

    def wt(args):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)["controller_step_decide"](store, *args) & 0xFFFFFFFF

    dis = subprocess.run([SYNTH, "disasm", ELF], capture_output=True, text=True).stdout
    syms = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r'^([0-9a-f]{8}) <(\w+)>:', dis, re.M)}
    fa = syms.get("func_0") or syms.get("controller_step_decide")
    if fa is None:
        print("FAIL: controller_step_decide symbol not found (function skipped?)")
        sys.exit(1)
    code = ELFFile(open(ELF, "rb")).get_section_by_name(".text").data()

    def run(args):
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        mu.mem_map(CODE, 0x20000)
        mu.mem_map(LIN, 0x20000)
        mu.mem_map(STK - 0x8000, 0x10000)
        mu.mem_map(RET, 0x1000)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_RISCV_REG_SP, STK)
        mu.reg_write(UC_RISCV_REG_S11, LIN)
        for r, v in zip(ARG_REGS, args):
            mu.reg_write(r, v & 0xFFFFFFFF)
        for r, v in SENTINELS.items():
            mu.reg_write(r, v)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(CODE + fa, RET, count=4000)
        except UcError as e:
            return None, False, str(e)
        res = mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF
        preserved = all((mu.reg_read(r) & 0xFFFFFFFF) == v for r, v in SENTINELS.items())
        return res, preserved, ""

    fails = 0
    for v in VECTORS:
        gt = wt(v)
        res, preserved, err = run(v)
        ok = res == gt and preserved
        fails += 0 if ok else 1
        shown = f"0x{res:08x}" if res is not None else f"ERR({err})"
        print(f"controller_step{v} = {shown}  wasmtime=0x{gt:08x}  "
              f"s-regs-preserved={preserved}  {'OK' if ok else 'FAIL'}")
    print("\nRISC-V controller_step ORACLE: PASS (correct + ABI-compliant)" if not fails
          else f"RISC-V controller_step ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
