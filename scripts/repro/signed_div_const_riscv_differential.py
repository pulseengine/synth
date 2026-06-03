#!/usr/bin/env python3
"""#232 — RV32 signed-division-by-constant overflow-guard clobber.

v0.11.26's lowest-free allocator (#231) materialized the `INT_MIN`/`-1` overflow
guard constants into the register still holding the live dividend (popped off the
vstack), so `filter_axis_decide(1000,100,500)` returned 0 instead of 1088 on
qemu_riscv32. This checks synth's RV32 output matches wasmtime across vectors,
including the INT_MIN/-1 overflow edge.

Run:
  synth compile scripts/repro/signed_div_const.wasm -b riscv -t rv32imac \
        --all-exports --relocatable -o /tmp/sdiv.o
  /tmp/armv/bin/python scripts/repro/signed_div_const_riscv_differential.py /tmp/sdiv.o
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
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = "scripts/repro/signed_div_const.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/sdiv.o"
SYNTH = "./target/debug/synth"
CODE, LIN, RET = 0x100000, 0x40000, 0x200000
VECTORS = [(1000, 100, 500), (-2000, 5, 5), (7, 3, 0), (-2147483648, 0, 0), (123456, -789, 42)]


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, WAT)

    def wt(args):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)["filter_axis_decide"](store, *args) & 0xFFFFFFFF

    dis = subprocess.run([SYNTH, "disasm", ELF], capture_output=True, text=True).stdout
    syms = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r'^([0-9a-f]{8}) <(\w+)>:', dis, re.M)}
    fa = syms.get("func_0") or syms.get("filter_axis_decide")
    if fa is None:
        print("FAIL: filter_axis_decide symbol not found (function skipped?)")
        sys.exit(1)
    code = ELFFile(open(ELF, "rb")).get_section_by_name(".text").data()

    def run(args):
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        for base, size in [(CODE, 0x20000), (LIN, 0x20000), (0x88000, 0x10000), (RET, 0x1000)]:
            mu.mem_map(base, size)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_RISCV_REG_SP, 0x90000)
        mu.reg_write(UC_RISCV_REG_S11, LIN)
        for r, v in zip((UC_RISCV_REG_A0, UC_RISCV_REG_A1, UC_RISCV_REG_A2), args):
            mu.reg_write(r, v & 0xFFFFFFFF)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(CODE + fa, RET, count=4000)
        except UcError as e:
            return None, str(e)
        return mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF, ""

    fails = 0
    for v in VECTORS:
        gt = wt(v)
        res, err = run(v)
        ok = res == gt
        fails += 0 if ok else 1
        shown = f"0x{res:08x}={res}" if res is not None else f"ERR({err})"
        print(f"filter_axis_decide{v} = {shown}  wasmtime=0x{gt:08x}={gt}  {'OK' if ok else 'FAIL'}")
    print("\nRISC-V signed-div-const ORACLE: PASS" if not fails
          else f"RISC-V signed-div-const ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
