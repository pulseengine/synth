#!/usr/bin/env python3
"""#220 — RISC-V callee-saved register preservation differential.

gale's first on-target RISC-V finding: the backend used callee-saved s-registers
(s1..s6) as scratch with no prologue/epilogue — an RV-psABI violation that
corrupts the caller's s-registers (including s11 = __linear_memory_base), hanging
qemu_riscv32 timing loops. The fix wraps the body in a prologue/epilogue that
spills+restores exactly the callee-saved registers it writes.

wasmtime is ground truth; unicorn runs synth's RV32 object and checks BOTH:
  (1) the returned value matches, and
  (2) the caller's callee-saved registers (seeded with sentinels) are restored.

Run:
  synth compile scripts/repro/filter_axis.wasm -b riscv -t rv32imac \
        --relocatable -o /tmp/fa.o
  /tmp/armv/bin/python scripts/repro/filter_axis_riscv_differential.py /tmp/fa.o
"""
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_A2,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S1,
    UC_RISCV_REG_S2,
    UC_RISCV_REG_S3,
    UC_RISCV_REG_S4,
    UC_RISCV_REG_S5,
    UC_RISCV_REG_S6,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WASM = "scripts/repro/filter_axis.wasm"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/fa.o"
CODE, STK, RET = 0x10000, 0x90000, 0x20000

# Caller's callee-saved registers, seeded with sentinels — must be restored.
SENTINELS = {
    UC_RISCV_REG_S1: 0x11111111,
    UC_RISCV_REG_S2: 0x22222222,
    UC_RISCV_REG_S3: 0x33333333,
    UC_RISCV_REG_S4: 0x44444444,
    UC_RISCV_REG_S5: 0x55555555,
    UC_RISCV_REG_S6: 0x66666666,
    UC_RISCV_REG_S11: 0xBBBBBBBB,  # __linear_memory_base — must never be clobbered
}

VECTORS = [(1000, 500, 300), (0, 0, 0), (-2000, 1000, -50), (3000, 50, 40), (100, -200, 77)]


def as_i32(v):
    return v - 0x100000000 if v >= 0x80000000 else v


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())
    store = wasmtime.Store(engine)
    fa = wasmtime.Instance(store, module, []).exports(store)["filter_axis_decide"]
    code = ELFFile(open(ELF, "rb")).get_section_by_name(".text").data()

    def run(a, b, c):
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        mu.mem_map(CODE, 0x10000)
        mu.mem_map(STK - 0x8000, 0x10000)
        mu.mem_map(RET, 0x1000)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_RISCV_REG_SP, STK)
        mu.reg_write(UC_RISCV_REG_A0, a & 0xFFFFFFFF)
        mu.reg_write(UC_RISCV_REG_A1, b & 0xFFFFFFFF)
        mu.reg_write(UC_RISCV_REG_A2, c & 0xFFFFFFFF)
        for r, v in SENTINELS.items():
            mu.reg_write(r, v)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(CODE, RET, count=300)
        except UcError as e:
            return None, False, str(e)
        res = mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF
        preserved = all((mu.reg_read(r) & 0xFFFFFFFF) == v for r, v in SENTINELS.items())
        return res, preserved, ""

    fails = 0
    for v in VECTORS:
        gt = fa(store, *[as_i32(x) for x in v]) & 0xFFFFFFFF
        res, preserved, err = run(*v)
        ok = res == gt and preserved
        fails += 0 if ok else 1
        shown = f"0x{res:08x}" if res is not None else f"ERR({err})"
        print(f"filter_axis{v} = {shown}  wasmtime=0x{gt:08x}  s-regs-preserved={preserved}"
              f"  {'OK' if ok else 'FAIL'}")
    print("\nRISC-V ORACLE: PASS (correct + ABI-compliant)" if not fails
          else f"RISC-V ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
