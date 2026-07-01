#!/usr/bin/env python3
"""#317 — RV32 i64.div_s / i64.rem_s sign clobbered by the udiv core.

The signed 64-bit div/rem lowering allocated its `nsign`/`dsign` sign masks
with the lowest-free allocator, which handed out `t4`/`t5` — the inline unsigned
long-division core's fixed `DIV_D_LO`/`DIV_D_HI` registers. The core's input
parallel-move (which copies the divisor into `t4`/`t5`) overwrote the sign masks
before `result_sign = nsign ^ dsign` was computed, so the result came back with
the WRONG SIGN, e.g. `div_s(-100, 3)` → `0x1f` where wasmtime says
`0xffffffffffffffde` (-34).

This oracle compiles the module for RV32, runs each `(export, n, d)` vector
under unicorn (UC_ARCH_RISCV / UC_MODE_RISCV32, ILP32) and compares the full
64-bit `a0:a1` result with wasmtime. Pre-fix the sign-differing vectors FAIL;
post-fix all vectors match.

Symbols are read from the ELF .symtab (SHT_SYMTAB) rather than `synth disasm`
text — the disassembler is host-dependent (it decodes RV bytes with whatever
target it defaults to) so its text is not a reliable symbol source.

Run:
  synth compile scripts/repro/i64_divs_317.wat -b riscv \
        --target riscv32imac --relocatable --all-exports -o /tmp/i64divs317.o
  /tmp/synthvenv/bin/python \
        scripts/repro/i64_divs_317_riscv_differential.py /tmp/i64divs317.o
"""
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = "scripts/repro/i64_divs_317.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/i64divs317.o"

CODE, LIN, RET = 0x100000, 0x40000, 0x200000
MASK64 = 0xFFFFFFFFFFFFFFFF

# (export, n, d) — signed dividend/divisor as i32s, sign-extended to i64 in the
# module. Covers all four sign quadrants (the clobber corrupts the XOR of the
# two signs) for BOTH div_s and rem_s, plus a few asymmetric magnitudes.
VECTORS = [
    ("divs", -100, 3),     # neg / pos  → -34  (the issue's canonical case)
    ("divs", 100, -3),     # pos / neg  → -33
    ("divs", -100, -3),    # neg / neg  → +33
    ("divs", 100, 3),      # pos / pos  → +33
    ("divs", -2000000000, 7),
    ("divs", 2000000000, -123),
    ("rems", -100, 3),     # rem sign follows the dividend → -1
    ("rems", 100, -3),     # → +1
    ("rems", -100, -7),    # → -2
    ("rems", 12345, 1000),
]


def symbols(path):
    f = ELFFile(open(path, "rb"))
    st = f.get_section_by_name(".symtab")
    syms = {}
    for s in st.iter_symbols():
        if s.name and s["st_info"]["type"] == "STT_FUNC":
            syms[s.name] = s["st_value"]
    code = f.get_section_by_name(".text").data()
    return syms, code


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, WAT)

    def wt(name, n, d):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)[name](store, n, d) & MASK64

    syms, code = symbols(ELF)

    def run(name, n, d):
        addr = syms.get(name)
        if addr is None:
            return None, f"symbol {name} missing (function skipped?)"
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        for base, size in [(CODE, 0x20000), (LIN, 0x20000), (0x88000, 0x10000), (RET, 0x1000)]:
            mu.mem_map(base, size)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_RISCV_REG_SP, 0x90000)
        mu.reg_write(UC_RISCV_REG_S11, LIN)
        mu.reg_write(UC_RISCV_REG_A0, n & 0xFFFFFFFF)
        mu.reg_write(UC_RISCV_REG_A1, d & 0xFFFFFFFF)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(CODE + addr, RET, count=20000)
        except UcError as e:
            return None, str(e)
        lo = mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF
        hi = mu.reg_read(UC_RISCV_REG_A1) & 0xFFFFFFFF
        return lo | (hi << 32), ""

    fails = 0
    for name, n, d in VECTORS:
        gt = wt(name, n, d)
        res, err = run(name, n, d)
        ok = res == gt
        fails += 0 if ok else 1
        shown = f"0x{res:016x}" if res is not None else f"ERR({err})"
        print(f"{name}({n}, {d}) = {shown}  wasmtime=0x{gt:016x}  {'OK' if ok else 'FAIL'}")

    print("\nRISC-V i64 div_s/rem_s sign #317 ORACLE: PASS" if not fails
          else f"\nRISC-V i64 div_s/rem_s sign #317 ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
