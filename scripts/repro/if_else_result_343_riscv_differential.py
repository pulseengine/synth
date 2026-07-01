#!/usr/bin/env python3
"""#343 — RV32 `if (result i32)` result-register reconciliation.

The RV32 selector lowered a value-returning `if/else` without merging the two
arms' result registers at the join. The then-arm computed its value into one
register (e.g. `t2`, from `add`) and jumped to the end label; the else-arm left
its value in another (`t0`, a bare const); the epilogue then unconditionally
read whichever register the else-arm happened to leave — so the then path
returned a stale leftover instead of its own result.

This oracle compiles the module for RV32, runs each export under unicorn
(UC_ARCH_RISCV / UC_MODE_RISCV32, ILP32) across both arms, and compares with
wasmtime. Pre-fix it FAILS the then-arm (and the pick2 else-arm); post-fix all
vectors match.

Symbols are read from the ELF .symtab (SHT_SYMTAB) rather than `synth disasm`
text — the disassembler is host-dependent (it decodes RV bytes with whatever
target it defaults to) so its text is not a reliable symbol source.

Run:
  synth compile scripts/repro/if_else_result_343.wat -b riscv \
        --target riscv32imac --relocatable --all-exports -o /tmp/if343.o
  /tmp/synthvenv/bin/python \
        scripts/repro/if_else_result_343_riscv_differential.py /tmp/if343.o
"""
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = "scripts/repro/if_else_result_343.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/if343.o"

CODE, LIN, RET = 0x100000, 0x40000, 0x200000
# (export, param) — exercise BOTH the then-arm (nonzero cond) and the
# else-arm (zero cond) of each value-returning if/else.
VECTORS = [
    ("pick", 1),
    ("pick", 7),
    ("pick", 0),
    ("pick2", 1),
    ("pick2", 42),
    ("pick2", 0),
    ("pick3", 1),
    ("pick3", 99),
    ("pick3", 0),
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

    def wt(name, arg):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)[name](store, arg) & 0xFFFFFFFF

    syms, code = symbols(ELF)

    def run(name, arg):
        addr = syms.get(name)
        if addr is None:
            return None, f"symbol {name} missing (function skipped?)"
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        for base, size in [(CODE, 0x20000), (LIN, 0x20000), (0x88000, 0x10000), (RET, 0x1000)]:
            mu.mem_map(base, size)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_RISCV_REG_SP, 0x90000)
        mu.reg_write(UC_RISCV_REG_S11, LIN)
        mu.reg_write(UC_RISCV_REG_A0, arg & 0xFFFFFFFF)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(CODE + addr, RET, count=4000)
        except UcError as e:
            return None, str(e)
        return mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF, ""

    fails = 0
    for name, arg in VECTORS:
        gt = wt(name, arg)
        res, err = run(name, arg)
        ok = res == gt
        fails += 0 if ok else 1
        shown = f"0x{res:08x}={res}" if res is not None else f"ERR({err})"
        print(f"{name}({arg}) = {shown}  wasmtime=0x{gt:08x}={gt}  {'OK' if ok else 'FAIL'}")

    print("\nRISC-V if/else-result #343 ORACLE: PASS" if not fails
          else f"\nRISC-V if/else-result #343 ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
