#!/usr/bin/env python3
"""#472 — RV32 cmp→select fusion (VCR-SEL-004 port) differential oracle.

Ports the ARM cmp→select lever to RV32: an i32 comparison that DIRECTLY feeds
a `select` fuses into the select's branch under `SYNTH_RV_CMP_SELECT` — the
boolean materialization (`slt`/`sltu`/`xor`+`sltiu`/`xori`) is deleted and the
branch tests the comparison itself (`blt a, b` instead of
`slt t, a, b; bne t, zero`), saving 1–2 instructions per select.

This oracle compiles the module for RV32, runs each export under unicorn
(UC_ARCH_RISCV / UC_MODE_RISCV32, ILP32) and compares with wasmtime. Run it
against BOTH the flag-off and the flag-on object — both must match wasmtime.

Coverage: every fusible i32 comparison kind (eq/ne/lt_s/gt_s/le_s/ge_s/
lt_u/gt_u/le_u/ge_u/eqz) feeding a select, an i32 comparison selecting i64
operands (both halves under one fused branch), an i64 comparison feeding a
select (out of fusion scope — must stay correct on the baseline path), and
back-to-back fused selects (record-invalidation stress). Vectors include
equal operands and sign-boundary values (0x80000000 / 0xFFFFFFF0) so a
signed/unsigned branch-condition mix-up is loud.

Symbols come from the ELF .symtab (SHT_SYMTAB), not `synth disasm` text.

Run:
  synth compile scripts/repro/rv32_cmp_select_472.wat -b riscv \
        --target riscv32imac --relocatable --all-exports -o /tmp/cmpsel.o
  /tmp/synthvenv/bin/python \
        scripts/repro/rv32_cmp_select_472_riscv_differential.py /tmp/cmpsel.o
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

WAT = "scripts/repro/rv32_cmp_select_472.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/cmpsel.o"

CODE, LIN, RET = 0x100000, 0x40000, 0x200000

FUNCS = [
    "sel_eq",
    "sel_ne",
    "sel_lt_s",
    "sel_gt_s",
    "sel_le_s",
    "sel_ge_s",
    "sel_lt_u",
    "sel_gt_u",
    "sel_le_u",
    "sel_ge_u",
    "sel_eqz",
    "sel_i64",
    "sel_cmp_i64",
    "clamp",
]

# (a, b) pairs: lt / gt / eq, zero (for eqz), and sign-boundary values where
# signed and unsigned comparisons disagree (0x80000000 = INT_MIN unsigned-huge;
# 0xFFFFFFF0 = -16 signed, huge unsigned).
PAIRS = [
    (5, 9),
    (9, 5),
    (7, 7),
    (0, 3),
    (3, 0),
    (0, 0),
    (0x80000000, 3),
    (3, 0x80000000),
    (0xFFFFFFF0, 3),
    (3, 0xFFFFFFF0),
    (0xFFFFFFF0, 0x80000000),
    (150, 4),  # clamp: above ceiling / below floor
    (4, 150),
]

ARG_REGS = [UC_RISCV_REG_A0, UC_RISCV_REG_A1]


def to_i32(v):
    """wasmtime wants i32 params in signed range."""
    v &= 0xFFFFFFFF
    return v - 0x100000000 if v >= 0x80000000 else v


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

    def wt(name, args):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)[name](store, *(to_i32(a) for a in args)) & 0xFFFFFFFF

    syms, code = symbols(ELF)

    def run(name, args):
        addr = syms.get(name)
        if addr is None:
            return None, f"symbol {name} missing (function skipped?)"
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        for base, size in [(CODE, 0x20000), (LIN, 0x20000), (RET, 0x1000)]:
            mu.mem_map(base, size)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_RISCV_REG_SP, 0x110000)
        mu.reg_write(UC_RISCV_REG_S11, LIN)
        for i, v in enumerate(args):
            mu.reg_write(ARG_REGS[i], v & 0xFFFFFFFF)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(CODE + addr, RET, count=4000)
        except UcError as e:
            return None, str(e)
        return mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF, ""

    fails = 0
    for name in FUNCS:
        for a, b in PAIRS:
            gt = wt(name, (a, b))
            res, err = run(name, (a, b))
            ok = res == gt
            fails += 0 if ok else 1
            if not ok:
                shown = f"0x{res:08x}" if res is not None else f"ERR({err})"
                print(f"{name}(0x{a:x},0x{b:x}) = {shown}  wasmtime=0x{gt:08x}  FAIL")
    print(f"{len(FUNCS) * len(PAIRS)} vectors, {fails} failures")

    print(
        "RISC-V cmp->select #472 ORACLE: PASS"
        if not fails
        else f"RISC-V cmp->select #472 ORACLE: FAIL ({fails})"
    )
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
