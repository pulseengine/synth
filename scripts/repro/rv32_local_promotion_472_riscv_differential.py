#!/usr/bin/env python3
"""#472 — RV32 i32 local-promotion lever (VCR-RA) differential oracle.

Ports the ARM local-promotion lever (#390/#457/#458) to RV32: non-parameter i32
locals in leaf functions are promoted into callee-saved s-registers (s8/s9/s10)
under `SYNTH_RV_LOCAL_PROMO`, so their reads become free register aliases and
their frame `lw`/`sw` traffic disappears.

This oracle compiles the module for RV32, runs each export under unicorn
(UC_ARCH_RISCV / UC_MODE_RISCV32, ILP32) and compares with wasmtime. Run it
against BOTH the flag-off and the flag-on object — both must match wasmtime.

It is also the *discriminator* for the two correctness hazards the direct-alias
`local.get` opens, so it fails loudly if either regresses:
  - $war_set / $war_tee — the get→…→set/tee→use WAR hazard. An earlier read of a
    promoted local must survive a later write to the SAME local (`snapshot_aliases`).
  - $rbw — a local read before its first write must observe the wasm zero-init
    (`addi s_i, zero, 0` at entry).

Symbols come from the ELF .symtab (SHT_SYMTAB), not `synth disasm` text — the
disassembler is host-dependent and unreliable as a symbol source.

Run:
  synth compile scripts/repro/rv32_local_promotion_472.wat -b riscv \
        --target riscv32imac --relocatable --all-exports -o /tmp/promo.o
  /tmp/synthvenv/bin/python \
        scripts/repro/rv32_local_promotion_472_riscv_differential.py /tmp/promo.o
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

WAT = "scripts/repro/rv32_local_promotion_472.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/promo.o"

CODE, LIN, RET = 0x100000, 0x40000, 0x200000

# (export, (args...)) — single-arg funcs pass a0; accum passes a0,a1.
VECTORS = [
    ("accum", (5, 3)),
    ("accum", (7, 2)),
    ("accum", (100, 40)),
    ("war_set", (5,)),
    ("war_set", (10,)),
    ("war_set", (0,)),
    ("war_tee", (5,)),
    ("war_tee", (42,)),
    ("war_tee", (0,)),
    ("rbw", (5,)),
    ("rbw", (7,)),
    ("rbw", (0,)),
]

ARG_REGS = [UC_RISCV_REG_A0, UC_RISCV_REG_A1]


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
        return inst.exports(store)[name](store, *args) & 0xFFFFFFFF

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
    for name, args in VECTORS:
        gt = wt(name, args)
        res, err = run(name, args)
        ok = res == gt
        fails += 0 if ok else 1
        shown = f"0x{res:08x}={res}" if res is not None else f"ERR({err})"
        av = ",".join(str(a) for a in args)
        print(f"{name}({av}) = {shown}  wasmtime=0x{gt:08x}={gt}  {'OK' if ok else 'FAIL'}")

    print(
        "\nRISC-V local-promotion #472 ORACLE: PASS"
        if not fails
        else f"\nRISC-V local-promotion #472 ORACLE: FAIL ({fails})"
    )
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
