#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 27
"""#882 — RV32 br_table compare-chain execution oracle.

RV32 lowers `br_table` as a compare-and-branch chain (`beq idx, x0` for entry
0, `li`+`beq` per further entry, `jal` to the default) — no jump table. This
oracle compiles scripts/repro/rv32_br_table_882.wat (gale's exact wdg_unlock
shape `targets: [0,1,0], default: 1`, plus a 3-distinct-target dispatch and a
default-distinct-from-every-entry dispatch), runs every export under unicorn
(UC_ARCH_RISCV / UC_MODE_RISCV32) and compares with wasmtime ground truth.

Index vectors cover EVERY table entry AND out-of-range — including the
unsigned-interpretation edge (0x80000000, 0xFFFFFFFF must land on default,
never wrap into the table): a wrong default target or a signed chain compare
is loud here.

Symbols come from the ELF .symtab (SHT_SYMTAB), not `synth disasm` text.

Run:
  synth compile scripts/repro/rv32_br_table_882.wat -b riscv \
        --target riscv32imac --relocatable --all-exports -o /tmp/brtable.o
  python scripts/repro/rv32_br_table_882_differential.py /tmp/brtable.o
"""

import os
import subprocess
import sys
import tempfile

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_S11,
    UC_RISCV_REG_SP,
)

WAT = "scripts/repro/rv32_br_table_882.wat"

CODE, LIN, RET = 0x100000, 0x40000, 0x200000

FUNCS = ["dispatch", "dispatch3", "dispatch_default"]

# Every table entry + first-out-of-range + far-out-of-range + the unsigned
# edge (INT32_MIN and -1 are huge unsigned indices → default, always).
INDICES = [0, 1, 2, 3, 4, 100, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]


def to_i32(v):
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
    synth = os.environ.get("SYNTH", "./target/debug/synth")
    if len(sys.argv) > 1:
        elf = sys.argv[1]
    else:
        elf = os.path.join(tempfile.mkdtemp(prefix="brtable882"), "brtable.o")
        subprocess.run(
            [
                synth,
                "compile",
                WAT,
                "-b",
                "riscv",
                "--target",
                "riscv32imac",
                "--relocatable",
                "--all-exports",
                "-o",
                elf,
            ],
            check=True,
        )

    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, WAT)

    def wt(name, idx):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)[name](store, to_i32(idx)) & 0xFFFFFFFF

    syms, code = symbols(elf)

    # RED-GUARD (vacuity): every export must be PRESENT — a build that skips
    # a function (the pre-fix decline) must fail loudly here, not pass
    # because nothing was compared.
    missing = [f for f in FUNCS if f not in syms]
    if missing:
        print(f"exports missing from ELF (function skipped?): {missing}")
        print("RV32 br_table #882 ORACLE: FAIL (vacuous — missing exports)")
        sys.exit(1)

    def run(name, idx):
        mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
        for base, size in [(CODE, 0x20000), (LIN, 0x20000), (RET, 0x1000)]:
            mu.mem_map(base, size)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_RISCV_REG_SP, 0x110000)
        mu.reg_write(UC_RISCV_REG_S11, LIN)
        mu.reg_write(UC_RISCV_REG_A0, idx & 0xFFFFFFFF)
        mu.reg_write(UC_RISCV_REG_RA, RET)
        try:
            mu.emu_start(CODE + syms[name], RET, count=4000)
        except UcError as e:
            return None, str(e)
        return mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF, ""

    fails = 0
    for name in FUNCS:
        for idx in INDICES:
            gt = wt(name, idx)
            res, err = run(name, idx)
            ok = res == gt
            fails += 0 if ok else 1
            if not ok:
                shown = f"0x{res:08x}" if res is not None else f"ERR({err})"
                print(f"{name}(0x{idx:x}) = {shown}  wasmtime=0x{gt:08x}  FAIL")
    print(f"{len(FUNCS) * len(INDICES)} vectors, {fails} failures")

    print(
        "RV32 br_table #882 ORACLE: PASS"
        if not fails
        else f"RV32 br_table #882 ORACLE: FAIL ({fails})"
    )
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
