#!/usr/bin/env python3
"""#209 Opt 1 — constant-divisor strength-reduction differential oracle.

wasmtime runs div_const.wat as ground truth; unicorn runs synth's ARM (the
`--relocatable` / select_with_stack path, which is where the optimization lives)
for the same inputs. Every export divides/remainders its i32 param by a
compile-time constant, so this validates that guard elision + LSR/MOV strength
reduction is numerically identical to a trapping UDIV/SDIV across the edge cases
(INT_MIN, 0x80000000, 0xFFFFFFFF, pow2 boundaries, signed negatives).

Run:
  synth compile scripts/repro/div_const.wat -o /tmp/dc.elf --target cortex-m4 --relocatable
  /tmp/armv/bin/python scripts/repro/div_const_differential.py /tmp/dc.elf

Exits nonzero on any mismatch so it can gate a release.
"""
import re
import subprocess
import sys

import wasmtime
from capstone import CS_ARCH_ARM, CS_MODE_THUMB, Cs  # noqa: F401 (handy when debugging)
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = "scripts/repro/div_const.wat"
ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/dc.elf"
SYNTH = "./target/debug/synth"

# (wasm export, ELF symbol) — the relocatable build renames most exports func_N.
PAIRS = [
    ("divu_pow2", "func_0"),
    ("divu_500", "func_1"),
    ("divu_one", "func_2"),
    ("divu_2e31", "func_3"),
    ("remu_500", "remu_500"),
    ("remu_one", "remu_one"),
    ("divs_5", "func_6"),
    ("divs_neg7", "func_7"),
    ("rems_5", "rems_5"),
    ("divs_one", "func_9"),
]

INPUTS = [
    0, 1, 2, 7, 8, 9, 15, 16, 17, 100, 499, 500, 501, 999, 1000, 1001,
    0x7FFFFFFF, 0x80000000, 0x80000001, 0xFFFFFFFF, 0xFFFFFFFE,
    0x12345678, 0xABCDEF01, 3500, 28, 0x40000000,
]

CODE, RET = 0x10000, 0x90000


def as_i32(v):
    return v - 0x100000000 if v >= 0x80000000 else v


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WAT).read())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    wt = {w: inst.exports(store)[w] for w, _ in PAIRS}

    dis = subprocess.run([SYNTH, "disasm", ELF], capture_output=True, text=True).stdout
    addr = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r'^([0-9a-f]{8}) <(\w+)>:', dis, re.M)}
    text = ELFFile(open(ELF, "rb")).get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]

    def run(a, x):
        mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        mu.mem_map(CODE, 0x20000)
        mu.mem_map(0x80000, 0x20000)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_ARM_REG_SP, 0x9F000)
        mu.reg_write(UC_ARM_REG_R11, 0x88000)
        mu.reg_write(UC_ARM_REG_R0, x & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            mu.emu_start((CODE + a - base) | 1, RET, count=200)
        except UcError as e:
            return ("ERR", str(e))
        return ("OK", mu.reg_read(UC_ARM_REG_R0))

    fails = total = 0
    for w, sym in PAIRS:
        a = addr[sym]
        for x in INPUTS:
            total += 1
            gt = wt[w](store, as_i32(x)) & 0xFFFFFFFF
            st, got = run(a, x)
            if st != "OK" or got != gt:
                fails += 1
                shown = hex(got) if st == "OK" else got
                print(f"MISMATCH {w}(0x{x:08X}): wasmtime=0x{gt:08X} synth={st}:{shown}")
    print(f"\n{total - fails}/{total} match  [--relocatable / select_with_stack path]")
    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails} mismatches)")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
