#!/usr/bin/env python3
"""#666 — rv32 i32.rem_s(INT_MIN,-1) must return 0, not trap (WASM §4.3.2).

The rv32 selector shared div_s's INT_MIN/-1 overflow `ebreak` guard with
rem_s; WASM defines irem_s(INT_MIN,-1) = 0 with NO trap (only idiv_s traps on
that overflow). RISC-V M-ext `rem` already returns 0 for the overflowing case
(unprivileged spec §7.2), so after dropping the guard the bare instruction is
exactly wasm-correct. Twin of the ARM #633 fix-guard pin
(`test_633_i64_rems_has_no_overflow_guard`); the RV32 unit pin is
`rv32_signed_rem_carries_only_zero_guard_666`.

Table (rems/divs from scripts/repro/rem_s_666.wat, rv32 under unicorn, each
row cross-checked against wasmtime ground truth):

  rems(INT_MIN,-1) -> 0      NO trap   <- RED on pre-fix synth (spurious ebreak)
  rems(INT_MIN, 1) -> 0
  rems(7, 3)       -> 1
  rems(-7, 3)      -> -1                (remainder takes the dividend sign)
  rems(7, 0)       -> TRAP              (zero-divisor guard KEPT)
  divs(INT_MIN,-1) -> TRAP              (div_s overflow guard KEPT)
  divs(7, 0)       -> TRAP
  divs(7, 3)       -> 2

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/rem_s_666_differential.py
Exits nonzero on any mismatch.
"""

import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_RISCV, UC_MODE_RISCV32, Uc, UcError
from unicorn.riscv_const import (
    UC_RISCV_REG_A0,
    UC_RISCV_REG_A1,
    UC_RISCV_REG_RA,
    UC_RISCV_REG_SP,
)

WAT = Path(__file__).with_name("rem_s_666.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
TRAP = "TRAP"
INT_MIN = -(2**31)
CODE, STK, RET = 0x100000, 0x90000, 0x200000

CASES = [
    ("rems", (INT_MIN, -1), 0),  # the #666 over-trap
    ("rems", (INT_MIN, 1), 0),
    ("rems", (7, 3), 1),
    ("rems", (-7, 3), -1),
    ("rems", (7, 0), TRAP),
    ("divs", (INT_MIN, -1), TRAP),
    ("divs", (7, 0), TRAP),
    ("divs", (7, 3), 2),
]


def compile_elf(out):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "riscv", "-t", "rv32imac",
         "--all-exports", "--relocatable"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    if r.returncode != 0:
        sys.exit(f"compile failed: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"] - base
    return code, syms


def wasm_result(func, args):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    try:
        return inst.exports(st)[func](st, *args) & 0xFFFFFFFF
    except Exception:
        return TRAP


def run_rv(code, fa, args):
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_RISCV_REG_A0, args[0] & 0xFFFFFFFF)
    mu.reg_write(UC_RISCV_REG_A1, args[1] & 0xFFFFFFFF)
    mu.reg_write(UC_RISCV_REG_SP, STK)
    mu.reg_write(UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(CODE + fa, RET, timeout=5_000_000, count=10_000)
    except UcError:
        return TRAP  # ebreak -> breakpoint exception
    return mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    elf = "/tmp/rem_s_666_rv.o"
    compile_elf(elf)
    code, syms = load(elf)

    fails = 0
    for func, args, expected in CASES:
        want = expected if expected == TRAP else expected & 0xFFFFFFFF
        gt = wasm_result(func, args)
        if gt != want:
            sys.exit(f"harness bug: wasmtime {func}{args} = {gt}, expected {want}")
        if func not in syms:
            fails += 1
            print(f"FAIL {func}{args}: SYMBOL MISSING from ELF symtab")
            continue
        got = run_rv(code, syms[func], args)
        ok = got == gt
        fails += 0 if ok else 1
        print(f"{'OK  ' if ok else 'FAIL'} {func}{args}: synth={got} wasmtime={gt}")

    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
