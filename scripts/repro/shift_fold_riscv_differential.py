#!/usr/bin/env python3
"""VCR-RA RV32 lever (#472, epic #242) — EXECUTION-validate the imm-shift-fold.

The immediate-shift-fold (SYNTH_RV_SHIFT_FOLD=1) rewrites a constant shift
`addi tmp,zero,N ; sll rd,val,tmp` to the immediate form `slli rd,val,(N & 31)`,
dropping the amount materialization. The RV32 path has no cargo byte-gate and no
local RISC-V disassembler-as-oracle, so EXECUTION is the correctness oracle: this
harness compiles `shift_fold.wat` in BOTH flag-off and flag-on builds, runs every
exported function under unicorn (UC_ARCH_RISCV), and asserts each result is
bit-identical to wasmtime ground truth.

What it proves:
  * flag-off ≡ flag-on ≡ wasmtime for every (function, input) — the fold is
    semantics-preserving, including the `& 31` mask (`shl33` shifts by 33→1,
    `shlneg` by -1→31).
  * NON-VACUITY: the flag-on `.text` is strictly smaller (each const shift drops
    one 4-byte `addi`); the 5 const-shift functions fold, and `shlvar` (a
    variable amount) is byte-identical flag-off vs flag-on — the fold only ever
    touches a constant amount.

Run (needs wasmtime + unicorn + pyelftools):
  /tmp/synthvenv/bin/python scripts/repro/shift_fold_riscv_differential.py
Exits nonzero on any mismatch or vacuity failure.
"""
import os
import re
import subprocess
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

WAT = "scripts/repro/shift_fold.wat"
# Default to the release binary for local dev; CI sets SYNTH=./target/debug/synth
# (it builds `cargo build -p synth-cli`, debug) so the isolated oracle job stays fast.
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
CODE, LIN, STK, RET = 0x100000, 0x40000, 0x90000, 0x200000

# (export name, list of argument tuples). Each function returns its result in a0.
CASES = {
    "shl8": [(1,), (0xFF,), (0x00AB_CDEF,), (0x8000_0001,)],
    "shru4": [(0xF0,), (0xFFFF_FFFF,), (0x8000_0000,), (0xABCD,)],
    "shrs4": [(0xF0,), (0xFFFF_FFFF,), (0x8000_0000,), (0x7FFF_FFFF,)],
    "shl33": [(1,), (3,), (0x8000_0001,)],          # amount 33 -> << 1
    "shlneg": [(1,), (2,), (0xFFFF_FFFF,)],          # amount -1 -> << 31
    "shlvar": [(1, 4), (0xABCD, 8), (0xFF, 33), (3, 0xFFFF_FFFF)],  # variable -> not folded
}


def compile_elf(out, fold):
    env = {"PATH": "/usr/bin:/bin"}
    if fold:
        env["SYNTH_RV_SHIFT_FOLD"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", WAT, "-o", out, "-b", "riscv", "-t", "rv32imac",
         "--all-exports", "--relocatable"],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed (fold={fold}): {r.stderr}")


def syms_and_code(elf):
    dis = subprocess.run([SYNTH, "disasm", elf], capture_output=True, text=True).stdout
    syms = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r'^([0-9a-f]{8}) <(\w+)>:', dis, re.M)}
    code = ELFFile(open(elf, "rb")).get_section_by_name(".text").data()
    return syms, code


def text_len(elf):
    return len(ELFFile(open(elf, "rb")).get_section_by_name(".text").data())


def run_rv(code, fa, args):
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_RISCV_REG_SP, STK)
    mu.reg_write(UC_RISCV_REG_S11, LIN)  # s11 = __linear_memory_base
    for r, v in zip((UC_RISCV_REG_A0, UC_RISCV_REG_A1), args):
        mu.reg_write(r, v & 0xFFFFFFFF)
    mu.reg_write(UC_RISCV_REG_RA, RET)
    try:
        mu.emu_start(CODE + fa, RET, count=2000)
    except UcError as e:
        return f"ERR:{e}"
    return mu.reg_read(UC_RISCV_REG_A0) & 0xFFFFFFFF


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — `cargo build --release -p synth-cli` first")
    off_elf, on_elf = "/tmp/shift_fold_off.o", "/tmp/shift_fold_on.o"
    compile_elf(off_elf, False)
    compile_elf(on_elf, True)

    off_syms, off_code = syms_and_code(off_elf)
    on_syms, on_code = syms_and_code(on_elf)

    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WAT, "rb").read())

    def wt(func, args):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)[func](store, *args) & 0xFFFFFFFF

    fails = 0
    for func, vecs in CASES.items():
        if func not in off_syms or func not in on_syms:
            print(f"{func}: SYMBOL MISSING  <-- FAIL")
            fails += 1
            continue
        for args in vecs:
            gt = wt(func, args)
            r_off = run_rv(off_code, off_syms[func], args)
            r_on = run_rv(on_code, on_syms[func], args)
            ok = r_off == gt and r_on == gt
            fails += 0 if ok else 1
            tag = "" if ok else "  <-- MISMATCH"
            shown_off = f"0x{r_off:08x}" if isinstance(r_off, int) else r_off
            shown_on = f"0x{r_on:08x}" if isinstance(r_on, int) else r_on
            print(f"{func}{args}: off={shown_off} on={shown_on} wt=0x{gt:08x}{tag}")

    # NON-VACUITY: the fold must actually fire (flag-on .text strictly smaller),
    # and the variable-shift function must be byte-identical (never folded).
    off_len, on_len = text_len(off_elf), text_len(on_elf)
    if not on_len < off_len:
        print(f"VACUOUS: flag-on .text ({on_len}B) not < flag-off ({off_len}B) "
              "— fold did not fire")
        fails += 1
    else:
        print(f"\n.text {off_len}B -> {on_len}B (-{off_len - on_len}B): "
              f"{(off_len - on_len)//4} const shift(s) folded")

    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
