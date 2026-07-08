#!/usr/bin/env python3
"""#500 (epic #242) — EXECUTION-validate optimized-path forward-branch shapes.

#483 fixed the single `block`+`br_if` forward-exit; #500 shows the class is
broader. This harness pins the remaining named shapes:

  - ifelse      — if/else desugared as nested block + br_if + br (issue repro A)
  - seqblocks   — two sequential sibling blocks, each exited by br_if (repro B)
  - real_ifelse — a REAL wasm `if`/`else` construct (WasmOp::If/Else)
  - real_if     — `if` with no else, content after the join
  - br_func     — function-level `br` (depth reaches the implicit function body)
  - early_ret   — early (non-tail) `return` with live code after the block

Each function is compiled on the OPTIMIZED (non-`--relocatable`) path, executed
under unicorn (Thumb, linear memory mapped at the absolute base the optimized
path materializes), and its MEMORY is compared bit-identically against wasmtime
ground truth across both branch directions. The functions store to disjoint
addresses, so memory is the observable.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/cf_shapes_500_differential.py
Exits nonzero on any mismatch.
"""

import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("cf_shapes_500.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
# Absolute linear-memory base the optimized (non-relocatable) path materializes
# for a const address: `movw ip,#0x100; movt ip,#0x2000` → 0x20000100 (see #197).
LINMEM = 0x20000100
MEM_WINDOW = 64  # bytes of memory compared against ground truth
# function -> list of arg tuples exercising both branch directions
CASES = {
    "ifelse": [(0,), (1,)],
    "seqblocks": [(0, 0), (0, 1), (1, 0), (1, 1)],
    "real_ifelse": [(0,), (1,)],
    "real_if": [(0,), (1,)],
    "br_func": [(0,), (1,)],
    "early_ret": [(0,), (1,)],
}


def compile_optimized(out):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
         "--target", "cortex-m4", "--all-exports"],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"},
    )
    if r.returncode != 0:
        sys.exit(f"compile failed: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    data, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return data, base, syms


def wasm_mem(func, args):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    inst.exports(st)[func](st, *args)
    return bytes(inst.exports(st)["memory"].read(st, 0, MEM_WINDOW))


def run_arm(code, base, addr, args):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(base & ~0xFFFF, 0x20000)
    mu.mem_write(base, code)
    mu.mem_map(LINMEM & ~0xFFFF, 0x20000)  # page-aligned region covering LINMEM
    mu.mem_map(0x90000, 0x10000)
    ret = 0x90100
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    regs = [UC_ARM_REG_R0, UC_ARM_REG_R1]
    for reg, val in zip(regs, args):
        mu.reg_write(reg, val & 0xFFFFFFFF)
    # Declined shapes fall back to the DIRECT selector, whose memory accesses
    # are fp/R11-relative (the runtime linear-memory base register); seed it
    # like the startup code does. Optimized-path functions either materialize
    # the absolute base inline (ip) or re-materialize R11 themselves
    # (base-CSE), so the seed is invisible to them.
    mu.reg_write(UC_ARM_REG_R11, LINMEM)
    mu.reg_write(UC_ARM_REG_SP, 0x98000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    mu.emu_start(addr | 1, ret, timeout=5_000_000)
    return bytes(mu.mem_read(LINMEM, MEM_WINDOW))


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    elf = "/tmp/cf_shapes_500.elf"
    compile_optimized(elf)
    code, base, syms = load(elf)

    fails = 0
    for func, arglists in CASES.items():
        if func not in syms:
            fails += 1
            print(f"FAIL {func}: SYMBOL MISSING from ELF symtab")
            continue
        for args in arglists:
            gt = wasm_mem(func, args)
            try:
                got = run_arm(code, base, syms[func], args)
            except Exception as e:  # unicorn faults on garbage addresses
                fails += 1
                print(f"FAIL {func}{args}: unicorn fault: {e}")
                continue
            ok = got == gt
            if not ok:
                fails += 1
            print(f"{'OK  ' if ok else 'FAIL'} {func}{args}")
            if not ok:
                diff = [(i, gt[i], got[i]) for i in range(MEM_WINDOW) if gt[i] != got[i]]
                print(f"     mem diffs (off, wasmtime, synth): {diff}")

    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
