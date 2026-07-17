#!/usr/bin/env python3
"""#791 — EXECUTION-validate const-only-body returns on the optimized path.

On the OPTIMIZED (default self-contained) ARM path, a function whose result is
a bare `i32.const` materialized the constant into a callee-saved temp (r4) and
never moved it to R0: `push {r4,lr}; movs r4,#100; pop {r4,pc}` — the export
returns whatever the caller had in R0 (AAPCS reads R0). Root cause: the
`Opcode::Const` arm in `optimizer_bridge::ir_to_arm` was the only
value-producing arm that did not record its dest as `last_result_vreg`, so the
epilogue's move-result-to-R0 pass never fired (and could fire on a STALE vreg
from an earlier op — the `stale` case returns the wrong live value, not just
caller residue).

This harness compiles the fixture via the optimized path (default
self-contained, `-b arm`), runs each export under unicorn (UC_ARCH_ARM /
Thumb) with SENTINEL values pre-loaded in R0/R1 (so "R0 happened to be right"
can't false-green), and asserts the returned R0 (R0:R1 for i64) matches
wasmtime ground truth.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/const_body_791_differential.py
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
    UC_ARM_REG_R4,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("const_body_791.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
# (export, result kind) — every function is nullary; the observable is R0
# (R0:R1 for i64).
CASES = [
    ("c100", "i32"),
    ("c64", "i64"),
    ("clocals", "i32"),
    ("stale", "i32"),
    ("tailret", "i32"),
    ("getzero", "i32"),
]
SENTINEL_R0 = 0xDEADBEEF  # caller residue the bug leaks back
SENTINEL_R1 = 0xCAFEF00D
SENTINEL_R4 = 0x5A5A5A5A  # caller's saved r4 — restored by `pop {r4,pc}`


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


def wasm_result(func):
    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])
    return inst.exports(st)[func](st)


def run_arm(code, base, addr, kind):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(base & ~0xFFFF, 0x20000)
    mu.mem_write(base, code)
    mu.mem_map(0x90000, 0x10000)
    ret = 0x90100
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.reg_write(UC_ARM_REG_R0, SENTINEL_R0)
    mu.reg_write(UC_ARM_REG_R1, SENTINEL_R1)
    mu.reg_write(UC_ARM_REG_R4, SENTINEL_R4)
    mu.reg_write(UC_ARM_REG_SP, 0x98000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    mu.emu_start(addr | 1, ret, timeout=5_000_000)
    r0 = mu.reg_read(UC_ARM_REG_R0)
    if kind == "i64":
        return r0 | (mu.reg_read(UC_ARM_REG_R1) << 32)
    return r0


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    elf = "/tmp/const_body_791.elf"
    compile_optimized(elf)
    code, base, syms = load(elf)

    fails = 0
    for func, kind in CASES:
        mask = 0xFFFFFFFFFFFFFFFF if kind == "i64" else 0xFFFFFFFF
        gt = wasm_result(func) & mask
        got = run_arm(code, base, syms[func], kind) & mask
        ok = got == gt
        if not ok:
            fails += 1
        print(f"{'OK  ' if ok else 'FAIL'} {func}() = {got:#x}  (wasmtime: {gt:#x})")

    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
