#!/usr/bin/env python3
"""#587 — DIRECT-PATH i64 spill-slot pool-grow differential oracle (epic #242).

`i64_spill_pool_587.wat` keeps twenty i64 constants simultaneously live —
~16 concurrent pair spills at peak, double the fixed 8-slot pool — so the
whole function used to loud-skip with "i64 spill-slot pool exhausted". The
backend's `pool-grow` recovery rung now retries with the pool sized from the
operand-stack-depth bound, so the function compiles; this oracle proves the
grown-pool code is CORRECT, not just present: wasmtime is ground truth,
unicorn runs synth's ARM, and the non-commutative fold (sub/xor with
distinct byte patterns per constant) makes any slot collision, lost store,
wrong-slot reload, or lo/hi swap change the result.

Covers the DIRECT path both ways it is reached: `--relocatable` (falcon) and
the default path (the optimized selector's pair pool also exhausts on this
shape and declines to direct — #496). i64 results read from r0 (lo):r1 (hi).

Exits nonzero on any mismatch or skip, so it can gate CI.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth /tmp/synthvenv/bin/python \
      scripts/repro/i64_spill_pool_587_differential.py
"""

import os
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("i64_spill_pool_587.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET, R11 = 0x100000, 0x900000, 0x300000, 0x20000000
ARGS = [0, 1, 0xDEADBEEF, 0xFFFFFFFF]


def wasmtime_run(arg):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    a = arg - (1 << 32) if arg >= (1 << 31) else arg
    return inst.exports(store)["hp20"](store, a) & 0xFFFFFFFFFFFFFFFF


def compile_synth(out, relocatable):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "arm",
           "--target", "cortex-m4", "--all-exports"]
    if relocatable:
        cmd.append("--relocatable")
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping function" in r.stderr:
        sys.exit(f"FAIL: compile failed/skipped (reloc={relocatable}) — the "
                 f"#587 pool-grow rung did not rescue hp20:\n{r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name and sy["st_info"]["type"] == "STT_FUNC":
                    syms[sy.name] = sy["st_value"]
    return code, base, syms


def unicorn_run(code, base, faddr, arg):
    foff = (faddr & ~1) - base
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, R11)
    mu.reg_write(UC_ARM_REG_R0, arg & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + foff) | 1, RET, count=200000)
    except UcError as e:
        return f"ERR:{e}"
    return (mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF) | (
        (mu.reg_read(UC_ARM_REG_R1) & 0xFFFFFFFF) << 32)


def run_path(label, relocatable):
    out = f"/tmp/i587_{'rel' if relocatable else 'opt'}.o"
    compile_synth(out, relocatable)
    code, base, syms = load(out)
    print(f"\n=== {label} path ===")
    if "hp20" not in syms:
        print("  [BUG] hp20: SYMBOL MISSING")
        return 1
    fails = 0
    for arg in ARGS:
        exp = wasmtime_run(arg)
        got = unicorn_run(code, base, syms["hp20"], arg)
        ok = isinstance(got, int) and got == exp
        fails += 0 if ok else 1
        print(f"  [{'ok ' if ok else 'BUG'}] hp20({arg:#x}) -> "
              + (f"{got:#x}" if isinstance(got, int) else str(got))
              + f"  (wasmtime {exp:#x})")
    return fails


def main():
    fails = run_path("DIRECT (--relocatable)", relocatable=True)
    fails += run_path("DEFAULT (optimized declines to direct)", relocatable=False)
    print("\n--- verdict ---")
    if fails == 0:
        print("RESULT: PASS — the previously pool-exhausted i64-dense function "
              "compiles via the #587 pool-grow rung and matches wasmtime on "
              "both paths.")
        sys.exit(0)
    print(f"RESULT: FAIL — {fails} divergence(s).")
    sys.exit(1)


if __name__ == "__main__":
    main()
