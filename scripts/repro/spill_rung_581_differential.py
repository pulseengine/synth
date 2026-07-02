#!/usr/bin/env python3
"""#581 — DIRECT-selector spill-rung differential: unicorn vs wasmtime.

The direct selector's spill rung (the backend's exhaustion retry,
VCR-RA-001 3b-lite) spills the deepest live vstack value when materializing a
constant exhausts the register pool. The spill STR is tagged with the const's
source_line — and the #253 add/sub immediate fold dropped the materialization
BY source_line, deleting the spill store with it. The victim's stack entry
stayed `Spilled`, so its reload read a never-written frame slot: a silent
wrong value on the shipped `--relocatable` path (issue #581; found by the
#580 lane on `spill_on_exhaust_242.wat`, hp(1,2) = 0xffffd1ce vs wasmtime
0x2e37).

Runs BOTH fixtures on the direct path (default env — the spill rung is the
backend's built-in retry ladder, no flag) over several argument pairs:
  * scripts/repro/spill_rung_581.wat        — the minimal fold-deletes-store shape
  * scripts/repro/spill_on_exhaust_242.wat  — the original discovery fixture

Exits nonzero on any mismatch so it can gate a release.

Run (rebuild synth first):
  SYNTH=/Volumes/devcache/wave15-581/debug/synth \
    /tmp/synthvenv/bin/python scripts/repro/spill_rung_581_differential.py
"""

import os
import subprocess
import sys

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

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

FIXTURES = [
    "scripts/repro/spill_rung_581.wat",
    "scripts/repro/spill_on_exhaust_242.wat",
]

ARGS = [(1, 2), (0, 0), (7, 3), (0xFFFFFFFF, 1), (12345, 54321), (2, 1)]

LIN_BASE = 0x20000000
MASK32 = 0xFFFFFFFF


def symtab(path):
    """Function symbols from the ELF symtab (NOT disasm text — host-dependent)."""
    with open(path, "rb") as f:
        elf = ELFFile(f)
        out = {}
        for sec in elf.iter_sections():
            if sec["sh_type"] != "SHT_SYMTAB":
                continue
            for s in sec.iter_symbols():
                if s["st_info"]["type"] == "STT_FUNC" and s.name:
                    out[s.name] = s["st_value"] & ~1
        return out


def run_wasmtime(wasm):
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(wasm, "rb").read())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    hp = inst.exports(store)["hp"]
    out = []
    for a, b in ARGS:
        # wasmtime takes i32 params as signed
        sa = a - (1 << 32) if a > 0x7FFFFFFF else a
        sb = b - (1 << 32) if b > 0x7FFFFFFF else b
        out.append(hp(store, sa, sb) & MASK32)
    return out


def run_unicorn(wasm, elf):
    subprocess.run(
        [SYNTH, "compile", wasm, "-t", "cortex-m4", "--relocatable", "-o", elf],
        check=True,
        capture_output=True,
    )
    syms = symtab(elf)
    fn = syms.get("hp", syms.get("func_0"))
    if fn is None:
        return f"ERR: no hp/func_0 symbol in {elf} (have {sorted(syms)})"
    with open(elf, "rb") as f:
        text = ELFFile(f).get_section_by_name(".text")
        code, base = text.data(), text["sh_addr"]

    CODE, STK = 0x10000, 0x30000000
    RET = CODE + 0xF000
    out = []
    for a, b in ARGS:
        mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        mu.mem_map(CODE, 0x10000)
        mu.mem_map(LIN_BASE, 0x10000)
        mu.mem_map(STK - 0x8000, 0x10000)
        mu.mem_write(CODE, code)
        mu.reg_write(UC_ARM_REG_R0, a)
        mu.reg_write(UC_ARM_REG_R1, b)
        mu.reg_write(UC_ARM_REG_R11, LIN_BASE)
        mu.reg_write(UC_ARM_REG_SP, STK)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        try:
            mu.emu_start((CODE + fn - base) | 1, RET, count=10000)
        except UcError as e:
            return f"ERR in hp({a},{b}): {e}"
        out.append(mu.reg_read(UC_ARM_REG_R0) & MASK32)
    return out


def main():
    fail = False
    for wat in FIXTURES:
        name = os.path.basename(wat)
        wasm = f"/tmp/{name}.wasm"
        elf = f"/tmp/{name}.o"
        subprocess.run(["wat2wasm", wat, "-o", wasm], check=True)
        gt = run_wasmtime(wasm)
        got = run_unicorn(wasm, elf)
        print(f"== {name} ==")
        print(f"  args                 : {ARGS}")
        print(f"  wasmtime (truth)     : {[hex(x) for x in gt]}")
        if isinstance(got, str):
            print(f"  synth ARM (unicorn)  : {got}")
            print("  MISMATCH  <-- #581")
            fail = True
            continue
        print(f"  synth ARM (unicorn)  : {[hex(x) for x in got]}")
        if got != gt:
            bad = [
                f"hp{ARGS[i]}: got {hex(got[i])} want {hex(gt[i])}"
                for i in range(len(gt))
                if got[i] != gt[i]
            ]
            print(f"  MISMATCH  <-- #581: {'; '.join(bad)}")
            fail = True
        else:
            print(f"  {len(got)}/{len(gt)} match")
    print("\nORACLE:", "FAIL" if fail else "PASS")
    sys.exit(1 if fail else 0)


if __name__ == "__main__":
    main()
