#!/usr/bin/env python3
"""#382 — large static load/store offset (> imm12) differential oracle.

The optimized (non-relocatable) ARM path materializes the linear-memory base as
a compile-time constant (`MOVW/MOVT R12,#0x20000100`), adds the dynamic index
(`ADD R12,R12,Raddr`), then accesses `[R12,#offset]`. For `offset > 0xFFF` the
encoder's check_ldst_imm12 (#259) refuses the imm12 form (never masking), so the
whole function was skipped. Fix: `optimizer_bridge::fold_mem_offset` folds the
large constant offset into the constant base (access immediate becomes #0).

This harness runs the SAME call sequence under wasmtime (ground truth) and under
unicorn (synth's emitted ARM, absolute base), and compares. It is constructed so
a *dropped* offset is observable, not just a self-consistent roundtrip: a value
stored via `offset=5000` is read back through an ABSOLUTE load at `addr+5000`
(and symmetrically an `offset=5000` load reads a byte written absolutely). If the
store/load silently dropped the +5000, these cross-addressed reads diverge from
wasmtime.

Run (rebuild synth first):
  /tmp/n374venv/bin/python scripts/repro/load_store_big_offset_382_differential.py

Exits nonzero on mismatch so it can gate a release.
"""
import re
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_SP,
)

WAT = "scripts/repro/load_store_big_offset_382.wat"
WASM = "/tmp/ls382.wasm"
ELF = "/tmp/ls382_diff.elf"
SYNTH = "./target/debug/synth"

# Absolute linear-memory base the optimized path materializes (optimizer_bridge).
LIN_BASE = 0x20000100

# The call program: a list of (fn, args, expects_result). Cross-addressed so a
# dropped +5000 offset is observable. Run identically on both engines.
PROGRAM = [
    ("store_off", (0, 0xDEADBEEF), False),     # write word at addr 0, +5000 -> byte 5000
    ("load_abs", (5000,), True),               # absolute read of byte 5000  -> 0xDEADBEEF
    ("load_off", (0,), True),                  # offset read of addr 0 +5000 -> 0xDEADBEEF
    ("store_off", (16, 0x12345678), False),    # byte 5016
    ("load_abs", (5016,), True),               # -> 0x12345678
    ("store_h_off", (40, 0xBEEF), False),      # half-word at byte 5040
    ("load_hu_abs", (5040,), True),            # -> 0x0000BEEF
    ("load_off", (40,), True),                 # NB: load word at 5040 (BEEF + next bytes)
]


def run_wasmtime():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    exports = inst.exports(store)
    results = []
    for fn, args, want in PROGRAM:
        r = exports[fn](store, *args)
        if want:
            results.append(r & 0xFFFFFFFF)
    return results


def run_unicorn():
    subprocess.run(
        [SYNTH, "compile", WASM, "-t", "cortex-m4", "--all-exports", "-o", ELF],
        check=True, capture_output=True,
    )
    dis = subprocess.run([SYNTH, "disasm", ELF], capture_output=True, text=True).stdout
    syms = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r'^([0-9a-f]{8}) <(\w+)>:', dis, re.M)}
    text = ELFFile(open(ELF, "rb")).get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]

    CODE, LIN, STK = 0x10000, LIN_BASE & ~0xFFFF, 0x30000000
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN, 0x10000)          # covers LIN_BASE .. LIN_BASE+0xFEFF (byte 5040 OK)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_write(CODE, code)
    RET = 0x1F00 | 1

    results = []
    for fn, args, want in PROGRAM:
        for i, a in enumerate(args):
            mu.reg_write(UC_ARM_REG_R0 + i, a & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_SP, STK)
        mu.reg_write(UC_ARM_REG_LR, RET)
        try:
            mu.emu_start((CODE + syms[fn] - base) | 1, RET & ~1, count=2000)
        except UcError as e:
            return f"ERR in {fn}{args}: {e}"
        if want:
            results.append(mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF)
    return results


def main():
    subprocess.run(["wat2wasm", WAT, "-o", WASM], check=True)
    gt = run_wasmtime()
    got = run_unicorn()
    print(f"wasmtime (ground truth): {[f'0x{x:08X}' for x in gt]}")
    if isinstance(got, str):
        print(f"synth ARM             : {got}")
        print("MISMATCH  <-- #382")
        sys.exit(1)
    print(f"synth ARM             : {[f'0x{x:08X}' for x in got]}")
    ok = got == gt
    print(f"\n{len(got)}/{len(gt)} match" if ok
          else f"\nMISMATCH  <-- #382 (got {got} vs {gt})")
    print("ORACLE: PASS" if ok else "ORACLE: FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
