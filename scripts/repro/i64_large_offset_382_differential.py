#!/usr/bin/env python3
"""#382 (direct/relocatable path) — i64 large static load/store offset oracle.

The direct selector (`--relocatable`, R11/fp = linear-memory base) lowers a
memory `i64.load`/`i64.store` at `offset > 0xFFF` to an `I64Ldr`/`I64Str` whose
encoder previously accessed the high half at `[ip,#offset+4]` — an imm12 the
`check_ldst_imm12` guard (#259) refused, skipping the WHOLE function. The fix
(`arm_encoder::i64_effective_base`) folds the large offset into the base
(`ADD ip, index, #offset; ADD ip, ip, base`) so the halves use `#0`/`#4`.

This harness runs the SAME call program under wasmtime (ground truth) and under
unicorn (synth's emitted Thumb-2, R11 = linear-memory base). It cross-addresses
so a *dropped* offset is observable, not just a self-consistent roundtrip: a
value stored via `offset=5000` is read back through an ABSOLUTE load at
`addr+5000` (and symmetrically). i32 cases are a regression guard (they already
lowered via #206/#372). Exits nonzero on mismatch so it can gate a release.

Run (rebuild synth first):
  SYNTH=/Volumes/devcache/wave6-382/debug/synth \
    /tmp/synthvenv/bin/python scripts/repro/i64_large_offset_382_differential.py
"""
import os
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
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = "scripts/repro/i64_large_offset_382.wat"
WASM = "/tmp/i64_lo382.wasm"
ELF = "/tmp/i64_lo382_diff.o"
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# In the direct/relocatable path R11 (fp) holds the linear-memory base, set by
# the caller. Any mapped, non-zero base works; the offsets stay in one 64 KiB page.
LIN_BASE = 0x20000000

MASK64 = (1 << 64) - 1
V64 = 0x1122334455667788
V64B = 0x8877665544332211


# Each step: (fn, arg_regs, is_i64_result). `arg_regs` is the AAPCS register map
# {reg_index: value} — i64 value params land in R2:R3 (even-aligned, R1 skipped),
# matching what the direct selector homes (#518).
def i64_args(addr, val):
    return {0: addr, 2: val & 0xFFFFFFFF, 3: (val >> 32) & 0xFFFFFFFF}


PROGRAM = [
    ("store64_off", {0: 0, **i64_args(0, V64)}, False),   # write 8 bytes at byte 5000
    ("load64_abs", {0: 5000}, True),                      # absolute read -> V64
    ("load64_off", {0: 0}, True),                         # offset read of addr 0 -> V64
    ("store64_off", {0: 24, **i64_args(24, V64B)}, False),  # byte 5024
    ("load64_abs", {0: 5024}, True),                      # -> V64B
    ("store32_off", {0: 64, 1: 0xDEADBEEF}, False),       # word at byte 5064
    ("load32_abs", {0: 5064}, False),                     # -> 0xDEADBEEF
    ("load32_off", {0: 64}, False),                       # offset read -> 0xDEADBEEF
]


def run_wasmtime():
    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    exports = inst.exports(store)
    # Reconstruct positional args from the register map.
    results = []
    for fn, regs, is64 in PROGRAM:
        if fn.startswith("store64"):
            addr = regs[0]
            val = (regs[3] << 32) | regs[2]
            exports[fn](store, addr, val)
        elif fn.startswith("store32"):
            exports[fn](store, regs[0], regs[1])
        else:  # loads take a single addr in R0
            r = exports[fn](store, regs[0])
            results.append(r & (MASK64 if is64 else 0xFFFFFFFF))
    return results


def run_unicorn():
    subprocess.run(
        [SYNTH, "compile", WASM, "-t", "cortex-m4", "--relocatable",
         "--all-exports", "-o", ELF],
        check=True, capture_output=True,
    )
    dis = subprocess.run([SYNTH, "disasm", ELF], capture_output=True, text=True).stdout
    syms = {m.group(2): int(m.group(1), 16)
            for m in re.finditer(r'^([0-9a-f]{8}) <(\w+)>:', dis, re.M)}
    text = ELFFile(open(ELF, "rb")).get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]

    CODE, STK = 0x10000, 0x30000000
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN_BASE, 0x10000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_write(CODE, code)
    RET = 0x1F00 | 1

    results = []
    for fn, regs, is64 in PROGRAM:
        for reg, val in regs.items():
            mu.reg_write(UC_ARM_REG_R0 + reg, val & 0xFFFFFFFF)
        mu.reg_write(UC_ARM_REG_R11, LIN_BASE)
        mu.reg_write(UC_ARM_REG_SP, STK)
        mu.reg_write(UC_ARM_REG_LR, RET)
        try:
            mu.emu_start((CODE + syms[fn] - base) | 1, RET & ~1, count=4000)
        except UcError as e:
            return f"ERR in {fn}{regs}: {e}"
        if not fn.startswith("store"):
            lo = mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF
            if is64:
                hi = mu.reg_read(UC_ARM_REG_R1) & 0xFFFFFFFF
                results.append((hi << 32) | lo)
            else:
                results.append(lo)
    return results


def main():
    subprocess.run(["wat2wasm", WAT, "-o", WASM], check=True)
    gt = run_wasmtime()
    got = run_unicorn()
    print(f"wasmtime (ground truth): {[hex(x) for x in gt]}")
    if isinstance(got, str):
        print(f"synth ARM             : {got}")
        print("MISMATCH  <-- #382 (function skipped or wrong)")
        sys.exit(1)
    print(f"synth ARM             : {[hex(x) for x in got]}")
    ok = got == gt
    print(f"\n{len(got)}/{len(gt)} match" if ok
          else f"\nMISMATCH  <-- #382 (got {got} vs {gt})")
    print("ORACLE: PASS" if ok else "ORACLE: FAIL")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
