#!/usr/bin/env python3
"""#538 milestone-2 — validate the BROADENED aarch64 backend codegen end-to-end.

Compiles the m2 acceptance module with `synth compile -b aarch64`, then executes
each exported function's emitted A64 `.text` under unicorn (UC_ARCH_ARM64) and
diffs the result against wasmtime ground truth. This is the "third backend =
third oracle" property extended to the full i32 AND i64 integer ALU: shifts,
rotates, clz/ctz, compares, and the natively-64-bit i64 core.

Milestone 1 covered i32 add/sub/mul/and/or/xor + const; this harness adds every
op milestone 2 landed. i64 functions take their args in the 64-bit X registers
(AAPCS64: one X per arg, no even-alignment) and return in X0; i32 functions use
W and return W0. Each case carries its wasm signature so the harness sets the
right register width and masks the read to the result width.

Runs on any host (unicorn emulates A64); on an arm64 host the same `.text` also
runs natively.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_m2_538_differential.py
"""
import os
import struct
import subprocess
import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM64, UC_MODE_ARM, Uc, UcError
from unicorn.arm64_const import (
    UC_ARM64_REG_LR,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_W0,
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X1,
    UC_ARM64_REG_X2,
)

WAT = Path(__file__).with_name("aarch64_m2_538.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
CODE, STK, RET = 0x100000, 0x200000, 0x300000
X_ARGS = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2]

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1

# (fn, arg_width, result_width, [args...]). arg_width/result_width in bits.
# Interesting values: zero, wrap, sign boundaries, shift-count masking (>=width).
def C32(fn, *args):
    return [(fn, 32, 32, list(a)) for a in args]

def C64(fn, rw, *args):
    return [(fn, 64, rw, list(a)) for a in args]

CASES = []
# i32 shifts/rotates — include shift counts >= 32 to exercise mod-32 masking.
CASES += C32("i32_shl", (1, 4), (1, 31), (1, 32), (1, 33), (0xFFFFFFFF, 1))
CASES += C32("i32_shr_u", (0x80000000, 4), (0xFFFFFFFF, 31), (1, 32))
CASES += C32("i32_shr_s", (0x80000000, 4), (0xFFFFFFFF, 3), (0x7FFFFFFF, 1))
CASES += C32("i32_rotr", (0x12345678, 4), (1, 1), (1, 0), (1, 33))
CASES += C32("i32_rotl", (0x12345678, 4), (1, 31), (1, 0), (0x80000000, 1))
# i32 clz/ctz — zero input is the edge case (32).
CASES += C32("i32_clz", (1,), (0x80000000,), (0,), (0xFFFFFFFF,))
CASES += C32("i32_ctz", (1,), (0x80000000,), (0,), (8,))
# i32 compares.
CASES += C32("i32_eqz", (0,), (1,), (0xFFFFFFFF,))
for cmp in ("i32_eq", "i32_ne", "i32_lt_s", "i32_lt_u", "i32_le_s",
            "i32_le_u", "i32_gt_s", "i32_gt_u", "i32_ge_s", "i32_ge_u"):
    CASES += C32(cmp, (3, 3), (2, 5), (5, 2), (0xFFFFFFFF, 1), (1, 0xFFFFFFFF))
# i64 arithmetic/bitwise.
BIG = 0x0123456789ABCDEF
for a in ("i64_add", "i64_sub", "i64_mul", "i64_and", "i64_or", "i64_xor"):
    CASES += C64(a, 64, (BIG, 0xFEDCBA9876543210), (M64, 1), (0, 7))
# i64 shifts/rotates with counts >= 64 (mod-64 masking).
CASES += C64("i64_shl", 64, (1, 4), (1, 63), (1, 64), (1, 65))
CASES += C64("i64_shr_u", 64, (0x8000000000000000, 4), (M64, 63))
CASES += C64("i64_shr_s", 64, (0x8000000000000000, 4), (M64, 3))
CASES += C64("i64_rotr", 64, (0x0123456789ABCDEF, 8), (1, 0), (1, 65))
CASES += C64("i64_rotl", 64, (0x0123456789ABCDEF, 8), (1, 63), (1, 0))
# i64 clz/ctz.
CASES += C64("i64_clz", 64, (1,), (0x8000000000000000,), (0,))
CASES += C64("i64_ctz", 64, (1,), (0x8000000000000000,), (0,), (256,))
# i64 compares (result i32).
CASES += C64("i64_eqz", 32, (0,), (1,), (M64,))
for cmp in ("i64_eq", "i64_ne", "i64_lt_s", "i64_lt_u",
            "i64_le_s", "i64_gt_s", "i64_ge_u"):
    CASES += C64(cmp, 32, (BIG, BIG), (2, 5), (5, 2),
                 (0x8000000000000000, 1), (1, M64))
# i64 const materialization.
CASES += C64("i64_const_big", 64, (0,), (1,), (0x1111111111111111,))


def wasmtime_run(fn, args):
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    return wasmtime.Instance(store, module, []).exports(store)[fn](store, *args)


def compile_aarch64(out):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr:
        sys.exit(f"aarch64 compile failed/skipped: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    syms = {}
    for sec in f.iter_sections():
        if sec.header.sh_type == "SHT_SYMTAB":
            for sy in sec.iter_symbols():
                if sy.name:
                    syms[sy.name] = sy["st_value"] & ~1
    return code, base, syms


def unicorn_run(code, base, faddr, arg_width, result_width, args):
    off = faddr - base
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    mask = M32 if arg_width == 32 else M64
    for r, v in zip(X_ARGS, args):
        mu.reg_write(r, v & mask)  # X reg; low 32 bits are the W view
    try:
        mu.emu_start(CODE + off, RET, count=2000)
    except UcError as e:
        return f"ERR:{e}"
    if result_width == 32:
        raw = mu.reg_read(UC_ARM64_REG_W0) & M32
        return struct.unpack("<i", struct.pack("<I", raw))[0]
    raw = mu.reg_read(UC_ARM64_REG_X0) & M64
    return struct.unpack("<q", struct.pack("<Q", raw))[0]


def to_wasm_args(arg_width, args):
    # wasmtime wants python ints in the right signedness range; pass through
    # as-is (values are already the raw bit patterns; wasmtime i32/i64 wrap).
    if arg_width == 32:
        return [struct.unpack("<i", struct.pack("<I", a & M32))[0] for a in args]
    return [struct.unpack("<q", struct.pack("<Q", a & M64))[0] for a in args]


def main():
    out = "/tmp/aarch64_m2_538.o"
    compile_aarch64(out)
    code, base, syms = load(out)
    fails = 0
    total = 0
    missing = set()
    for fn, aw, rw, args in CASES:
        total += 1
        if fn not in syms:
            if fn not in missing:
                print(f"FAIL {fn}: symbol missing")
                missing.add(fn)
            fails += 1
            continue
        exp = wasmtime_run(fn, to_wasm_args(aw, args))
        got = unicorn_run(code, base, syms[fn], aw, rw, args)
        m = M32 if rw == 32 else M64
        ok = isinstance(got, int) and (got & m) == (exp & m)
        if not ok:
            fails += 1
            print(f"BUG {fn}{tuple(hex(a) for a in args)} A64={got} wasmtime={exp}")
    print(f"\n{total - fails}/{total} cases matched wasmtime")
    print("RESULT:", "PASS — aarch64 m2 codegen matches wasmtime (third oracle)"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
