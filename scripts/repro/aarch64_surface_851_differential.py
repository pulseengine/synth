#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 58
"""#851 v0.53 — execution-differential for the aarch64 op-surface closes.

The VCR-SEL-005 third-backend enumeration (cross_backend_op_parity.rs, aarch64
leg) measured 20 integer-core ops ARM lowers that aarch64 loud-declined;
thirteen were closed in v0.53: `select` (CSEL/FCSEL, all four value types),
`drop`, `nop`, `i32.wrap_i64`, `i64.extend_i32_{s,u}`, the five in-place sign
extensions, and fixed-memory `memory.size`/`memory.grow`. This harness
execution-verifies each of them: compiles `aarch64_surface_851.wat` with
`synth compile -b aarch64 --all-exports`, runs every exported probe under
unicorn (A64 emulation), and diffs bit-exact against wasmtime.

Adversarial detail (AAPCS64): a caller may leave GARBAGE in the upper 32 bits
of an i32 argument register. Every i32 argument here is written with poisoned
upper bits (0x5A5A5A5A_xxxxxxxx), so a lowering that reads the X view of an
i32 (the wrap/extend hazard class) diverges from wasmtime and fails this gate.

The module pins `(memory 2 2)` (min = max) so `memory.grow(n>0)` must fail
(-1) in wasmtime as well — the aarch64 fixed-buffer lowering's growth failure
is spec-permitted in general, but pinning max makes it spec-forced, so the
differential asserts REAL parity rather than an always-allowed divergence.

RED-first: before the v0.53 lowerings `synth compile` fails on the first
declined op (`select`), so this gate is RED; after them it is GREEN.

Runs on any host (unicorn emulates A64). Needs wasmtime + unicorn + pyelftools:
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_surface_851_differential.py
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
    UC_ARM64_REG_D0,
    UC_ARM64_REG_D1,
    UC_ARM64_REG_LR,
    UC_ARM64_REG_S0,
    UC_ARM64_REG_S1,
    UC_ARM64_REG_SP,
    UC_ARM64_REG_X0,
    UC_ARM64_REG_X1,
    UC_ARM64_REG_X2,
    UC_ARM64_REG_X28,
)

WAT = Path(__file__).with_name("aarch64_surface_851.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, STK, RET = 0x100000, 0x400000, 0x500000
LINMEM = 0x1000000
LINMEM_SIZE = 0x20000  # 128 KiB = the (memory 2) declared minimum

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1
POISON = 0x5A5A_5A5A << 32  # garbage upper bits for i32 args (AAPCS-legal)

NAN32 = 0x7FC00000
NAN64 = 0x7FF8000000000000

# (fn, [param kinds], result kind, [arg case lists]) — kinds: i32/i64/f32/f64.
# f32/f64 args are given as BIT PATTERNS (ints); results compared bit-exact.
CASES = [
    # select: both arms, boundary values, cond 0/1/nonzero.
    ("sel32", ["i32", "i32", "i32"], "i32",
     [(10, 20, 1), (10, 20, 0), (0x80000000, 0x7FFFFFFF, 2),
      (0xFFFFFFFF, 0, 0), (7, 9, 0xFFFFFFFF)]),
    ("sel64", ["i64", "i64", "i32"], "i64",
     [(0x0123456789ABCDEF, 0xFEDCBA9876543210, 1),
      (0x0123456789ABCDEF, 0xFEDCBA9876543210, 0),
      (M64, 0, 1), (M64, 0, 0)]),
    ("self32", ["f32", "f32", "i32"], "f32",
     [(0x3F800000, 0x40000000, 1), (0x3F800000, 0x40000000, 0),
      (NAN32, 0x3F800000, 1), (NAN32, 0x3F800000, 0),
      (0x80000000, 0x00000000, 1)]),  # -0.0 vs +0.0: bit-exact carry
    ("self64", ["f64", "f64", "i32"], "f64",
     [(0x3FF0000000000000, 0x4000000000000000, 1),
      (0x3FF0000000000000, 0x4000000000000000, 0),
      (NAN64, 0x3FF0000000000000, 0),
      (0x8000000000000000, 0, 1)]),
    # wrap / extends — poisoned upper bits on every i32 arg (see POISON).
    ("wrap", ["i64"], "i32",
     [(0x1_00000001,), (M64,), (0x7FFFFFFF,), (0xDEADBEEF_80000000,)]),
    ("ext32s", ["i32"], "i64", [(0x80000000,), (0x7FFFFFFF,), (0,), (M32,)]),
    ("ext32u", ["i32"], "i64", [(0x80000000,), (0x7FFFFFFF,), (0,), (M32,)]),
    ("e8", ["i32"], "i32", [(0x80,), (0x7F,), (0x1234AB80,), (M32,)]),
    ("e16", ["i32"], "i32", [(0x8000,), (0x7FFF,), (0x1234_8000,), (M32,)]),
    ("e648", ["i64"], "i64", [(0x80,), (0x7F,), (0xFFFF_FF80,), (M64,)]),
    ("e6416", ["i64"], "i64", [(0x8000,), (0x7FFF,), (0xFFFF_8000,), (M64,)]),
    ("e6432", ["i64"], "i64",
     [(0x80000000,), (0x7FFFFFFF,), (0x1_00000000,), (M64,)]),
    # nop + drop
    ("dn", ["i32"], "i32", [(41,), (M32,)]),
    # fixed-memory size/grow: size=2 pages; grow(0)=2, grow(n>0)=-1; a failed
    # grow must not change the observed size.
    ("msize", [], "i32", [()]),
    ("mgrow", ["i32"], "i32", [(0,), (1,), (100,)]),
    ("growsize", ["i32"], "i32", [(0,), (1,)]),
]


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def bits_to_float(bits, kind):
    if kind == "f32":
        return struct.unpack("<f", struct.pack("<I", bits))[0]
    return struct.unpack("<d", struct.pack("<Q", bits))[0]


def wasmtime_runner():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))

    def run(fn, kinds, args):
        store = wasmtime.Store(engine)
        exports = wasmtime.Instance(store, module, []).exports(store)
        wargs = []
        for k, a in zip(kinds, args):
            if k == "i32":
                wargs.append(sx(a, 32))
            elif k == "i64":
                wargs.append(sx(a, 64))
            else:
                wargs.append(bits_to_float(a, k))
        return exports[fn](store, *wargs)

    return run


def compile_aarch64(out):
    cmd = [SYNTH, "compile", str(WAT), "-o", out, "-b", "aarch64", "--all-exports"]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={"PATH": "/usr/bin:/bin"})
    if r.returncode != 0 or "skipping" in r.stderr:
        return None, f"aarch64 compile failed/skipped: {r.stderr.strip()}"
    return out, None


def load_elf(elf):
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


def new_uc(code):
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(STK - 0x10000, 0x20000)
    mu.mem_map(RET & ~0xFFF, 0x1000)
    mu.mem_map(LINMEM, LINMEM_SIZE)
    mu.mem_write(CODE, code)
    return mu


def call(mu, code_base, faddr, kinds, rkind, args):
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    mu.reg_write(UC_ARM64_REG_X28, LINMEM)
    xregs = [UC_ARM64_REG_X0, UC_ARM64_REG_X1, UC_ARM64_REG_X2]
    sregs = [UC_ARM64_REG_S0, UC_ARM64_REG_S1]
    dregs = [UC_ARM64_REG_D0, UC_ARM64_REG_D1]
    ngrn = nsrn = 0
    for k, v in zip(kinds, args):
        if k == "i32":
            # POISON the upper bits: AAPCS64 lets the caller leave garbage
            # there, so a lowering reading the X view of an i32 must fail here.
            mu.reg_write(xregs[ngrn], (v & M32) | POISON)
            ngrn += 1
        elif k == "i64":
            mu.reg_write(xregs[ngrn], v & M64)
            ngrn += 1
        elif k == "f32":
            mu.reg_write(sregs[nsrn], v & M32)
            nsrn += 1
        else:
            mu.reg_write(dregs[nsrn], v & M64)
            nsrn += 1
    try:
        mu.emu_start(CODE + (faddr - code_base), RET, count=4000)
    except UcError as e:
        return f"ERR:{e}"
    if rkind == "i32":
        return mu.reg_read(UC_ARM64_REG_X0) & M32
    if rkind == "i64":
        return mu.reg_read(UC_ARM64_REG_X0) & M64
    if rkind == "f32":
        return mu.reg_read(UC_ARM64_REG_S0) & M32
    return mu.reg_read(UC_ARM64_REG_D0) & M64


def expected_bits(wt_val, rkind):
    if rkind == "i32":
        return wt_val & M32
    if rkind == "i64":
        return wt_val & M64
    if rkind == "f32":
        return struct.unpack("<I", struct.pack("<f", wt_val))[0]
    return struct.unpack("<Q", struct.pack("<d", wt_val))[0]


def main():
    out, err = compile_aarch64("/tmp/aarch64_surface_851.o")
    if err:
        print("RED (expected before the v0.53 #851 op-surface closes):", err)
        sys.exit(1)
    code, base, syms = load_elf(out)
    wt_run = wasmtime_runner()

    fails, total = 0, 0
    for fn, kinds, rkind, arglists in CASES:
        if fn not in syms:
            print(f"BUG {fn}: symbol missing (op declined?)")
            fails += 1
            continue
        for args in arglists:
            total += 1
            exp = expected_bits(wt_run(fn, kinds, args), rkind)
            mu = new_uc(code)
            got = call(mu, base, syms[fn], kinds, rkind, args)
            if got != exp:
                fails += 1
                print(f"BUG {fn}{tuple(hex(a) for a in args)} "
                      f"A64={got if isinstance(got, str) else hex(got)} "
                      f"wasmtime={hex(exp)}")

    if fails:
        print(f"FAIL: {fails}/{total} aarch64 surface checks diverged")
        sys.exit(1)
    print(f"PASS: {total} aarch64 #851 op-surface checks bit-identical to "
          f"wasmtime (select x4 types incl. NaN/-0, wrap/extends with poisoned "
          f"upper bits, drop/nop, fixed-memory size/grow)")


if __name__ == "__main__":
    main()
