#!/usr/bin/env python3
"""#851 — execution-differential for aarch64 linear-memory load/store.

Compiles a `(memory 1)` module of store/load round-trips with
`synth compile -b aarch64`, executes each function's emitted A64 `.text` under
unicorn with a REAL linear-memory region and the dedicated base register
`x28 = __linear_memory_base` on entry, and diffs the result bit-exact against
wasmtime. This is the memory analogue of the m2 "third backend = third oracle"
differential (`aarch64_m2_538_differential.py`) — every accepted load/store op
proven bit-identical to the WASM reference.

The dedicated-base convention (x28) — not sp-scratch — is validated by the
`wr`/`rd` pair: `wr` stores to a fixed linear-memory address in one function,
`rd` reads it in a SEPARATE function; they agree only because both address the
same ambient base. A store to stack scratch would not survive across the call.

RED-first: before the #851 lowering every memory op loud-declines
(`unsupported wasm op for aarch64 subset`), so `synth compile` fails and the
symbols are absent → this gate is RED. After the lowering it is GREEN.

SOUNDNESS / honest frontier: the lowering computes the WASM effective address
and dereferences it — it does NOT bounds-check. All inputs here are IN-BOUNDS;
out-of-bounds trap, data-segment init, and memory.{size,grow} are the documented
follow-on frontier (the host-native subset has no memory-size convention yet).

Runs on any host (unicorn emulates A64). Needs wasmtime + unicorn + pyelftools:
  SYNTH=<target>/debug/synth python scripts/repro/aarch64_mem_851_differential.py
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
    UC_ARM64_REG_X28,
)

WAT = Path(__file__).with_name("aarch64_mem_851.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

# Address map (unicorn). LINMEM is the wasm linear memory (1 page = 64 KiB);
# x28 is set to its base on entry, matching the synth aarch64 base convention.
CODE, STK, RET = 0x100000, 0x400000, 0x500000
LINMEM = 0x1000000
LINMEM_SIZE = 0x20000  # 128 KiB mapped (>= the 1-page module + bigoff test)

M32 = (1 << 32) - 1
M64 = (1 << 64) - 1

# (fn, [ (arg_width_bits...) per param ], result_width_bits, [args...]).
# The first param of every round-trip is an i32 ADDRESS (kept small + aligned so
# in-bounds); the second is the value (i32 or i64). wr/rd take/return one value.
def case(fn, pw, rw, *arglists):
    return [(fn, pw, rw, list(a)) for a in arglists]


CASES = []
# i32 word round-trips at assorted in-bounds addresses + value bit-patterns.
CASES += case("rt_i32", [32, 32], 32,
              (0, 0x12345678), (16, 0xFFFFFFFF), (4092, 0x80000000), (256, 42))
CASES += case("rt_i32_off", [32, 32], 32, (0, 0xDEADBEEF), (100, 0x7FFFFFFF))
CASES += case("rt_i32_bigoff", [32, 32], 32, (0, 0xCAFEBABE), (8, 0x01020304))
# sub-word: value's high bits must be dropped by the narrow store, and the load
# form must zero/sign-extend the retrieved byte/halfword correctly.
CASES += case("rt_i32_8u", [32, 32], 32, (0, 0x000000FF), (7, 0x1234AB80), (32, 0x7F))
CASES += case("rt_i32_8s", [32, 32], 32, (0, 0x00000080), (7, 0x1234AB7F), (32, 0xFF))
CASES += case("rt_i32_16u", [32, 32], 32, (0, 0x0000FFFF), (10, 0x12348000), (64, 0x1234))
CASES += case("rt_i32_16s", [32, 32], 32, (0, 0x00008000), (10, 0x12347FFF), (64, 0xFFFF))
# i64 round-trips.
CASES += case("rt_i64", [32, 64], 64,
              (0, 0x0123456789ABCDEF), (16, 0xFFFFFFFFFFFFFFFF), (128, 1))
CASES += case("rt_i64_8u", [32, 64], 64, (0, 0xFF), (9, 0x80))
CASES += case("rt_i64_8s", [32, 64], 64, (0, 0x80), (9, 0x7F))
CASES += case("rt_i64_16u", [32, 64], 64, (0, 0xFFFF), (18, 0x8000))
CASES += case("rt_i64_16s", [32, 64], 64, (0, 0x8000), (18, 0x7FFF))
CASES += case("rt_i64_32u", [32, 64], 64, (0, 0xFFFFFFFF), (36, 0x80000000))
CASES += case("rt_i64_32s", [32, 64], 64, (0, 0x80000000), (36, 0x7FFFFFFF))


def sx(v, bits):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def wasmtime_all():
    """Run the WHOLE module once per (fn,args) with a fresh instance; also run
    the wr/rd cross-function pair against ONE shared instance."""
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))

    def run(fn, args):
        store = wasmtime.Store(engine)
        exports = wasmtime.Instance(store, module, []).exports(store)
        return exports[fn](store, *args)

    def run_wr_rd(value):
        store = wasmtime.Store(engine)
        exports = wasmtime.Instance(store, module, []).exports(store)
        exports["wr"](store, value)
        return exports["rd"](store)

    return run, run_wr_rd


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


def call(mu, code_base, faddr, pw, rw, args):
    off = faddr - code_base
    mu.reg_write(UC_ARM64_REG_SP, STK)
    mu.reg_write(UC_ARM64_REG_LR, RET)
    mu.reg_write(UC_ARM64_REG_X28, LINMEM)  # the linear-memory base convention
    # AAPCS64: each integer/i64 arg in x0,x1,... (low 32 bits = the w view).
    argregs = [UC_ARM64_REG_X0, UC_ARM64_REG_X1]
    for reg, w, v in zip(argregs, pw, args):
        mask = M32 if w == 32 else M64
        mu.reg_write(reg, v & mask)
    try:
        mu.emu_start(CODE + off, RET, count=4000)
    except UcError as e:
        return f"ERR:{e}"
    if rw == 32:
        return sx(mu.reg_read(UC_ARM64_REG_W0) & M32, 32)
    return sx(mu.reg_read(UC_ARM64_REG_X0) & M64, 64)


def main():
    out, err = compile_aarch64("/tmp/aarch64_mem_851.o")
    if err:
        print("RED (expected before the #851 lowering):", err)
        sys.exit(1)
    code, base, syms = load_elf(out)
    wt_run, wt_wr_rd = wasmtime_all()

    fails, total = 0, 0
    for fn, pw, rw, args in CASES:
        total += 1
        if fn not in syms:
            print(f"BUG {fn}: symbol missing (op declined?)")
            fails += 1
            continue
        # wasmtime args in native signedness.
        wargs = [sx(a, w) for w, a in zip(pw, args)]
        exp = wt_run(fn, wargs)
        mu = new_uc(code)  # fresh memory per case
        got = call(mu, base, syms[fn], pw, rw, args)
        m = M32 if rw == 32 else M64
        ok = isinstance(got, int) and (got & m) == (exp & m)
        if not ok:
            fails += 1
            print(f"BUG {fn}{tuple(hex(a) for a in args)} A64={got} wasmtime={exp}")

    # Cross-function shared-base check: wr then rd on ONE unicorn instance
    # (persistent linear memory) must match wasmtime's wr;rd on one store.
    for value in (0x11223344, 0x80000000, 0):
        total += 1
        if "wr" not in syms or "rd" not in syms:
            print("BUG wr/rd: symbol missing")
            fails += 1
            continue
        mu = new_uc(code)
        call(mu, base, syms["wr"], [32], 0, [value])
        got = call(mu, base, syms["rd"], [], 32, [])
        exp = wt_wr_rd(sx(value, 32))
        if (got & M32) != (exp & M32):
            fails += 1
            print(f"BUG wr/rd({hex(value)}) A64={got} wasmtime={exp}")

    print(f"\n{total - fails}/{total} memory cases matched wasmtime")
    print("RESULT:", "PASS — aarch64 #851 load/store matches wasmtime (in-bounds)"
          if not fails else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
