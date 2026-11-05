#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 64
"""#1635 — a register-homed param read only after a forward block join is
clobbered by a const-CSE hoist (`movw r0, #0`), so the trailing stores
through it land at linear-memory 0/4 instead of the caller's pointer.

ROOT CAUSE: `liveness::free_reg_over` (the const-CSE extending-alias hoist's
holder search) accepted a candidate register that is neither read nor
redefined before the end of its straight-line segment — "untouched in the
segment" is not "dead": cpetig's sret pointer in r0 is read only after the
forward join that ends the segment. Fixed by requiring a redefinition inside
the segment. Pre-fix: 32 of 64 vectors mismatch (every leg, every vector that
reaches the trailing stores); `SYNTH_CONST_CSE=0` is green on the same
binary, isolating the pass.

Fixture: scripts/repro/r0_clobber_1635.wat — `bump` is the reporter's rustc
output verbatim (export added), `min` the reporter's reduced function. Both
are `(param $out i32) (param $size i32) (param $align i32)` and end with
`local.get 0; ...; i32.store offset=4; local.get 0; ...; i32.store`.

Oracle: each case runs under wasmtime (ground truth) and under unicorn on
the synth-compiled Thumb-2 object, from the SAME initial linear memory (the
`CURSOR` static at 0x100000 seeded per case); the WHOLE linear memory is
compared afterwards. Red = the result written at 0/4 instead of `out`.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/r0_clobber_1635_differential.py
Exits nonzero on any mismatch.
"""

import os
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_MCLASS, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("r0_clobber_1635.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")

PAGES = 17
MEM_SIZE = PAGES * 65536
CURSOR = 0x100000  # the reporter's `static mut CURSOR` (i32.load offset=1048576)
LM_BASE = 0x2000_0000  # unicorn-side linear-memory base (R11)

# (func, out, size, align, cursor) — `out` is never 0 or 4, so a store
# through a clobbered r0 is visible as a write at 0/4 AND a missing write
# at `out`.
CASES = [
    ("bump", 0x200, 16, 8, 0),  # Some(0): the path the reporter hit
    ("bump", 0x200, 24, 4, 0x13),  # Some(0x14) — aligned up
    ("bump", 0x300, 8, 16, 0x1FF0),  # end > 8192 -> None (tag 0)
    ("bump", 0x300, 8, 3, 0),  # align not a power of two -> None
    ("bump", 0x400, 8, 32, 0),  # align > 16 -> None (the early exit)
    ("bump", 0x500, 0xFFFFFFF0, 8, 0x40),  # checked_add overflow -> None
    ("min", 0x200, 16, 8, 0),
    ("min", 0x600, 0, 1, 0),
]

# Reporter's exact command first; the rest scope the defect — every Cortex-M
# profile, the self-contained (optimized) path and --no-optimize all ran the
# hoist and all were red. cortex-r5 (A32) also emits the clobber but is NOT a
# leg: its forward branches execute wrongly for an unrelated reason, so its
# rows could not isolate this defect.
_EMB = ["--relocatable", "--embedder-data-init", "--embedder-global-init"]
VARIANTS = [
    ("m7-reloc", ["--target", "cortex-m7", *_EMB]),
    ("m3-reloc", ["--target", "cortex-m3", *_EMB]),
    ("m4f-reloc", ["--target", "cortex-m4f", *_EMB]),
    ("m7dp-reloc", ["--target", "cortex-m7dp", *_EMB]),
    ("m55-reloc", ["--target", "cortex-m55", *_EMB]),
    ("m7-reloc-noopt", ["--target", "cortex-m7", "--no-optimize", *_EMB]),
    ("m3-self", ["--target", "cortex-m3"]),
    ("m7dp-self", ["--target", "cortex-m7dp"]),
]


def compile_elf(out, extra):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, *extra, "--all-exports"],
        capture_output=True,
        text=True,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed ({extra}): {r.stderr}")


def load(elf):
    with open(elf, "rb") as fh:
        f = ELFFile(fh)
        text = f.get_section_by_name(".text")
        code, base = text.data(), text["sh_addr"]
        syms = {}
        for s in f.iter_sections():
            if s.header.sh_type == "SHT_SYMTAB":
                for sym in s.iter_symbols():
                    if sym.name and sym["st_info"]["type"] == "STT_FUNC":
                        syms[sym.name] = (sym["st_value"] & ~1) - base
    return code, syms


def initial_memory(cursor):
    mem = bytearray(MEM_SIZE)
    mem[CURSOR : CURSOR + 4] = cursor.to_bytes(4, "little")
    return mem


def wasm_run(func, out, size, align, cursor):
    eng = wasmtime.Engine()
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, wasmtime.Module(eng, WAT.read_bytes()), [])
    mem = inst.exports(st)["memory"]
    mem.write(st, bytes(initial_memory(cursor)), 0)
    s32 = [a - 2**32 if a >= 2**31 else a for a in (out, size, align)]
    inst.exports(st)[func](st, *s32)
    return bytes(mem.read(st, 0, MEM_SIZE))


def arm_run(code, off, out, size, align, cursor):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB | UC_MODE_MCLASS)
    mu.mem_map(0, 0x40000)
    mu.mem_write(0x1000, code)
    ret = 0x30000
    mu.mem_write(ret, b"\x00\xbf\x00\xbf")
    mu.mem_map(LM_BASE, MEM_SIZE)
    mu.mem_write(LM_BASE, bytes(initial_memory(cursor)))
    for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2), (out, size, align)):
        mu.reg_write(reg, val & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R11, LM_BASE)
    mu.reg_write(UC_ARM_REG_R10, MEM_SIZE)
    mu.reg_write(UC_ARM_REG_SP, 0x3F000)
    mu.reg_write(UC_ARM_REG_LR, ret | 1)
    try:
        mu.emu_start((0x1000 + off) | 1, ret, timeout=5_000_000, count=100_000)
    except UcError as e:
        return f"UC_ERR:{e}"
    return bytes(mu.mem_read(LM_BASE, MEM_SIZE))


def describe(a, b):
    diffs = [i for i in range(MEM_SIZE) if a[i] != b[i]]
    words = sorted({i & ~3 for i in diffs})[:6]
    return ", ".join(
        f"[{w:#x}] synth={int.from_bytes(a[w:w + 4], 'little'):#x} "
        f"wasmtime={int.from_bytes(b[w:w + 4], 'little'):#x}"
        for w in words
    )


def main():
    fails = runs = 0
    for vname, extra in VARIANTS:
        with tempfile.TemporaryDirectory() as td:
            obj = os.path.join(td, "m.o")
            compile_elf(obj, extra)
            code, syms = load(obj)
            for func, out, size, align, cursor in CASES:
                want = wasm_run(func, out, size, align, cursor)
                if func not in syms:
                    print(f"[{vname}] SYMBOL MISSING: {func}")
                    fails += 1
                    continue
                got = arm_run(code, syms[func], out, size, align, cursor)
                runs += 1
                args = f"{func}(out={out:#x}, size={size:#x}, align={align}, cursor={cursor:#x})"
                if isinstance(got, str):
                    fails += 1
                    print(f"[{vname}] FAIL {args}: {got}")
                elif got != want:
                    fails += 1
                    print(f"[{vname}] FAIL {args}: {describe(got, want)}")
                else:
                    print(f"[{vname}] ok   {args}")
    if fails:
        sys.exit(f"\n#1635 differential: {fails} of {runs} mismatched")
    print(f"\n#1635 differential: all {runs} green")


if __name__ == "__main__":
    main()
