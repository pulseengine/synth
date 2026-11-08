#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 1666
"""MEMKFLOAT (#1673) — `f32.load`, `f32.store`, `f64.load` and `f64.store` on
a NON-DEFAULT memory k, on ARM `--relocatable`, executed against wasmtime.

WHY. #1622 lowered the i32/i64 integer access families on memory k and #1619
guarded them under `--safety-bounds software` against memory k's OWN size. The
four float accesses still declined as a function-level skip: RED at 617e440b,
every float function in this oracle is skipped (the object holds none of them),
so every leg below fails at compile.

THE LOWERING (memory 0's own shape, #708/#719/#369): the proven integer WORD
access on the integer family's `__synth_wasm_data_<k> + offset + addr` base,
bit-cast with `VMOV` — never VLDR/VSTR, which would alignment-fault on an
unaligned address on silicon (unicorn does not model that fault, so the
unaligned rows here cannot catch it; it is avoided by construction). f64 is
the #1622 `I64Ldr`/`I64Str` pair. Under `software` ONE guard checks the WHOLE
width (4 or 8) against `__synth_mem_size_k` BEFORE any word moves, so an
out-of-bounds store traps having written NOTHING (#1642's lesson).

WHAT IS COMPARED, after every call:
  * the result, BIT-EXACT — NaN payloads included. wasmtime-py marshals an
    f32 through a Python double, which may quiet an sNaN, so wasmtime is
    always driven through BIT-CARRYING twins (i32/i64 in, reinterpret, store;
    load, reinterpret, i32/i64 out). The float-ABI functions are run on
    unicorn with S0/D0 written and read as raw bits and compared with their
    twin's bits. The sNaN rows assert that wasmtime's own bits still have the
    quiet bit CLEAR — otherwise the row would prove nothing;
  * ALL THREE memories' full images against wasmtime, and a CANARY band past
    each memory's end, so a write past memory k's end is SEEN;
  * a trap counts only when the emulator stops on the guard's `UDF #0`
    (0xDE00); any other stop is a BUG;
  * the AAPCS(-VFP) callee-saved state: R4-R11, SP and S16-S31.

THE MEMORIES have three different sizes — memory 0 = 64 KiB, memory 1 = 5,376
B `(pagesize 1)` (not a power of two), memory 2 = 128 KiB — and rows sit
between the sizes in both directions, so a guard reading R10 (memory 0's size)
instead of `__synth_mem_size_k` is red both ways.

LEGS: {cortex-m4f, cortex-m7dp} x {software, none} x {plain, npa}.
  cortex-m4f has a SINGLE-precision FPU, so it runs the f32 functions only; its
  f64 functions must DECLINE with exactly the text their memory-0 twin
  declines with (cortex-m7 too, and cortex-m3 for the f32 ones — no FPU).
  Under `none` (the documented default envelope: no OOB trap) only in-bounds
  rows run. Under `--safety-bounds mask` every memory-k float function must
  still LOUD-SKIP (mask needs a power-of-two size; CLAUDE.md's multi-memory
  paragraph).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/memk_float_1673_differential.py
Exits nonzero on any mismatch, canary write, non-UDF fault, ABI violation,
decline-parity break, compile failure or vacuity.
"""

import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.unicorn_const import UC_ERR_INSN_INVALID
from unicorn import arm_const as A

SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
R_ARM_ABS32 = 2
R_ARM_THM_CALL = 10
BASES = {".text": 0x0010_0000, ".bss": 0x0040_0000, ".data": 0x0080_0000,
         ".synth.wasm_mem_1": 0x0100_0000, ".synth.wasm_mem_2": 0x0180_0000}
GLOBALS_BASE = 0x0300_0000
STACK_BASE, STACK_SIZE = 0x0200_0000, 0x1_0000
GARBAGE = 0xDEADBEEF
CANARY, CANARY_LEN = 0x5A, 0x2000
S0, S1, S2 = 0x10000, 5376, 0x20000
FRAME_CANARY = 0xC0FFEE00

MEMS = (f'(memory $m0 1 1) (memory $m1 {S1} {S1} (pagesize 1)) '
        f'(memory $m2 2 2)')

# name -> (wat body, params, result, wasmtime twin). Float-ABI functions are
# executed on wasmtime through their bit-carrying twin (same positions, i32/i64
# in place of f32/f64).
F32 = {
    "lf32b": ("(param i32) (result i32) (i32.reinterpret_f32 (f32.load $m1 (local.get 0)))",
              ["i32"], "i32", None),
    "sf32b": ("(param i32 i32) (f32.store $m1 (local.get 0) (f32.reinterpret_i32 (local.get 1)))",
              ["i32", "i32"], None, None),
    "lf32o": ("(param i32) (result i32) (i32.reinterpret_f32 (f32.load $m1 offset=4 (local.get 0)))",
              ["i32"], "i32", None),
    "sf32o": ("(param i32 i32) (f32.store $m1 offset=4 (local.get 0) (f32.reinterpret_i32 (local.get 1)))",
              ["i32", "i32"], None, None),
    "lf32b2": ("(param i32) (result i32) (i32.reinterpret_f32 (f32.load $m2 (local.get 0)))",
               ["i32"], "i32", None),
    "sf32b2": ("(param i32 i32) (f32.store $m2 (local.get 0) (f32.reinterpret_i32 (local.get 1)))",
               ["i32", "i32"], None, None),
    "lf32big": ("(param i32) (result i32) (i32.reinterpret_f32 (f32.load $m2 offset=0x10000 (local.get 0)))",
                ["i32"], "i32", None),
    "lf32": ("(param i32) (result f32) (f32.load $m1 (local.get 0))", ["i32"], "f32", "lf32b"),
    "sf32": ("(param i32 f32) (f32.store $m1 (local.get 0) (local.get 1))",
             ["i32", "f32"], None, "sf32b"),
    "cp32": ("(param i32 i32) (f32.store $m1 (local.get 0) (f32.load $m1 (local.get 1)))",
             ["i32", "i32"], None, None),
    "cp32_21": ("(param i32 i32) (f32.store $m2 (local.get 0) (f32.load $m1 (local.get 1)))",
                ["i32", "i32"], None, None),
    "x01_32": ("(param i32 i32) (f32.store $m1 (local.get 0) (f32.load $m0 (local.get 1)))",
               ["i32", "n"], None, None),
    "x10_32": ("(param i32 i32) (f32.store $m0 (local.get 0) (f32.load $m1 (local.get 1)))",
               ["n", "i32"], None, None),
    # an f32 carried through a local
    "loc32": ("(param i32 i32) (local f32) (local.set 2 (f32.load $m1 (local.get 1))) "
              "(f32.store $m1 (local.get 0) (local.get 2))", ["i32", "i32"], None, None),
    # an f32 LIVE ACROSS an internal call whose callee clobbers S0/S1 (the
    # VFP call-spill area must be reserved for a memory-k float function)
    "call32": ("(param i32 i32) local.get 0 local.get 1 f32.load $m1 "
               "i32.const 7 call $clob drop f32.store $m1", ["i32", "i32"], None, None),
    # four live loads stored back reversed (register pressure on both files)
    "rev4": ("(param i32 i32) (local f32 f32 f32 f32) "
             "(local.set 2 (f32.load $m1 (local.get 1))) "
             "(local.set 3 (f32.load $m1 offset=4 (local.get 1))) "
             "(local.set 4 (f32.load $m1 offset=8 (local.get 1))) "
             "(local.set 5 (f32.load $m1 offset=12 (local.get 1))) "
             "(f32.store $m1 (local.get 0) (local.get 5)) "
             "(f32.store $m1 offset=4 (local.get 0) (local.get 4)) "
             "(f32.store $m1 offset=8 (local.get 0) (local.get 3)) "
             "(f32.store $m1 offset=12 (local.get 0) (local.get 2))", ["i32", "i32"], None, None),
}
F64 = {
    "lf64b": ("(param i32) (result i64) (i64.reinterpret_f64 (f64.load $m1 (local.get 0)))",
              ["i32"], "i64", None),
    "sf64b": ("(param i32 i64) (f64.store $m1 (local.get 0) (f64.reinterpret_i64 (local.get 1)))",
              ["i32", "i64"], None, None),
    "lf64o": ("(param i32) (result i64) (i64.reinterpret_f64 (f64.load $m1 offset=4 (local.get 0)))",
              ["i32"], "i64", None),
    "sf64o": ("(param i32 i64) (f64.store $m1 offset=4 (local.get 0) (f64.reinterpret_i64 (local.get 1)))",
              ["i32", "i64"], None, None),
    "lf64b2": ("(param i32) (result i64) (i64.reinterpret_f64 (f64.load $m2 (local.get 0)))",
               ["i32"], "i64", None),
    "sf64b2": ("(param i32 i64) (f64.store $m2 (local.get 0) (f64.reinterpret_i64 (local.get 1)))",
               ["i32", "i64"], None, None),
    "lf64big": ("(param i32) (result i64) (i64.reinterpret_f64 (f64.load $m2 offset=0x10000 (local.get 0)))",
                ["i32"], "i64", None),
    "lf64": ("(param i32) (result f64) (f64.load $m1 (local.get 0))", ["i32"], "f64", "lf64b"),
    "sf64": ("(param i32 f64) (f64.store $m1 (local.get 0) (local.get 1))",
             ["i32", "f64"], None, "sf64b"),
    "cp64": ("(param i32 i32) (f64.store $m1 (local.get 0) (f64.load $m1 (local.get 1)))",
             ["i32", "i32"], None, None),
    "x10_64": ("(param i32 i32) (f64.store $m0 (local.get 0) (f64.load $m1 (local.get 1)))",
               ["n", "i32"], None, None),
    "x01_64": ("(param i32 i32) (f64.store $m1 (local.get 0) (f64.load $m0 (local.get 1)))",
               ["i32", "n"], None, None),
    "call64": ("(param i32 i32) local.get 0 local.get 1 f64.load $m1 "
               "i32.const 7 call $clob drop f64.store $m1", ["i32", "i32"], None, None),
    "rev3d": ("(param i32 i32) (local f64 f64 f64) "
              "(local.set 2 (f64.load $m1 (local.get 1))) "
              "(local.set 3 (f64.load $m1 offset=8 (local.get 1))) "
              "(local.set 4 (f64.load $m1 offset=16 (local.get 1))) "
              "(f64.store $m1 (local.get 0) (local.get 4)) "
              "(f64.store $m1 offset=8 (local.get 0) (local.get 3)) "
              "(f64.store $m1 offset=16 (local.get 0) (local.get 2))", ["i32", "i32"], None, None),
}
# Internal callee: clobbers the low S registers with real f32 arithmetic.
CLOB = ("(func $clob (param i32) (result i32) (i32.reinterpret_f32 (f32.add "
        "(f32.convert_i32_s (local.get 0)) (f32.const 1.5))))")


def module(funcs):
    body = "\n".join(f'  (func (export "{n}") {w})' for n, (w, *_r) in funcs.items())
    return f"(module {MEMS}\n  {CLOB}\n{body})"


SNAN32 = 0x7FA0_0001          # f32 signalling NaN (quiet bit 22 clear)
SNAN32N = 0xFF80_1234         # negative f32 sNaN
QNAN32 = 0xFFC1_2345          # negative f32 quiet NaN, payload
SNAN64 = 0x7FF0_0000_0000_0001   # f64 signalling NaN (quiet bit 51 clear)
SNAN64B = 0xFFF0_DEAD_BEEF_0001
QNAN64 = 0x7FF8_0000_CAFE_F00D
V32 = [0x3F80_0000, 0xC2F6_E979, 0x0000_0001, 0x8000_0000, SNAN32, SNAN32N,
       QNAN32, 0x7F80_0000]
V64 = [0x3FF0_0000_0000_0000, 0xC05E_DD2F_1A9F_BE77, 0x0000_0000_0000_0001,
       SNAN64, SNAN64B, QNAN64, 0x8000_0000_0000_0000]
SNAN_ROWS = {SNAN32: 32, SNAN32N: 32, SNAN64: 64, SNAN64B: 64}

T = "trap"


def rows32():
    r = []
    # seeds + round trips at aligned and UNALIGNED addresses, every bit pattern
    for i, v in enumerate(V32):
        for a in (0x100 + 8 * i, 0x301 + 8 * i, 0x402 + 8 * i, 0x503 + 8 * i):
            r.append(("sf32b", [a, v], 1))
            r.append(("lf32b", [a], 1))
            r.append(("lf32", [a], 1))
    for i, v in enumerate(V32):
        r.append(("sf32", [0x600 + 4 * i, v], 1))     # float-ABI store, S0 bits
        r.append(("lf32b", [0x600 + 4 * i], 1))
    r += [
        ("cp32", [0x700, 0x100 + 8 * V32.index(SNAN32)], 1),   # sNaN mem->mem
        ("cp32", [0x705, 0x301 + 8 * V32.index(SNAN32N)], 1),  # unaligned both
        ("lf32b", [0x700], 1), ("lf32b", [0x705], 1),
        ("cp32_21", [0x8000, 0x402 + 8 * V32.index(QNAN32)], 1),
        ("lf32b2", [0x8000], 1),
        ("loc32", [0x720, 0x100 + 8 * V32.index(SNAN32)], 1),
        ("call32", [0x730, 0x100 + 8 * V32.index(SNAN32N)], 1),
        ("rev4", [0x740, 0x600], 1),
        ("rev4", [0x781, 0x100], 1),
        ("x01_32", [0x790, "n:0x40"], 1),
        ("x10_32", ["n:0x80", 0x100 + 8 * V32.index(SNAN32)], 1),
        # memory 1's boundary (S1 = 5376, not a power of two)
        ("sf32b", [S1 - 4, 0x4049_0FDB], 1),           # ends exactly at the size
        ("lf32b", [S1 - 4], 1), ("lf32", [S1 - 4], 1),
        ("sf32b", [S1 - 3, SNAN32], 0),                # straddles: writes NOTHING
        ("sf32b", [S1 - 1, 0x1234_5678], 0),
        ("sf32b", [S1, 0x2345_6789], 0),
        ("sf32b", [0x2000, 0x3456_789A], 0),           # past memory 1, inside S0
        ("sf32b", [0xFFFF_FFFC, 0x4567_89AB], 0),      # addr+4 wraps u32
        ("sf32", [S1 - 2, SNAN32N], 0),
        ("sf32o", [S1 - 8, 0x5555_AAAA], 1),           # offset=4, end-exact
        ("lf32o", [S1 - 8], 1),
        ("sf32o", [S1 - 7, 0x6666_BBBB], 0),
        ("lf32b", [S1 - 3], 0), ("lf32b", [S1], 0), ("lf32b", [0x2000], 0),
        ("lf32", [S1 - 2], 0), ("lf32o", [S1 - 7], 0),
        ("lf32b", [0xFFFF_FFFD], 0),
        ("cp32", [S1 - 2, 0x100], 0),                  # store side OOB
        ("cp32", [0x100, S1 - 2], 0),                  # load side OOB
        ("x01_32", [S1 - 1, "n:0x40"], 0),
        ("x01_32", [0x7A0, f"n:{S0 - 2:#x}"], 0),      # memory-0 side OOB
        ("x10_32", [f"n:{S0 - 3:#x}", 0x100], 0),
        ("call32", [S1 - 3, 0x100], 0),
        # memory 2 (128 KiB): rows past memory 0 AND memory 1 are IN bounds
        ("sf32b2", [0x18000, SNAN32], 1), ("lf32b2", [0x18000], 1),
        ("sf32b2", [S2 - 4, 0x7777_CCCC], 1), ("lf32b2", [S2 - 4], 1),
        ("sf32b2", [S2 - 3, 0x8888_DDDD], 0), ("lf32b2", [S2 - 3], 0),
        ("lf32big", [S2 - 0x10000 - 4], 1),
        ("lf32big", [S2 - 0x10000 - 3], 0),
        ("lf32big", [0xFFFF_0000], 0),
    ]
    return r


def rows64():
    r = []
    for i, v in enumerate(V64):
        for a in (0x900 + 16 * i, 0xA01 + 16 * i, 0xB04 + 16 * i, 0xC07 + 16 * i):
            r.append(("sf64b", [a, v], 1))
            r.append(("lf64b", [a], 1))
            r.append(("lf64", [a], 1))
    for i, v in enumerate(V64):
        r.append(("sf64", [0xD00 + 8 * i, v], 1))
        r.append(("lf64b", [0xD00 + 8 * i], 1))
    r += [
        ("cp64", [0xE00, 0x900 + 16 * V64.index(SNAN64)], 1),
        ("cp64", [0xE09, 0xA01 + 16 * V64.index(SNAN64B)], 1),
        ("lf64b", [0xE00], 1), ("lf64b", [0xE09], 1),
        ("call64", [0xE20, 0x900 + 16 * V64.index(SNAN64)], 1),
        ("rev3d", [0xE40, 0xD00], 1),
        ("rev3d", [0xE73, 0x900], 1),
        ("x01_64", [0xEA0, "n:0x48"], 1),
        ("x10_64", ["n:0x88", 0x900 + 16 * V64.index(SNAN64B)], 1),
        ("sf64b", [S1 - 8, 0x4009_21FB_5444_2D18], 1),   # end-exact
        ("lf64b", [S1 - 8], 1), ("lf64", [S1 - 8], 1),
        ("sf64b", [S1 - 7, SNAN64], 0),                  # straddle: NOTHING written
        ("sf64b", [S1 - 4, 0x1111_2222_3333_4444], 0),   # low word fits, high not
        ("sf64b", [S1 - 1, 0x5555_6666_7777_8888], 0),
        ("sf64b", [S1, 0x0102_0304_0506_0708], 0),
        ("sf64b", [0x2000, 0x99AA_BBCC_DDEE_FF00], 0),   # past memory 1, inside S0
        ("sf64b", [0xFFFF_FFF8, 0x1357_9BDF_2468_ACE0], 0),
        ("sf64", [S1 - 4, SNAN64B], 0),
        ("sf64o", [S1 - 12, 0x0BAD_F00D_DEAD_BEEF], 1),  # offset=4, end-exact
        ("lf64o", [S1 - 12], 1),
        ("sf64o", [S1 - 11, 0x0BAD_F00D_DEAD_BEEE], 0),
        ("sf64o", [S1 - 8, 0x0BAD_F00D_DEAD_BEED], 0),
        ("lf64b", [S1 - 7], 0), ("lf64b", [S1 - 4], 0), ("lf64b", [0x2000], 0),
        ("lf64", [S1 - 1], 0), ("lf64o", [S1 - 11], 0),
        ("cp64", [S1 - 4, 0x900], 0),
        ("cp64", [0x900, S1 - 4], 0),
        ("x10_64", [f"n:{S0 - 4:#x}", 0x900], 0),
        ("x01_64", [0xEB0, f"n:{S0 - 4:#x}"], 0),
        ("call64", [S1 - 5, 0x900], 0),
        ("sf64b2", [0x18000, SNAN64], 1), ("lf64b2", [0x18000], 1),
        ("sf64b2", [S2 - 8, QNAN64], 1), ("lf64b2", [S2 - 8], 1),
        ("sf64b2", [S2 - 7, 0x1], 0), ("sf64b2", [S2 - 4, 0x2], 0),
        ("lf64b2", [S2 - 7], 0),
        ("lf64big", [S2 - 0x10000 - 8], 1),
        ("lf64big", [S2 - 0x10000 - 7], 0),
        ("lf64big", [0xFFFF_0000], 0),
    ]
    return r


TARGETS = {
    # target: (funcs, rows)
    "cortex-m4f": ({**F32}, rows32()),
    "cortex-m7dp": ({**F32, **F64}, rows32() + rows64()),
}
MODES = {
    "software": (["--safety-bounds", "software"], True),
    "none": ([], False),
}
ABIS = {
    "plain": ["--embedder-data-init", "--embedder-global-init"],
    "npa": ["--native-pointer-abi"],
}
MASK_REFUSAL = "--safety-bounds mask is not lowered for an op on memory"


def compile_obj(wat, tmp, label, target, flags):
    src = tmp / f"{label}.wat"
    src.write_text(wat)
    obj = tmp / f"{label}.o"
    if obj.exists():
        obj.unlink()
    r = subprocess.run(
        [SYNTH, "compile", str(src), "-o", str(obj), "--target", target,
         "--all-exports", "--relocatable", *flags],
        capture_output=True, text=True, env={"PATH": "/usr/bin:/bin"})
    return r.returncode, (r.stdout or "") + (r.stderr or ""), obj


def thm_bl(src, dst):
    off = dst - (src + 4)
    imm = (off >> 1) & 0xFFFFFF
    s, i1, i2 = (imm >> 23) & 1, (imm >> 22) & 1, (imm >> 21) & 1
    j1, j2 = (~(i1 ^ s)) & 1, (~(i2 ^ s)) & 1
    return struct.pack("<HH", 0xF000 | (s << 10) | ((imm >> 11) & 0x3FF),
                       0xD000 | (j1 << 13) | (j2 << 11) | (imm & 0x7FF))


def rup(n):
    return max(0x1000, (n + 0xFFF) & ~0xFFF)


CORE = [A.UC_ARM_REG_R0, A.UC_ARM_REG_R1, A.UC_ARM_REG_R2, A.UC_ARM_REG_R3]
CALLEE = [A.UC_ARM_REG_R4, A.UC_ARM_REG_R5, A.UC_ARM_REG_R6, A.UC_ARM_REG_R7,
          A.UC_ARM_REG_R8, A.UC_ARM_REG_R9, A.UC_ARM_REG_R10, A.UC_ARM_REG_R11]
SREG = [A.UC_ARM_REG_S0 + i for i in range(32)]
DREG = [A.UC_ARM_REG_D0 + i for i in range(8)]


class Linked:
    def __init__(self, obj, npa):
        self.npa = npa
        e = ELFFile(open(obj, "rb"))
        secs = list(e.iter_sections())
        self.sizes, blobs = {}, {}
        for s in secs:
            if s.name in BASES:
                self.sizes[s.name] = s["sh_size"]
                blobs[s.name] = b"" if s["sh_type"] == "SHT_NOBITS" else bytes(s.data())
        symtab = [s for s in secs if s["sh_type"] == "SHT_SYMTAB"][0]
        self.syms, self.abs = {}, {}
        for s in symtab.iter_symbols():
            if not s.name:
                continue
            if s["st_shndx"] == "SHN_ABS":
                self.abs[s.name] = s["st_value"]
            elif s["st_shndx"] != "SHN_UNDEF":
                sec = secs[s["st_shndx"]].name
                if sec in BASES:
                    self.syms[s.name] = (sec, s["st_value"])
        self.msize = [self.abs[f"__synth_mem_size_{k}"] for k in range(3)]
        if not npa or ".bss" not in self.sizes:
            self.sizes[".bss"] = self.msize[0]
            blobs[".bss"] = b""
            self.syms["__synth_wasm_data"] = (".bss", 0)
        text = bytearray(blobs[".text"])
        self.size_relocs = 0
        rel = e.get_section_by_name(".rel.text")
        for r in (rel.iter_relocations() if rel else []):
            sym = symtab.get_symbol(r["r_info_sym"])
            if sym["st_shndx"] == "SHN_ABS":
                dst = sym["st_value"]
                self.size_relocs += sym.name.startswith("__synth_mem_size_")
            elif sym.name in self.syms:
                dst = self.addr(sym.name)
            else:
                sys.exit(f"unresolvable reloc target {sym.name!r}")
            if r["r_info_type"] == R_ARM_ABS32:
                (add,) = struct.unpack_from("<I", text, r["r_offset"])
                struct.pack_into("<I", text, r["r_offset"], (dst + add) & 0xFFFFFFFF)
            elif r["r_info_type"] == R_ARM_THM_CALL:
                text[r["r_offset"]:r["r_offset"] + 4] = thm_bl(
                    BASES[".text"] + r["r_offset"], dst & ~1)
            else:
                sys.exit(f"unhandled reloc type {r['r_info_type']} for {sym.name}")
        self.text = bytes(text)
        self.mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        try:
            self.mu.ctl_set_cpu_model(A.UC_CPU_ARM_MAX)
        except AttributeError:
            pass
        for name, base in BASES.items():
            self.mu.mem_map(base, rup(self.sizes.get(name, 0) + CANARY_LEN + 0x20))
        self.mu.mem_map(STACK_BASE, STACK_SIZE)
        self.mu.mem_map(GLOBALS_BASE, 0x1000)
        self.ret = BASES[".text"] + rup(len(text) + CANARY_LEN + 0x20) - 0x10
        self.mu.mem_write(BASES[".text"], self.text)
        self.mu.mem_write(self.ret, b"\x00\xbf\x00\xbf")
        for name, blob in blobs.items():
            if blob and name != ".text":
                self.mu.mem_write(BASES[name], blob)
        for k in (0, 1, 2):
            self.mu.mem_write(self.mem_end(k), bytes([CANARY]) * CANARY_LEN)
        self.mu.reg_write(A.UC_ARM_REG_C1_C0_2, 0x00F00000)  # CPACR: CP10/11
        self.mu.reg_write(A.UC_ARM_REG_FPEXC, 0x40000000)    # FPEXC.EN

    def addr(self, name):
        sec, val = self.syms[name]
        return BASES[sec] + val

    def mem_base(self, k):
        return self.addr("__synth_wasm_data") if k == 0 else BASES[f".synth.wasm_mem_{k}"]

    def mem_end(self, k):
        if k == 0:
            return BASES[".bss"] + self.sizes[".bss"]
        return BASES[f".synth.wasm_mem_{k}"] + self.sizes[f".synth.wasm_mem_{k}"]

    def canary_ok(self, k):
        return bytes(self.mu.mem_read(self.mem_end(k), CANARY_LEN)) == bytes([CANARY]) * CANARY_LEN

    def image(self, k):
        return bytes(self.mu.mem_read(self.mem_base(k), self.msize[k]))

    def call(self, fn, kinds, rkind, args):
        """Run `fn`; return (outcome, abi_violations)."""
        for i, r in enumerate(CORE):
            self.mu.reg_write(r, GARBAGE ^ i)
        for i in range(32):
            self.mu.reg_write(SREG[i], (0x5EED_0000 | i) ^ (i << 20))
        callee0 = [GARBAGE ^ (0x100 * i) for i in range(5)] + [
            GLOBALS_BASE, self.msize[0], 0 if self.npa else BASES[".bss"]]
        for r, v in zip(CALLEE, callee0):
            self.mu.reg_write(r, v)
        ncrn = nsrn = 0
        for kind, a in zip(kinds, args):
            if isinstance(a, str):  # "n:0x.." — a memory-0 offset, native under npa
                a = int(a[2:], 16) + (self.addr("__synth_wasm_data") if self.npa else 0)
            if kind in ("i32", "n"):
                self.mu.reg_write(CORE[ncrn], a & 0xFFFFFFFF)
                ncrn += 1
            elif kind == "i64":  # even pair (#518)
                ncrn += ncrn & 1
                self.mu.reg_write(CORE[ncrn], a & 0xFFFFFFFF)
                self.mu.reg_write(CORE[ncrn + 1], a >> 32)
                ncrn += 2
            elif kind == "f32":
                self.mu.reg_write(SREG[nsrn], a)
                nsrn += 1
            else:  # f64
                d = (nsrn + 1) // 2
                self.mu.reg_write(DREG[d], a)
                nsrn = 2 * d + 2
        self.mu.reg_write(A.UC_ARM_REG_R12, GARBAGE)
        sp0 = STACK_BASE + STACK_SIZE - 0x100
        self.mu.mem_write(sp0, struct.pack("<4I", *(FRAME_CANARY + i for i in range(4))))
        self.mu.reg_write(A.UC_ARM_REG_SP, sp0)
        self.mu.reg_write(A.UC_ARM_REG_LR, self.ret | 1)
        hi_s = [self.mu.reg_read(SREG[i]) for i in range(16, 32)]
        try:
            self.mu.emu_start(self.addr(fn) | 1, self.ret, timeout=20_000_000)
        except UcError as ex:
            pc = self.mu.reg_read(A.UC_ARM_REG_PC)
            off = (pc & ~1) - BASES[".text"]
            hw = struct.unpack_from("<H", self.text, off)[0] if 0 <= off < len(self.text) - 1 else None
            if ex.errno == UC_ERR_INSN_INVALID and hw == 0xDE00:
                return T, []
            return f"FAULT {ex} @pc={pc:#x}", []
        bad = [f"R{4 + i}" for i, (r, v) in enumerate(zip(CALLEE, callee0))
               if self.mu.reg_read(r) != v]
        if self.mu.reg_read(A.UC_ARM_REG_SP) != sp0:
            bad.append("SP")
        if bytes(self.mu.mem_read(sp0, 16)) != struct.pack("<4I", *(FRAME_CANARY + i for i in range(4))):
            bad.append("caller-frame")
        bad += [f"S{16 + i}" for i in range(16) if self.mu.reg_read(SREG[16 + i]) != hi_s[i]]
        if rkind is None:
            return "ret", bad
        if rkind == "i32":
            v = self.mu.reg_read(A.UC_ARM_REG_R0)
        elif rkind == "i64":
            v = self.mu.reg_read(A.UC_ARM_REG_R0) | self.mu.reg_read(A.UC_ARM_REG_R1) << 32
        elif rkind == "f32":
            v = self.mu.reg_read(SREG[0])
        else:
            v = self.mu.reg_read(DREG[0])
        return f"ret {v:#x}", bad


def wasmtime_instance(wat):
    wat_x = wat
    for k in range(3):
        wat_x = wat_x.replace(f"(memory $m{k} ", f"(memory $m{k} (export \"m{k}\") ", 1)
    cfg = wasmtime.Config()
    cfg.wasm_multi_memory = True
    cfg.wasm_custom_page_sizes = True
    eng = wasmtime.Engine(cfg)
    st = wasmtime.Store(eng)
    ex = wasmtime.Instance(st, wasmtime.Module(eng, wat_x), []).exports(st)
    return st, ex, [ex[f"m{k}"] for k in range(3)]


def to_signed(v, bits):
    return v - (1 << bits) if v >> (bits - 1) else v


def run_leg(name, target, flags, funcs, rows, assert_oob, tmp):
    label = name.replace("/", "_")
    wat = module(funcs)
    rc, log, obj = compile_obj(wat, tmp, label, target, flags)
    want = len([r for r in rows if r[2] or assert_oob])
    if rc != 0 or not obj.exists():
        tail = [ln for ln in log.splitlines() if "rror" in ln or "skipping" in ln][:2]
        print(f"[RED] {name}: compile rc={rc}: {' | '.join(tail)[:400]}")
        return 0, want
    npa = "--native-pointer-abi" in flags
    ln = Linked(obj, npa)
    missing = [f for f in funcs if f not in ln.syms]
    if missing:
        print(f"[RED] {name}: functions missing from the object: {missing}")
        return 0, want
    if "software" in flags and ln.size_relocs == 0:
        print(f"[RED] {name}: no R_ARM_ABS32 against __synth_mem_size_k — the "
              "memory-k guard is absent")
        return 0, want
    st, ex, wm = wasmtime_instance(wat)
    if [w.data_len(st) for w in wm] != ln.msize:
        print(f"[RED] {name}: size symbols {ln.msize} != wasmtime "
              f"{[w.data_len(st) for w in wm]}")
        return 0, want
    compared = fails = 0
    for fn, args, inb in rows:
        if not inb and not assert_oob:
            continue
        _w, kinds, rkind, twin = funcs[fn]
        wfn = twin or fn
        wkinds = [{"f32": "i32", "f64": "i64", "n": "i32"}.get(k, k) for k in kinds]
        wargs = []
        for k, a in zip(wkinds, args):
            a = int(a[2:], 16) if isinstance(a, str) else a
            wargs.append(to_signed(a, 64 if k == "i64" else 32))
        try:
            res = ex[wfn](st, *wargs)
            bits = 64 if rkind in ("i64", "f64") else 32
            exp = "ret" if res is None else f"ret {res & ((1 << bits) - 1):#x}"
        except wasmtime.Trap:
            exp = T
        if (exp == T) == bool(inb):
            print(f"[RED] {name}: row table wrong — {fn}{tuple(args)} in_bounds={inb} "
                  f"but wasmtime {exp}")
            return compared, fails + 1
        # A NaN row proves bit-exactness only if the REFERENCE kept the sNaN.
        if exp.startswith("ret ") and int(exp[4:], 16) in SNAN_ROWS:
            v, w = int(exp[4:], 16), SNAN_ROWS[int(exp[4:], 16)]
            assert not (v >> (22 if w == 32 else 51)) & 1, "reference quieted an sNaN"
        got, abi = ln.call(fn, kinds, rkind, args)
        same = [ln.image(k) == bytes(wm[k].read(st, 0, ln.msize[k])) for k in range(3)]
        canary = [ln.canary_ok(k) for k in range(3)]
        good = got == exp and all(same) and all(canary) and not abi
        compared += 1
        fails += not good
        if not good or os.environ.get("MEMKF_VERBOSE") == "1":
            note = "" if good else ("  <-- " + ("" if got == exp else "RESULT ")
                                    + " ".join(f"MEM{k}" for k in range(3) if not same[k]) + " "
                                    + " ".join(f"PAST-END{k}" for k in range(3) if not canary[k])
                                    + (f" ABI{abi}" if abi else ""))
            print(f"  [{'ok ' if good else 'BUG'}] {name}.{fn}{tuple(args)} -> {got} "
                  f"(wasmtime {exp}){note}")
        if not good:
            for k in range(3):  # resync: a divergent write would poison later rows
                ln.mu.mem_write(ln.mem_base(k), bytes(wm[k].read(st, 0, ln.msize[k])))
                ln.mu.mem_write(ln.mem_end(k), bytes([CANARY]) * CANARY_LEN)
    traps = sum(1 for r in rows if not r[2]) if assert_oob else 0
    print(f"  {name}: {compared} calls compared ({traps} trap rows), {fails} failed")
    return compared, fails


def decline_text(log, fn):
    for line in log.splitlines():
        if f"skipping function '{fn}'" in line:
            return line.split("failed:", 1)[-1].strip()
    return None


def decline_parity(tmp):
    """Where memory 0's float access declines (no FPU / single precision), the
    memory-k twin must decline with the SAME text; and under mask every memory-k
    float function must loud-skip."""
    bad = checks = 0
    cases = [("cortex-m4f", F64), ("cortex-m7", F64), ("cortex-m3", F32), ("cortex-m3", F64)]
    for target, funcs in cases:
        wat_k = module(funcs)
        wat_0 = module({n: (re.sub(r"\$m[12]\b", "$m0", w), *rest)
                        for n, (w, *rest) in funcs.items()})
        logs = []
        for tag, wat in (("k", wat_k), ("0", wat_0)):
            rc, log, _ = compile_obj(wat, tmp, f"parity_{target}_{tag}_{len(funcs)}",
                                     target, ["--allow-skipped-exports"])
            logs.append(log)
        for fn in funcs:
            dk, d0 = decline_text(logs[0], fn), decline_text(logs[1], fn)
            ok = dk is not None and dk == d0 and "FPU" in dk
            checks += 1
            bad += not ok
            if not ok:
                print(f"  [BUG] {target} {fn}: memory-k decline {dk!r} != memory-0 {d0!r}")
    for target, funcs in (("cortex-m7dp", {**F32, **F64}), ("cortex-m4f", F32)):
        rc, log, _ = compile_obj(module(funcs), tmp, f"mask_{target}", target,
                                 ["--safety-bounds", "mask", "--allow-skipped-exports"])
        for fn in funcs:
            d = decline_text(log, fn)
            # A cross-memory function may hit memory 0's own mask decline
            # first (f64 under mask, #369); either way it is loud.
            ok = d is not None and (MASK_REFUSAL in d or "mask" in d)
            checks += 1
            bad += not ok
            if not ok:
                print(f"  [BUG] mask {target} {fn}: not loud-skipped ({d!r})")
    print(f"  decline parity + mask loud-skip: {checks} checks, {bad} failed")
    return checks, bad


def main():
    tmp = Path(tempfile.mkdtemp(prefix="memk_float_1673_"))
    total = fails = floor = 0
    for target, (funcs, rows) in TARGETS.items():
        for mode, (mflags, assert_oob) in MODES.items():
            for abi, aflags in ABIS.items():
                name = f"{target}/{mode}/{abi}"
                print(f"=== {name} ===")
                f_leg, r_leg = funcs, rows
                if mode == "software" and abi == "npa":
                    # Memory 0's pointers are NATIVE under npa and memory 0's
                    # own software guard compares them with R10 (the #1619
                    # refusal's reason), so the cross-memory functions'
                    # memory-0 side is not a memory-k question: memory-k only.
                    f_leg = {n: v for n, v in funcs.items() if not n.startswith("x")}
                    r_leg = [r for r in rows if not r[0].startswith("x")]
                floor += len([r for r in r_leg if r[2] or assert_oob])
                c, f = run_leg(name, target, mflags + aflags, f_leg, r_leg, assert_oob, tmp)
                total += c
                fails += f
    print("=== decline parity (memory 0 vs memory k) and mask ===")
    checks, bad = decline_parity(tmp)
    fails += bad
    if total < floor or checks == 0:
        print(f"VACUOUS: compared {total} calls, expected {floor}")
        fails += 1
    print(f"\ncompared: {total} (expected {floor}); decline checks: {checks}")
    print(f"ORACLE: {'PASS' if fails == 0 else f'FAIL ({fails})'}")
    return 0 if fails == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
