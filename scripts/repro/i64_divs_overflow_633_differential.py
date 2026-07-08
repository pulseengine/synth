# #633: i64.div_s(INT64_MIN, -1) must trap (WASM Core 4.3.2 idiv_s — the
# quotient +2^63 is unrepresentable). The Thumb-2 I64DivS expansion emitted
# only the divide-by-zero guard: it negated the dividend (INT64_MIN wraps to
# itself), negated the divisor (-1 -> 1), ran the unsigned core, and silently
# returned 0x8000000000000000. The i32 signed-div path HAS the overflow guard
# — this pins the i64 mirror (dividend==INT64_MIN && divisor==-1 -> UDF #0,
# emitted on the #610/#613 fixed-ABI wrapper path where the dividend is in
# R0:R1 and the divisor in R2:R3).
#
# Fix-guard twin: i64.rem_s(INT64_MIN, -1) is DEFINED as 0 and must NOT trap
# (irem_s) — vectors below pin that the guard is div_s-only.
#
# Differential: compile each export with the issue's exact config
# (`-t cortex-m3 -n <name> --relocatable`), emulate under unicorn
# (UC_MODE_THUMB), difference against the wasmtime oracle. Trap vectors
# assert BOTH sides trap (unicorn: UDF hit / no return-pad; wasmtime:
# "integer overflow" / "divide by zero").
#
# Usage: python3 i64_divs_overflow_633_differential.py <synth-binary> [wat]
import os
import shutil
import struct
import subprocess
import sys
import tempfile

from elftools.elf.elffile import ELFFile
from unicorn import Uc, UcError, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_PC,
    UC_ARM_REG_SP,
)

SYNTH = sys.argv[1] if len(sys.argv) > 1 else "target/debug/synth"
WAT = (
    sys.argv[2]
    if len(sys.argv) > 2
    else os.path.join(os.path.dirname(__file__), "i64_divs_overflow_633.wat")
)
CODE, STK = 0x1000000, 0x6000000
RET = CODE + 0xFFF0
M64 = (1 << 64) - 1
M32 = (1 << 32) - 1
TRAP = "TRAP"
IMIN = 1 << 63  # INT64_MIN as u64
NEG1 = M64

SIG = {
    "div_s_m1": ("i32", "i32"),
    "rem_s_m1": ("i32", "i32"),
    "div_s": ("i64", "i64"),
    "rem_s": ("i64", "i64"),
    "div_s_hi": ("i64", "i64"),
}

# (function, args tuple (unsigned), expected u32 or TRAP)
VECTORS = [
    # --- the issue's exact shape: dividend from halves, divisor const -1 ---
    ("div_s_m1", (0, 0x80000000), TRAP),  # INT64_MIN / -1 -> overflow trap
    ("div_s_m1", (100, 0), (-100) & M32),  # issue row 2: normal path intact
    ("div_s_m1", ((-100) & M32, M32), 100),  # -100 / -1 = 100
    # --- fix-guard twin: rem_s(INT64_MIN, -1) == 0, NO trap ---
    ("rem_s_m1", (0, 0x80000000), 0),
    ("rem_s_m1", (100, 0), 0),  # 100 rem -1 = 0
    # --- general two-i64-param forms ---
    ("div_s", (IMIN, NEG1), TRAP),  # overflow trap, runtime divisor
    ("div_s", (100, NEG1), (-100) & M32),
    ("div_s", (IMIN, 1), 0),  # INT64_MIN / 1: lo word 0, NO trap
    ("div_s_hi", (IMIN, 1), 0x80000000),  # ... hi word intact, NO trap
    ("div_s", (IMIN, 2), 0),  # INT64_MIN / 2: defined, NO trap
    ("div_s_hi", (IMIN, 2), 0xC0000000),
    ("div_s", ((-100) & M64, 7), (-14) & M32),
    ("rem_s", (IMIN, NEG1), 0),  # twin again through the i64-param form
    ("rem_s", ((-100) & M64, 7), (-2) & M32),
    # --- divide by zero must still trap (guard ordering unchanged) ---
    ("div_s", (100, 0), TRAP),
    ("rem_s", (100, 0), TRAP),
]


def sext(kind, v):
    bits = 32 if kind == "i32" else 64
    return v - (1 << bits) if v & (1 << (bits - 1)) else v


def wasmtime_oracle(func, args):
    if shutil.which("wasmtime") is None:
        return None
    sig = SIG[func]
    argv = ["wasmtime", "run", "--invoke", func, WAT] + [
        str(sext(k, a)) for k, a in zip(sig, args)
    ]
    out = subprocess.run(argv, capture_output=True, text=True)
    if out.returncode != 0:
        if "divide by zero" in out.stderr or "integer overflow" in out.stderr:
            return TRAP
        return None
    return int(out.stdout.strip()) & M32


def compile_func(func, out_o):
    argv = [
        SYNTH, "compile", WAT,
        "-t", "cortex-m3",
        "-n", func,
        "--relocatable",
        "-o", out_o,
    ]
    r = subprocess.run(argv, capture_output=True, text=True)
    if r.returncode != 0:
        print(f"COMPILE FAILED for {func}:\n{r.stderr}")
        sys.exit(2)


def emulate(elf_path, func, args):
    """Returns the u32 result, or TRAP if execution hit a UDF/fault."""
    e = ELFFile(open(elf_path, "rb"))
    text = e.get_section_by_name(".text").data()
    # Symbols from the symtab, never from disasm text (host-dependent).
    st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: s["st_value"] & ~1 for s in st.iter_symbols() if s.name}
    if func not in syms:
        print(f"SYMBOL MISSING: {func}")
        sys.exit(2)

    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x100000)
    mu.mem_map(STK, 0x100000)
    mu.mem_write(CODE, text)
    mu.mem_write(RET, struct.pack("<HH", 0xBF00, 0xBF00))  # Thumb NOP pad

    # AAPCS: i32 args take one register; i64 args a lo:hi pair at an even reg.
    regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
    ri = 0
    for kind, a in zip(SIG[func], args):
        if kind == "i32":
            mu.reg_write(regs[ri], a & M32)
            ri += 1
        else:
            ri += ri & 1  # even-align the pair
            mu.reg_write(regs[ri], a & M32)
            mu.reg_write(regs[ri + 1], (a >> 32) & M32)
            ri += 2
    mu.reg_write(UC_ARM_REG_SP, STK + 0x80000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        # div expansions loop 64 times (~1.1k insns) — generous budget.
        mu.emu_start((CODE + syms[func]) | 1, RET, count=50000)
    except UcError:
        return TRAP  # UDF #0 (zero-divisor or overflow guard) or genuine fault
    if mu.reg_read(UC_ARM_REG_PC) != RET & ~1:
        return TRAP  # never reached the return pad
    return mu.reg_read(UC_ARM_REG_R0) & M32


tmp = tempfile.mkdtemp(prefix="i64divs633_")
fails = 0
for func, args, want in VECTORS:
    oracle = wasmtime_oracle(func, args)
    if oracle is not None and oracle != want:
        print(f"HARNESS BUG: builtin expect {want} != wasmtime {oracle} for {func}{args}")
        sys.exit(2)
    want = oracle if oracle is not None else want
    obj = os.path.join(tmp, f"{func}.o")
    if not os.path.exists(obj):
        compile_func(func, obj)
    got = emulate(obj, func, args)
    ok = got == want
    fails += 0 if ok else 1
    argstr = ", ".join(hex(a) for a in args)
    gots = got if got == TRAP else hex(got)
    wants = want if want == TRAP else hex(want)
    print(f"{func}({argstr}) = {gots} (oracle: {wants}) {'OK' if ok else 'MISMATCH'}")

if fails == 0:
    print("ORACLE: PASS")
    sys.exit(0)
print(f"ORACLE: FAIL — {fails} vector(s) wrong (#633)")
sys.exit(1)
