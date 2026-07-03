# #610: i64.rotl / i64.rotr / i64.div_u / i64.rem_u compiled to code returning
# 0 for every input on the ARM Cortex-M path. The encoder expansions either
# used colliding hardcoded scratch and restored it OVER the result (rot: `POP
# {R4}` with rd_lo == R4) or ignored their register operands entirely (div/rem:
# hardcoded R0:R1/R2:R3, result to R0:R1, while the selector read rd = R4:R5).
# Pre-fix, every vector below (except the shl4 control) returned the stale
# caller register — 0.
#
# Differential: compile EACH export with the issue's exact config
# (`-t cortex-m3 -n <name> --relocatable`), emulate under unicorn
# (UC_MODE_THUMB), and difference against the wasmtime oracle. Divide-by-zero
# vectors assert BOTH sides trap (synth now emits a UDF #0 guard; wasmtime
# reports "integer divide by zero").
#
# Edge vectors per the #610 gate: rot-by-0 identity, rot by 32 (half swap),
# rot >= 64 (mod-64 mask), div by 1 / by self / by zero (trap), high-bit
# patterns, >32-bit divisors, and _hi twins so both halves of the 64-bit
# result are checked through the i32 return register.
#
# Usage: python3 i64_rot_div_610_differential.py <synth-binary> [wat]
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
    else os.path.join(os.path.dirname(__file__), "i64_rot_div_610.wat")
)
CODE, STK = 0x1000000, 0x6000000
RET = CODE + 0xFFF0
M64 = (1 << 64) - 1
M32 = (1 << 32) - 1
TRAP = "TRAP"


def sext64(v):
    return v - (1 << 64) if v & (1 << 63) else v


def rotl(x, n):
    n &= 63
    return ((x << n) | (x >> (64 - n))) & M64 if n else x


PAT = 0x123456789ABCDEF0

# (function, args-as-u64 tuple, wasm-semantics expected i32-as-u32 or TRAP)
VECTORS = [
    # --- rotl: identity, issue repro, cross-word, mod-64, high-bit ---
    ("rotl", (123, 0), 123),  # identity — the issue's clearest tell
    ("rotl", (1, 8), 256),  # issue table row 1
    ("rotl", (PAT, 4), rotl(PAT, 4) & M32),
    ("rotl_hi", (PAT, 4), rotl(PAT, 4) >> 32),
    ("rotl", (PAT, 32), rotl(PAT, 32) & M32),  # exact half swap
    ("rotl_hi", (PAT, 32), rotl(PAT, 32) >> 32),
    ("rotl", (PAT, 33), rotl(PAT, 33) & M32),  # large-branch path
    ("rotl_hi", (PAT, 33), rotl(PAT, 33) >> 32),
    ("rotl", (PAT, 63), rotl(PAT, 63) & M32),
    ("rotl_hi", (PAT, 63), rotl(PAT, 63) >> 32),
    ("rotl", (PAT, 64), PAT & M32),  # rot >= 64: mod-64 identity
    ("rotl_hi", (PAT, 64), PAT >> 32),
    ("rotl", (PAT, 100), rotl(PAT, 100) & M32),
    ("rotl", (0x8000000000000001, 1), 3),  # both edge bits cross
    # --- rotr ---
    ("rotr", (256, 8), 1),  # issue table row 3
    ("rotr", (PAT, 0), PAT & M32),  # identity
    ("rotr_hi", (PAT, 0), PAT >> 32),
    ("rotr", (1, 1), 0),  # lo bit 0 -> hi bit 31
    ("rotr_hi", (1, 1), 0x80000000),
    ("rotr", (PAT, 32), rotl(PAT, 32) & M32),  # rotr 32 == rotl 32
    ("rotr_hi", (PAT, 32), rotl(PAT, 32) >> 32),
    ("rotr", (PAT, 63), rotl(PAT, 1) & M32),  # rotr 63 == rotl 1
    ("rotr_hi", (PAT, 63), rotl(PAT, 1) >> 32),
    ("rotr", (PAT, 64), PAT & M32),
    # --- const-amount shapes (the issue's exact repro) ---
    ("rotl8", (1,), 256),
    ("rotl0", (123,), 123),
    ("rotr8", (256,), 1),
    # --- div_u: issue rows, by 1, by self, big, >32-bit divisor ---
    ("div_u", (100, 7), 14),
    ("div_u", (700, 7), 100),
    ("divu7", (100,), 14),
    ("div_u", (PAT, 1), PAT & M32),  # by 1: identity
    ("div_u_hi", (PAT, 1), PAT >> 32),
    ("div_u", (PAT, PAT), 1),  # by self
    ("div_u", (M64, 3), (M64 // 3) & M32),
    ("div_u_hi", (M64, 3), (M64 // 3) >> 32),
    ("div_u", (1 << 63, 10), ((1 << 63) // 10) & M32),
    ("div_u_hi", (1 << 63, 10), ((1 << 63) // 10) >> 32),
    ("div_u", (PAT, 1 << 32), (PAT >> 32) & M32),  # 64-bit divisor
    ("div_u", (7, 100), 0),  # divisor > dividend
    # --- rem_u ---
    ("rem_u", (100, 7), 2),  # issue table row 6
    ("rem_u", (PAT, 1), 0),  # by 1: zero
    ("rem_u", (M64, 1 << 32), M32),
    ("rem_u_hi", (M64, (1 << 32) + 1), 0),
    ("rem_u", (7, 100), 7),
    # --- div_s / rem_s (same fixed-ABI disease, fixed together) ---
    ("div_s", ((-100) & M64, 7), (-14) & M32),
    ("div_s", (100, (-7) & M64), (-14) & M32),
    ("div_s", ((-100) & M64, (-7) & M64), 14),
    ("rem_s", ((-100) & M64, 7), (-2) & M32),
    ("rem_s", (100, (-7) & M64), 2),
    # --- divide by zero: BOTH sides must trap ---
    ("div_u", (100, 0), TRAP),
    ("rem_u", (100, 0), TRAP),
    ("div_s", (100, 0), TRAP),
    ("rem_s", (100, 0), TRAP),
    # --- control: correct before the fix (issue table) ---
    ("shl4", (256,), 4096),
]


def wasmtime_oracle(func, args):
    if shutil.which("wasmtime") is None:
        return None
    argv = ["wasmtime", "run", "--invoke", func, WAT] + [str(sext64(a)) for a in args]
    out = subprocess.run(argv, capture_output=True, text=True)
    if out.returncode != 0:
        if "divide by zero" in out.stderr:
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

    # AAPCS: each i64 arg is a lo:hi register pair starting at an even reg.
    regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
    ri = 0
    for a in args:
        mu.reg_write(regs[ri], a & M32)
        mu.reg_write(regs[ri + 1], (a >> 32) & M32)
        ri += 2
    mu.reg_write(UC_ARM_REG_SP, STK + 0x80000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        # div/rem expansions loop 64 times (~1.1k insns) — generous budget.
        mu.emu_start((CODE + syms[func]) | 1, RET, count=50000)
    except UcError:
        return TRAP  # UDF #0 (divide-by-zero guard) or a genuine fault
    if mu.reg_read(UC_ARM_REG_PC) != RET & ~1:
        return TRAP  # never reached the return pad
    return mu.reg_read(UC_ARM_REG_R0) & M32


tmp = tempfile.mkdtemp(prefix="i64rotdiv610_")
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
print(f"ORACLE: FAIL — {fails} vector(s) wrong (#610)")
sys.exit(1)
