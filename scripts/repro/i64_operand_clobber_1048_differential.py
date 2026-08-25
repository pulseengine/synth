#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 105
# #1048: the Thumb-2 and A32 expansions of I64Shl / I64ShrU / I64ShrS opened
# by masking the shift amount IN PLACE (`AND rm_lo, rm_lo, #63`) and writing
# `amt-32` into the amount's HOME HIGH REGISTER (`SUBS rm_hi, rm_lo, #32`,
# then RSB/LSR scratch traffic through the same register) — the expansion
# destroyed its own input operand, so re-reading the amount after the shift
# returned a mangled value (amt=64 read back 0; amt=67 read back 3; the hi
# limb of amt=35 read back 3). Sibling class fixed with it: I64Clz / I64Ctz /
# I64Popcnt ended with `MOV rnhi, #0` — a hi-clear aimed at the result that
# lands on the OPERAND's home high register on the direct selector.
#
# WHY THE WIRED #599 DIFFERENTIAL WAS BLIND: every function in
# i64_shr_599.wat consumes the shift result immediately (i32.wrap_i64) and
# NEVER reads the amount again — the destroyed registers are dead in every
# one of its vectors, and it only ever checks R0. This harness exists to
# exercise the orthogonal axis: every function re-reads an operand AFTER the
# pseudo-op consumed it, so an expansion that writes its own inputs cannot
# pass.
#
# Legs: Thumb-2 OPTIMIZED (cortex-m4), Thumb-2 DIRECT (--relocatable), and
# A32 DIRECT (cortex-r5 --relocatable --no-optimize, UC_MODE_ARM). Oracle:
# wasmtime when on PATH (cross-checked against the builtin expectation);
# builtin pure-python WASM semantics otherwise.
#
# Usage: python3 i64_operand_clobber_1048_differential.py [synth-binary] [wat]
import os
import shutil
import struct
import subprocess
import sys
import tempfile

from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

SYNTH = sys.argv[1] if len(sys.argv) > 1 else "target/debug/synth"
WAT = (
    sys.argv[2]
    if len(sys.argv) > 2
    else os.path.join(os.path.dirname(__file__), "i64_operand_clobber_1048.wat")
)
CODE, STK, LINMEM = 0x1000000, 0x6000000, 0x20000000
RET = CODE + 0xFFF0
M64 = (1 << 64) - 1
M32 = (1 << 32) - 1


def sext64(v):
    return v - (1 << 64) if v & (1 << 63) else v


def clz64(x):
    return 64 if x == 0 else 64 - x.bit_length()


def ctz64(x):
    return 64 if x == 0 else (x & -x).bit_length() - 1


# WASM reference semantics (i64, shift amounts mod 64).
def expect(func, args):
    if func in (
        "shl_reread",
        "shr_u_reread",
        "shr_s_reread",
        "shl_reread_val",
        "div_u_reread",
        "rotl_reread",
    ):
        x, amt = args
        n = amt & 63
        if func == "shl_reread":
            r = (x << n) & M64
            back = amt
        elif func == "shr_u_reread":
            r = x >> n
            back = amt
        elif func == "shr_s_reread":
            r = sext64(x) >> n
            back = amt
        elif func == "div_u_reread":
            r = x // amt
            back = amt
        elif func == "rotl_reread":
            r = ((x << n) | (x >> (64 - n))) & M64 if n else x
            back = amt
        else:  # shl_reread_val
            r = (x << n) & M64
            back = x
        return (r + back) & M64
    x = args[0]
    if func == "clz_reread":
        c = clz64(x)
    elif func == "ctz_reread":
        c = ctz64(x)
    else:  # popcnt_reread
        c = bin(x).count("1")
    return (c + x) & M64


SHIFT_FUNCS = ("shl_reread", "shr_u_reread", "shr_s_reread", "shl_reread_val")
SHIFT_AMTS = (3, 35, 64, 67, 127)
COUNT_FUNCS = ("clz_reread", "ctz_reread", "popcnt_reread")
COUNT_XS = (0x100000005, 0xDEADBEEF00000001, 5)  # hi!=0 twice, hi==0 control

# The #610 fixed-ABI wrapper family (restores its operands by construction):
# pinned so a wrapper regression is caught by execution.
WRAPPER_FUNCS = ("div_u_reread", "rotl_reread")

VECTORS = (
    [(f, (8, a)) for f in SHIFT_FUNCS for a in SHIFT_AMTS]
    + [(f, (x,)) for f in COUNT_FUNCS for x in COUNT_XS]
    + [(f, (1000, a)) for f in WRAPPER_FUNCS for a in (3, 35, 67)]
)


def wasmtime_oracle(func, args):
    if shutil.which("wasmtime") is None:
        return None
    argv = ["wasmtime", "run", "--invoke", func, WAT] + [str(sext64(a)) for a in args]
    out = subprocess.run(argv, capture_output=True, text=True)
    if out.returncode != 0:
        return None
    return int(out.stdout.strip()) & M64


def compile_module(out_o, backend_args):
    argv = [SYNTH, "compile", WAT, "--all-exports", "-o", out_o] + backend_args
    r = subprocess.run(argv, capture_output=True, text=True)
    if r.returncode != 0:
        print(f"COMPILE FAILED ({' '.join(backend_args)}):\n{r.stderr}")
        sys.exit(2)


def emulate(elf_path, func, args, thumb):
    e = ELFFile(open(elf_path, "rb"))
    text = e.get_section_by_name(".text").data()
    # Symbols from the symtab, never from disasm text (host-dependent, #489).
    st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: s["st_value"] & ~1 for s in st.iter_symbols() if s.name}
    if func not in syms:
        print(f"SYMBOL MISSING: {func}")
        sys.exit(2)

    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB if thumb else UC_MODE_ARM)
    mu.mem_map(CODE, 0x100000)
    mu.mem_map(STK, 0x100000)
    mu.mem_map(LINMEM, 0x100000)
    mu.mem_write(CODE, text)
    if thumb:
        mu.mem_write(RET, struct.pack("<HH", 0xBF00, 0xBF00))  # Thumb NOP pad
    else:
        mu.mem_write(RET, struct.pack("<II", 0xE1A00000, 0xE1A00000))  # A32 NOPs

    # AAPCS: each i64 arg is a lo:hi register pair starting at an even reg.
    regs = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
    ri = 0
    for a in args:
        mu.reg_write(regs[ri], a & M32)
        mu.reg_write(regs[ri + 1], (a >> 32) & M32)
        ri += 2
    mu.reg_write(UC_ARM_REG_R11, LINMEM)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x80000)
    mu.reg_write(UC_ARM_REG_LR, RET | (1 if thumb else 0))
    mu.emu_start((CODE + syms[func]) | (1 if thumb else 0), RET, count=20000)
    # i64 return in R0:R1.
    return (mu.reg_read(UC_ARM_REG_R1) << 32 | mu.reg_read(UC_ARM_REG_R0)) & M64


LEGS = [
    ("THUMB OPTIMIZED", ["--target", "cortex-m4"], True),
    ("THUMB DIRECT (--relocatable)", ["--target", "cortex-m4", "--relocatable"], True),
    (
        "A32 DIRECT (cortex-r5)",
        ["--target", "cortex-r5", "--relocatable", "--no-optimize"],
        False,
    ),
]

tmp = tempfile.mkdtemp(prefix="i64clob1048_")
fails = 0
for label, backend_args, thumb in LEGS:
    obj = os.path.join(tmp, label.split()[0].lower() + ("_rel" if "relocatable" in " ".join(backend_args) else "") + ".o")
    compile_module(obj, backend_args)
    print(f"--- {label} ---")
    for func, args in VECTORS:
        want = expect(func, args)
        oracle = wasmtime_oracle(func, args)
        if oracle is not None and oracle != want:
            print(f"HARNESS BUG: builtin expect {want:#x} != wasmtime {oracle:#x} for {func}{args}")
            sys.exit(2)
        got = emulate(obj, func, args, thumb)
        ok = got == want
        fails += 0 if ok else 1
        argstr = ", ".join(hex(a) for a in args)
        print(f"{func}({argstr}) = {got:#x} (oracle: {want:#x}) {'OK' if ok else 'MISMATCH'}")

if fails == 0:
    print("ORACLE: PASS")
    sys.exit(0)
print(f"ORACLE: FAIL — {fails} vector(s) wrong (#1048 operand clobber)")
sys.exit(1)
