# #599: i64.shr_u / i64.shr_s register-pair right shift miscompiled on the
# single-function CLI path (`-n <name>`): the path built its CompileConfig with
# `..default()` and never plumbed the module's declared param widths
# (func_params_i64), so a read-only i64 param stayed classified i32 — the
# shift-amount constant pair was allocated INTO the param's live high register
# (movw r1, #32 over hi(param)). shr by 32 then returned the SHIFT AMOUNT
# (lsr rd, r1, #0 with r1=32); smaller shifts leaked `n << (32-n)` into the
# result (256>>1 gave 0x80000080). The all-exports path plumbs the widths
# (#518) and was already correct.
#
# Differential: compile EACH export with `-n <name> --no-optimize` (the broken
# path), emulate under unicorn (UC_MODE_THUMB), and difference against the
# wasmtime oracle (invoked per vector when wasmtime is on PATH; otherwise the
# built-in wasm-semantics expectation, which was cross-checked against
# wasmtime when this harness was written).
#
# High-bit-set vectors included per the #599 gate: hi=0x80000001 >> 1 pulls a
# hi bit into lo bit 31; 1<<63 >> 63 exercises the n>=32 funnel path both
# logically (=1) and arithmetically (=-1).
#
# Usage: python3 i64_shr_599_differential.py <synth-binary> [wat]
import os
import shutil
import struct
import subprocess
import sys
import tempfile

from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_THUMB
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_SP,
)

SYNTH = sys.argv[1] if len(sys.argv) > 1 else "target/debug/synth"
WAT = sys.argv[2] if len(sys.argv) > 2 else os.path.join(os.path.dirname(__file__), "i64_shr_599.wat")
CODE, STK = 0x1000000, 0x6000000
RET = CODE + 0xFFF0
M64 = (1 << 64) - 1
M32 = (1 << 32) - 1


def sext64(v):
    return v - (1 << 64) if v & (1 << 63) else v


# (function, args-as-u64 tuple, wasm-semantics expected i32-as-u32)
VECTORS = [
    ("shr_u_32", (0x0000006300000001,), 99),  # lo=1 hi=99 -> hi word
    ("shr_s_32", (0x0000006300000001,), 99),
    ("shr_u_1", (256,), 128),
    ("shr_u_1", (0x8000000100000000,), 0x80000000),  # hi bit 0 -> lo bit 31
    ("shr_u_63", (1 << 63,), 1),
    ("shr_s_63", (1 << 63,), M32),  # -1 wrapped
    ("shr_u_var", (1 << 63, 63), 1),
    ("shr_u_var", (256, 4), 16),
    ("shl_4", (256,), 4096),  # control: shl was already correct
]


def wasmtime_oracle(func, args):
    if shutil.which("wasmtime") is None:
        return None
    argv = ["wasmtime", "run", "--invoke", func, WAT] + [str(sext64(a)) for a in args]
    out = subprocess.run(argv, capture_output=True, text=True)
    if out.returncode != 0:
        return None
    return int(out.stdout.strip()) & M32


def compile_func(func, out_o):
    argv = [
        SYNTH, "compile", WAT,
        "-t", "cortex-m3",
        "-n", func,
        "--no-optimize",
        "-o", out_o,
    ]
    r = subprocess.run(argv, capture_output=True, text=True)
    if r.returncode != 0:
        print(f"COMPILE FAILED for {func}:\n{r.stderr}")
        sys.exit(2)


def emulate(elf_path, func, args):
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
    mu.emu_start((CODE + syms[func]) | 1, RET, count=5000)
    return mu.reg_read(UC_ARM_REG_R0) & M32


tmp = tempfile.mkdtemp(prefix="i64shr599_")
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
    print(f"{func}({argstr}) = {got:#x} (oracle: {want:#x}) {'OK' if ok else 'MISMATCH'}")

if fails == 0:
    print("ORACLE: PASS")
    sys.exit(0)
print(f"ORACLE: FAIL — {fails} vector(s) wrong (#599)")
sys.exit(1)
