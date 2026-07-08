# #632: i64.popcnt result clobbered by the expansion's own scratch-restore pop.
#
# The Thumb-2 I64Popcnt expansion saves scratch with `PUSH {R3,R4,R5}`,
# computes popcnt(lo) -> R4 and popcnt(hi) -> R5, materializes the total with
# `ADDS rd, R4, R5`, and then restores scratch with `POP {R3,R4,R5}`. The
# selector-assigned rd is any allocatable register (R0-R8): whenever the
# surrounding pressure (the u64-from-two-u32-halves construction below) lands
# rd inside {R3,R4,R5}, the restore pop overwrites the count one instruction
# after it is produced — the caller receives stale stack garbage (0 under a
# zero-initialized emulator) for EVERY input.
#
# Post-fix the expansion carries the total across the restore in R12 (encoder
# scratch, never allocatable #212, never in any restore set) and only then
# moves it into rd — structural: no choice of rd can collide with the pop.
#
# Differential: compile each export with the issue's exact config
# (`-t cortex-m3 -n <name> --relocatable`), emulate under unicorn
# (UC_MODE_THUMB), difference against the wasmtime oracle.
#
# Usage: python3 i64_popcnt_632_differential.py <synth-binary> [wat]
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
    else os.path.join(os.path.dirname(__file__), "i64_popcnt_632.wat")
)
CODE, STK = 0x1000000, 0x6000000
RET = CODE + 0xFFF0
M64 = (1 << 64) - 1
M32 = (1 << 32) - 1
TRAP = "TRAP"

# Signatures: arg kinds drive both register marshaling and the wasmtime CLI.
SIG = {
    "popcnt64": ("i32", "i32"),
    "popcnt64_hi": ("i32", "i32"),
    "popcnt_direct": ("i64",),
}

# (function, args tuple (unsigned), expected u32) — the #632 issue table plus
# hi-word and direct-form controls.
VECTORS = [
    ("popcnt64", (7, 0), 3),  # issue row 1
    ("popcnt64", (1, 1), 2),  # issue row 2
    ("popcnt64", (M32, 0), 32),  # issue row 3: (-1, 0)
    ("popcnt64", (M32, M32), 64),  # issue row 4: (-1, -1)
    ("popcnt64", (0, 0), 0),
    ("popcnt64", (0, M32), 32),  # all bits in the hi half
    ("popcnt64", (0x12345678, 0x9ABCDEF0), 32),
    ("popcnt64_hi", (M32, M32), 0),  # count is a proper i64: hi word must be 0
    ("popcnt64_hi", (7, 0), 0),
    ("popcnt_direct", (255,), 8),  # control: correct pre-fix
    ("popcnt_direct", (M64,), 64),  # control: correct pre-fix
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
        mu.emu_start((CODE + syms[func]) | 1, RET, count=50000)
    except UcError:
        return TRAP
    if mu.reg_read(UC_ARM_REG_PC) != RET & ~1:
        return TRAP  # never reached the return pad
    return mu.reg_read(UC_ARM_REG_R0) & M32


tmp = tempfile.mkdtemp(prefix="i64popcnt632_")
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
print(f"ORACLE: FAIL — {fails} vector(s) wrong (#632)")
sys.exit(1)
