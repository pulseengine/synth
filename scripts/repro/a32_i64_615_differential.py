#!/usr/bin/env python3
# #615: A32/ARM-mode encoder silently NOP'd every i64 op (--target cortex-r5)
# — mul/shift/rotate/compare/eqz/clz/ctz/popcnt/div/rem/const/extend/wrap all
# encoded as 0xE1A00000, so the operation vanished and functions returned
# garbage. This differential executes the A32 object under unicorn
# (UC_MODE_ARM — NOT Thumb) and compares every exported function against the
# wasmtime oracle across sign-boundary / lo-hi-straddle vectors.
#
# Symbols are read from the ELF symtab, never from disasm text (#489).
#
# Usage:
#   synth compile scripts/repro/a32_i64_615.wat --target cortex-r5 \
#       --all-exports --relocatable --no-optimize -o /tmp/a615.o
#   python3 a32_i64_615_differential.py /tmp/a615.o scripts/repro/a32_i64_615.wat
#
# Deps: unicorn, pyelftools, wasmtime (pip).
import sys

from elftools.elf.elffile import ELFFile
from unicorn import Uc, UC_ARCH_ARM, UC_MODE_ARM
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_SP,
)
from wasmtime import Instance, Module, Store

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/a615.o"
WAT = sys.argv[2] if len(sys.argv) > 2 else "scripts/repro/a32_i64_615.wat"

M64 = (1 << 64) - 1
M32 = (1 << 32) - 1
CODE, STK = 0x1000000, 0x6000000
RET = CODE + 0xFFF00  # return pad inside the CODE mapping

# --- ELF: .text + symtab (#489: symbols from SHT_SYMTAB, not disasm text) ---
e = ELFFile(open(ELF, "rb"))
text = e.get_section_by_name(".text").data()
st = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] for s in st.iter_symbols() if s.name}
odd = [n for n, v in syms.items() if n.startswith(("func_",)) and v & 1]
if odd:
    print(f"A32 symbol(s) with Thumb bit set (#598 regression): {odd}")
    sys.exit(1)

# --- wasmtime oracle ---
store = Store()
module = Module(store.engine, open(WAT).read())
inst = Instance(store, module, [])
exports = inst.exports(store)


def s32(v):
    v &= M32
    return v - (1 << 32) if v >= (1 << 31) else v


def oracle(fn, args):
    r = exports[fn](store, *[s32(a) for a in args])
    return r & M64


def emulate(fn, args, is64):
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM)
    mu.mem_map(CODE, 0x100000)
    mu.mem_map(STK, 0x100000)
    mu.mem_write(CODE, text)
    mu.mem_write(RET, (0xE1A00000).to_bytes(4, "little") * 4)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x80000)
    mu.reg_write(UC_ARM_REG_LR, RET)  # A32 return: bit 0 clear
    for reg, val in zip((UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3), args):
        mu.reg_write(reg, val & M32)
    mu.emu_start(CODE + syms[fn], RET, count=500_000)
    lo = mu.reg_read(UC_ARM_REG_R0) & M32
    if not is64:
        return lo
    return ((mu.reg_read(UC_ARM_REG_R1) & M32) << 32) | lo


def halves(v):
    v &= M64
    return (v & M32, v >> 32)


def neg64(v):
    return (-v) & M64


# --- vectors: sign boundaries + lo/hi straddles ---
PAIRS = [
    (1, 3),
    (neg64(1), 7),
    (0x8000000000000000, 1),
    (0x00000000FFFFFFFF, 0x0000000100000000),
    (0x123456789ABCDEF0, 0x0000000FEDCBA987),
    (0x7FFFFFFFFFFFFFFF, neg64(2)),
    (0xFEDCBA9876543210, 0x0000000000010001),
    (5, 5),
]
UNARY = [
    0,
    1,
    neg64(1),
    0x8000000000000000,
    0x00000000FFFFFFFF,
    0xFFFFFFFF00000000,
    0x123456789ABCDEF0,
    0x80,
]
SHIFT_VALS = [0x8000000000000001, 0x123456789ABCDEF0, 0xFFFFFFFF00000000]
AMOUNTS = [0, 1, 31, 32, 33, 63, 65]

cases = []  # (fn, args, is64_result)
for fn in ("add64", "sub64", "mul64", "and64", "or64", "xor64",
           "div_u64", "div_s64", "rem_u64", "rem_s64"):
    for a, b in PAIRS:
        cases.append((fn, halves(a) + halves(b), True))
for fn in ("shl64", "shr_u64", "shr_s64", "rotl64", "rotr64"):
    for v in SHIFT_VALS:
        for n in AMOUNTS:
            cases.append((fn, halves(v) + (n,), True))
for fn in ("eq64", "ne64", "lt_s64", "lt_u64", "gt_s64",
           "gt_u64", "le_s64", "le_u64", "ge_s64", "ge_u64"):
    for a, b in PAIRS:
        cases.append((fn, halves(a) + halves(b), False))
for fn in ("clz64", "ctz64", "popcnt64", "extend8_s64",
           "extend16_s64", "extend32_s64"):
    for v in UNARY:
        cases.append((fn, halves(v), True))
for fn in ("eqz64", "wrap64"):
    for v in UNARY:
        cases.append((fn, halves(v), False))
for v in (0, 1, 0xFFFFFFFF, 0x80000000, 0x12345678):
    cases.append(("extend_s", (v,), True))
    cases.append(("extend_u", (v,), True))
    cases.append(("popcnt32", (v,), False))
cases.append(("const64", (), True))
for a, b in ((0, 0), (1, 2), (0xFFFFFFFF, 0), (0x80000000, 0x7FFFFFFF)):
    cases.append(("lt_s32", (a, b), False))
for c in (0, 1, 0xFFFFFFFF):
    cases.append(("sel32", (11, 22, c), False))

missing = sorted({fn for fn, _, _ in cases} - set(syms))
if missing:
    print(f"SYMBOL MISSING: {missing}")
    sys.exit(1)

fails = 0
for fn, args, is64 in cases:
    want = oracle(fn, args)
    if not is64:
        want &= M32
    got = emulate(fn, args, is64)
    if got != want:
        fails += 1
        print(f"MISMATCH {fn}{args}: synth={got:#x} wasmtime={want:#x}")

print(f"{len(cases)} cases, {fails} mismatches")
if fails:
    print("ORACLE: FAIL — A32 i64 codegen diverges from wasmtime (#615)")
    sys.exit(1)
print("ORACLE: PASS — A32 (cortex-r5) matches wasmtime on all vectors")
