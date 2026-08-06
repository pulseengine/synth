#!/usr/bin/env python3
# ci-status: wired
"""#916 — i64 zero-fill mis-encodes for a HIGH destination (R8-R12).

The 16-bit `MOVS Rd,#imm8` (T1) has a **three-bit** Rd field. `reg_to_bits(R8)`
is 8, so `8 << 8 = 0x0800` and `0x2000 | 0x0800 = 0x2800` — the emitted halfword
is `CMP r0,#0`, not a move. The half that must be zeroed is NEVER WRITTEN and
keeps whatever the destination register held; the flags are clobbered too.

Five expansions carried the defect (`I64Shl`, `I64ShrU`, `I64Clz`, `I64Ctz`,
`I64ExtendI32U`). The unit test `i64_high_reg_zero_fill_916.rs` pins the emitted
halfwords and the expansion certifier pins the symbolic semantics; this oracle
is the third leg — it EXECUTES synth's ARM under unicorn against wasmtime, which
the byte-level tests cannot do.

That matters specifically because the fix CHANGED INSTRUCTION SIZE. `MOV.W` is
4 bytes where `MOVS` was 2, and in `I64Shl`/`I64ShrU` the expansion's internal
`B .done` targets the END of the sequence — PAST the zero-fill — so its
displacement had to be recomputed (0xE002 -> 0xE003). A mis-recomputed branch
would sail past the end of the expansion into the next instruction, and NO
byte-level assertion on the tail halfword would notice. Only execution does.
The shift amounts below straddle 32 deliberately so both arms of that branch,
and the branch itself, are exercised.

`pressure_shru` is the reachability witness: with four i32 params pinned in
r0-r3 (#193/#204) and several live i64 pairs, the allocator puts a zero-fill
destination in R8. Confirmed present in the emitted image — `MOV.W R8, #0`
appears in that function's body. Pre-fix that halfword was `0x2800`.

Run:
  synth compile scripts/repro/i64_high_reg_zero_fill_916.wat -o /tmp/zf916.elf \
        --target cortex-m4 --relocatable --all-exports
  python scripts/repro/i64_high_reg_zero_fill_916_differential.py /tmp/zf916.elf

Exits nonzero on any mismatch so it can gate a release.
"""

import sys
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R8,
    UC_ARM_REG_SP,
)

ELF = sys.argv[1] if len(sys.argv) > 1 else "/tmp/zf916.elf"
WAT = Path(__file__).with_name("i64_high_reg_zero_fill_916.wat")

# Ground truth: wasmtime.
eng = wasmtime.Engine()
mod = wasmtime.Module(eng, WAT.read_bytes())
store = wasmtime.Store(eng)
inst = wasmtime.Instance(store, mod, [])
exports = inst.exports(store)

# synth's ARM under unicorn.
elf = ELFFile(open(ELF, "rb"))
text = elf.get_section_by_name(".text").data()
symtab = [s for s in elf.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}

# --------------------------------------------------------------------------
# REACHABILITY WITNESS — this oracle's teeth.
#
# Everything below only tests #916 if the allocator actually puts a zero-fill
# destination in R8-R12 somewhere in this image. If it stops doing so, every
# assertion still passes and the oracle silently degrades into a no-op that
# prints "48/48 OK" while testing nothing about the high-register path — the
# #890 "gate that cannot fail" shape.
#
# So assert the witness directly: scan .text for the 32-bit `MOV.W Rd,#0` (T2,
# F04F 0000 | Rd<<8) with Rd >= 8. That encoding EXISTS ONLY BECAUSE of the
# #916 fix; before it the same site emitted the 16-bit 0x2800.
#
# This is expected to go RED, not silently green, if the allocator changes —
# e.g. VCR-DEC-001 / #917's interference edge keeps R8 out of the candidate
# colours. That is correct behavior: it says the module lost its reachability
# witness and needs a different pressure shape, rather than pretending to
# still cover the class.
_hw = [
    int.from_bytes(text[i : i + 2], "little") for i in range(0, len(text) - 1, 2)
]
_high_zero_fills = [
    (i * 2, (_hw[i + 1] >> 8) & 0xF)
    for i in range(len(_hw) - 1)
    if _hw[i] == 0xF04F and (_hw[i + 1] & 0x00FF) == 0 and ((_hw[i + 1] >> 8) & 0xF) >= 8
]
assert _high_zero_fills, (
    "REACHABILITY LOST: no `MOV.W Rd,#0` with Rd >= R8 in .text, so this module "
    "no longer exercises the #916 high-register zero-fill and the differential "
    "below proves nothing. The allocator stopped choosing a high register for "
    "these destinations (an allocator change, or VCR-DEC-001/#917 keeping R8 "
    "out of the candidate colours). Restore the witness by raising register "
    "pressure in i64_high_reg_zero_fill_916.wat — do NOT delete this assertion."
)
print(
    "reachability witness: "
    + ", ".join(f"MOV.W R{rd},#0 @ {off:#x}" for off, rd in _high_zero_fills)
)
CODE, STK = 0x10000, 0x90000
mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
mu.mem_map(CODE, 0x10000)
mu.mem_write(CODE, text)
mu.mem_map(STK, 0x10000)
RET = CODE + 0xFF00
mu.mem_write(RET, b"\x00\xbf\x00\xbf")

MASK64 = (1 << 64) - 1


def signed32(v):
    return v - (1 << 32) if v >= 1 << 31 else v


# The poison. #916 leaves the destination register UNWRITTEN, so it keeps
# whatever it held on entry. Seeding R8 (and r0-r3 for the single-param
# functions) with a value that is not plausibly a correct result is what turns
# the latent bug into an observable failure: a run that "passes" only because
# the stale register happened to hold 0 would be a false green.
POISON = 0xDEADBEEF


def run(name, args):
    for reg, val in zip(
        (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3), args
    ):
        mu.reg_write(reg, val)
    # Unused argument registers and R8 are poisoned, never zeroed.
    for reg in (UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3)[
        len(args) :
    ]:
        mu.reg_write(reg, POISON)
    mu.reg_write(UC_ARM_REG_R8, POISON)
    mu.reg_write(UC_ARM_REG_SP, STK + 0x8000)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    mu.emu_start((CODE + syms[name]) | 1, RET, timeout=5_000_000)
    return mu.reg_read(UC_ARM_REG_R0) | (mu.reg_read(UC_ARM_REG_R1) << 32)


# Shift amounts straddle 32 on purpose: below it the small-shift arm runs and
# the `B .done` whose displacement changed is TAKEN; at/above it the
# large-shift arm containing the widened zero-fill runs.
SHIFTS = [0, 1, 31, 32, 33, 40, 63]

CASES = []
for fn in ("shru_keep_high", "shl_keep_low", "shrs_keep_high"):
    CASES += [(fn, (n,)) for n in SHIFTS]
for fn in ("clz64", "ctz64", "extend_u64"):
    CASES += [
        (fn, (v,))
        for v in (0, 1, 2, 0x80000000, 0xFFFFFFFF, 0x0000FF00, 0xDEADBEEF)
    ]
CASES += [
    ("pressure_shru", a)
    for a in (
        (0, 0, 0, 0),
        (32, 1, 32, 2),
        (40, 7, 33, 11),
        (63, 0xFFFFFFFF, 40, 0x80000000),
        (31, 12345, 63, 54321),
        (1, 0xDEADBEEF, 0, 0xCAFEBABE),
    )
]

ok = True
checked = 0
for name, args in CASES:
    expected = exports[name](store, *[signed32(a) for a in args]) & MASK64
    got = run(name, list(args))
    checked += 1
    good = got == expected
    if not good:
        ok = False
    argstr = ",".join(f"{a:#x}" for a in args)
    print(
        f"{'OK  ' if good else 'FAIL'} {name}({argstr}) = {got:#018x} "
        f"expect {expected:#018x}"
    )

# A differential that silently executed nothing is a false green.
assert checked == len(CASES) and checked > 0, f"no cases executed ({checked})"
print(f"checked {checked} executions across {len({c[0] for c in CASES})} functions")
print("ORACLE:", "PASS" if ok else "FAIL")
sys.exit(0 if ok else 1)
