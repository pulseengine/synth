#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 360
"""#973 — ARM: `select` on an i64-comparison condition with COMPUTED arms.

THE DEFECT, as MEASURED (not as reported — the mechanism was re-derived here
from the emitted bytes and from execution, because a reported mechanism has
been wrong three times in the last release).

`sel_i64_lt_s(a, b) = (i64)a < (i64)b ? a + 100 : b + 200`, compiled
`--target cortex-m4 --relocatable`, lowered to (capstone over the ELF
`.text`, never `synth disasm` text):

    0008: add.w  r3, r0, #0x64     ; then-arm  -> r3
    000c: add.w  r5, r1, #0xc8     ; else-arm  -> r5   (LIVE from here on)
    0010: mov    r6, r0
    0012: asr.w  r7, r6, #0x1f     ; sign-extend a  (pair r6:r7)
    0016: str.w  r3, [sp]          ; SPILL the then-arm to free a pair
    001a: mov    r2, r1
    001c: asr.w  r3, r2, #0x1f     ; sign-extend b  (pair r2:r3)
    0020: cmp    r6, r2
    0022: sbcs.w r4, r7, r3
    0026: ite    lt
    0028: movlt  r4, #1
    002a: movge  r4, #0
    002c: ldr.w  r5, [sp]          ; RELOAD the then-arm INTO r5 == else-arm
    0030: cmp    r4, #0
    0032: it     ne
    0034: movne  r6, r5
    0036: it     eq
    0038: moveq  r6, r5            ; both arms move the SAME register

The spill is NOT the opt-in `SYNTH_SPILL_ON_EXHAUST` rung: `alloc_consecutive_pair`
spills the deepest register-resident vstack entry UNCONDITIONALLY when no free
consecutive pair remains, and the i64 comparison needs two pairs. The reload
then allocated against `live_params` only — the already-popped `val2` (else-arm)
and `cond_reg` are on neither the vstack nor the reserved list, so the allocator
was free to hand out exactly the register the select still needed.

Executed on the pre-fix binary, 5 of 8 argument pairs were wrong and every one
of them returned the THEN-arm:

    BUG sel_i64_lt_s(7,5):     want=205 got=107
    BUG sel_i64_lt_s(0,0):     want=200 got=100
    BUG sel_i64_lt_s(1,-1):    want=199 got=101
    BUG sel_i64_lt_s(100,100): want=300 got=200
    BUG sel_i64_lt_s(-5,-7):   want=193 got=95
    ok  cmp_i64_lt_s(...)  8/8 -- the comparison ALONE was always correct

WHY THE ARMS MUST BE COMPUTED: with `i32.const` arms nothing needs spilling and
the bug is invisible; with EQUAL arms the two `mov`s reading one register is
correct. `guard_const_arms` and `guard_same_arm` are in the fixture precisely so
those two non-signatures are on the record.

Ground truth is wasmtime on the same `.wat`. Both ARM lowering paths are run:
`--relocatable` (the direct selector, `select_with_stack`, where #973 lives) and
the self-contained/optimized path, so a fix that only moves one is visible.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/select_i64cmp_973_arm_differential.py
"""
import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("select_i64cmp_973.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, LIN = 0x100000, 0x40000
RET_PAD = CODE + 0x18000
STACK_BASE, STACK_SIZE = 0x80000, 0x10000
SP0 = STACK_BASE + 0xC000

MEM_POISON = 0xDEADBEEF  # every stack word below the entry SP
REG_POISON = 0xFEEDFACE  # every argument register the signature does not use
CORE_ARGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]

R_ARM_THM_CALL, R_ARM_THM_JUMP24 = 10, 30
M32 = 0xFFFFFFFF

# Every export of the fixture. The two `cmp_*` are the CONTRAST (always
# correct); the four `guard_*` are the shapes the fix must not disturb.
EXPORTS = [
    "sel_i64_lt_s",
    "sel_i64_lt_u",
    "sel_i64_gt_s",
    "sel_i64_le_s",
    "sel_i64_ge_u",
    "sel_i64_eq",
    "sel_i64_ne",
    "sel_i64_deep",
    "sel_wide_i64cmp",
    "cmp_i64_lt_s",
    "cmp_i64_ge_u",
    "guard_const_arms",
    "guard_i32cmp",
    "guard_same_arm",
    "guard_nested",
]

# Argument pairs chosen so BOTH arms are exercised on every comparison kind,
# including the a == b case (which distinguishes le/lt and ge/gt) and the
# sign-boundary pairs where the i64 sign-extension itself matters.
ARGS = [
    (5, 7),
    (7, 5),
    (0, 0),
    (-1, 1),
    (1, -1),
    (100, 100),
    (-5, -7),
    (-7, -5),
    (0x7FFFFFFF, -1),
    (-1, 0x7FFFFFFF),
    (0, -1),
    (-1, 0),
]


def die(msg):
    print(f"#973 ARM ORACLE: FAIL — {msg}")
    sys.exit(1)


def compile_fixture(out, relocatable):
    cmd = [SYNTH, "compile", str(WAT), "--target", "cortex-m4", "--all-exports", "-o", out]
    if relocatable:
        cmd.append("--relocatable")
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0:
        die(f"synth compile failed ({' '.join(cmd)}):\n{p.stdout}\n{p.stderr}")
    return out


def encode_thm_bl(pc_at_reloc, target):
    """Re-encode a Thumb-2 BL, exactly as `ld` resolves R_ARM_THM_CALL."""
    off = (target - (pc_at_reloc + 4)) & 0x01FFFFFF
    s = (off >> 24) & 1
    i1, i2 = (off >> 23) & 1, (off >> 22) & 1
    imm10, imm11 = (off >> 12) & 0x3FF, (off >> 1) & 0x7FF
    j1, j2 = (~i1 & 1) ^ s, (~i2 & 1) ^ s
    return 0xF000 | (s << 10) | imm10, 0xD000 | (j1 << 13) | (j2 << 11) | imm11


def load(path):
    """(symbols, .text with in-module branch relocations applied, base_vaddr)."""
    with open(path, "rb") as fh:
        e = ELFFile(fh)
        symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
        syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
        sec = e.get_section_by_name(".text")
        if sec is None:
            die("no .text section in the compiled object")
        base = sec["sh_addr"]
        text = bytearray(sec.data())
        for rel in e.iter_sections():
            if rel["sh_type"] not in ("SHT_REL", "SHT_RELA"):
                continue
            for r in rel.iter_relocations():
                t = r["r_info_type"]
                name = symtab.get_symbol(r["r_info_sym"]).name
                if t not in (R_ARM_THM_CALL, R_ARM_THM_JUMP24):
                    die(f"unexpected reloc type {t} against {name!r}")
                if name not in syms:
                    die(f"reloc names {name!r}, not a defined symbol")
                off = r["r_offset"]
                hw1, hw2 = encode_thm_bl(CODE + off, CODE + ((syms[name] - base) & ~1))
                struct.pack_into("<HH", text, off, hw1, hw2)
    return syms, bytes(text), base


def run(syms, text, base, name, args):
    """Execute one export under unicorn with the sub-SP stack POISONED."""
    if name not in syms:
        return None, f"symbol {name} missing from .symtab"
    addr = (syms[name] - base) & ~1
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    mu.mem_write(CODE, text)
    # Poison every word the callee's frame can occupy: a read of an
    # uninitialised slot is then legible instead of reading as a benign 0.
    mu.mem_write(STACK_BASE, struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    mu.reg_write(UC_ARM_REG_SP, SP0)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    for i, a in enumerate(args[:4]):
        mu.reg_write(CORE_ARGS[i], a & M32)
    for i in range(len(args), 4):
        mu.reg_write(CORE_ARGS[i], REG_POISON)
    mu.reg_write(UC_ARM_REG_LR, RET_PAD | 1)
    try:
        mu.emu_start((CODE + addr) | 1, RET_PAD, count=20000)
    except UcError as ex:
        return None, str(ex)
    return mu.reg_read(UC_ARM_REG_R0) & M32, ""


def leg(engine, module, obj, label):
    """Run the whole matrix against one compiled object. Returns (checks, fails)."""
    syms, text, base = load(obj)
    checks = fails = 0
    for name in EXPORTS:
        for a, b in ARGS:
            store = wasmtime.Store(engine)
            inst = wasmtime.Instance(store, module, [])
            want = inst.exports(store)[name](store, a, b) & M32
            got, err = run(syms, text, base, name, [a & M32, b & M32])
            checks += 1
            ok = got == want
            if not ok:
                fails += 1
                shown = f"{got}" if got is not None else f"ERR({err})"
                print(f"BUG [{label}] {name}({a},{b}): want={want} got={shown}")
    return checks, fails


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))

    total_checks = total_fails = 0
    with tempfile.TemporaryDirectory() as td:
        for label, reloc in (("relocatable", True), ("self-contained", False)):
            obj = compile_fixture(os.path.join(td, f"sel973_{reloc}.o"), reloc)
            c, f = leg(engine, module, obj, label)
            print(f"[{label}] {c - f}/{c} vectors match wasmtime")
            total_checks += c
            total_fails += f

    print(f"\n#973 CHECKS={total_checks - total_fails}/{total_checks}")
    if total_fails:
        print("#973 ARM i64-cmp select ORACLE: FAIL")
    else:
        print("#973 ARM i64-cmp select ORACLE: PASS")
    sys.exit(1 if total_fails else 0)


if __name__ == "__main__":
    main()
