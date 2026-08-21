#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 34
"""#990 — ARM: a plain local written on only ONE arm of a `br_if` must read 0.

WASM mandates every non-parameter local starts at ZERO. The #457 zero-init
classifier (`read_before_write_locals`) walks the op stream in LINEAR order and
skips any local whose first access is a write — but a write sitting on a
conditionally-skipped path (`br_if`, `if` without else, one `br_table` arm)
does NOT dominate the merge-point read. On the skipping path the frame slot is
never written, and the function returns whatever the previous frame left below
SP: an information-disclosure leak, not merely a wrong answer. Measured on the
v0.58 tree (`--target cortex-m4f --relocatable`):

    0010: cmp    r3, #0
    0012: bne    #0x1c      ; x < 0 -> JUMP PAST the initialisation
    0014: movw   r4, #0xa
    0018: str.w  r4, [sp]   ; the ONLY write to the local's slot
    001c: ldr.w  r5, [sp]   ; on the taken path this slot was NEVER written

#970 fixed the conditionally-written PARAMETER half of this class (a param
must keep its incoming argument); this oracle covers the PLAIN-LOCAL half
(the local must read the mandated 0). The `guard_cond_param_970` case keeps
the two halves from being traded against each other: the fix must zero the
local WITHOUT regressing the param homing.

Every stack word below the entry SP is poisoned with 0xDEADBEEF and every
argument register the signature does not use with 0xFEEDFACE (two DISTINCT
words), so "read an uninitialised slot" is provable as a leak of
previous-frame bytes and cannot be confused with "read the wrong register".
The i64 case reads BOTH return words (r0/r1) — a half-zeroed 8-byte slot
would leak one word and still fail.

Ground truth is wasmtime on the same `.wat`. Symbols come from the ELF
`.symtab` (SHT_SYMTAB), never `synth disasm` text (host-dependent).

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/brif_local_zeroinit_990_arm_differential.py
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

WAT = Path(__file__).with_name("brif_local_zeroinit_990.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

CODE, LIN = 0x100000, 0x40000
RET_PAD = CODE + 0x8000  # mapped, halfword-aligned; emulation stops here
STACK_BASE, STACK_SIZE = 0x80000, 0x10000
SP0 = STACK_BASE + 0xC000  # entry SP: 48 KiB of poison below, 16 KiB above

MEM_POISON = 0xDEADBEEF   # every stack word below the entry SP
REG_POISON = 0xFEEDFACE   # every argument register the signature does not use
CORE_ARGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]

R_ARM_THM_CALL, R_ARM_THM_JUMP24 = 10, 30
M32 = 0xFFFFFFFF
M64 = 0xFFFFFFFFFFFFFFFF

# Exports returning i64 (read r0 = low, r1 = high per AAPCS32).
RET_I64 = {"bl_brif_i64"}

# (export, args). Every `bl_*` case includes at least one vector that SKIPS
# the only write — the vector that reads the never-written slot — plus taken
# vectors so a broken WRITE path is caught too.
CASES = [
    # THE #990 shape: x < 0 takes the br_if and skips the only write.
    ("bl_brif", [0]),
    ("bl_brif", [1]),
    ("bl_brif", [5]),
    ("bl_brif", [0xFFFFFFFF]),   # -1: leaks on the unfixed tree
    ("bl_brif", [0xFFFFFFFB]),   # -5
    ("bl_brif", [0x80000000]),   # INT_MIN
    # `if` without an else: param 0 == 0 skips the only write.
    ("bl_if_no_else", [0]),
    ("bl_if_no_else", [1]),
    ("bl_if_no_else", [0xFFFFFFFF]),
    # if/else writing DIFFERENT locals: one is unwritten on EVERY input.
    ("bl_if_else_one_arm", [0]),
    ("bl_if_else_one_arm", [1]),
    ("bl_if_else_one_arm", [2]),
    # br_table: index >= 1 jumps straight past the writing arm.
    ("bl_br_table", [0]),
    ("bl_br_table", [1]),
    ("bl_br_table", [2]),
    ("bl_br_table", [0xFFFFFFFF]),
    # i64 sibling: BOTH words of the 8-byte slot must be zeroed.
    ("bl_brif_i64", [0]),
    ("bl_brif_i64", [1]),
    ("bl_brif_i64", [0xFFFFFFFF]),
    ("bl_brif_i64", [0xFFFFFFFB]),
    # ── guards: shapes the fix must NOT change ────────────────────────────────
    ("guard_straightline", [0]),
    ("guard_straightline", [4]),
    ("guard_straightline", [0xFFFFFFFF]),
    ("guard_rbw", [7]),
    ("guard_rbw", [0]),
    ("guard_both_arms", [0]),
    ("guard_both_arms", [1]),
    ("guard_same_block", [0]),
    ("guard_same_block", [9]),
    # #970's param half: the conditionally-written PARAM keeps its argument.
    ("guard_cond_param_970", [0, 0x2A]),
    ("guard_cond_param_970", [1, 0x2A]),
    ("guard_cond_param_970", [0, 0xDEADBEEF]),  # arg == poison: must still match
    ("guard_loop_acc", [0]),
    ("guard_loop_acc", [3]),
]


def die(msg):
    print(f"FATAL: {msg}")
    sys.exit(1)


def compile_fixture(out):
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "--target", "cortex-m4",
         "--relocatable", "--all-exports", "-o", out],
        capture_output=True, text=True,
    )
    if r.returncode != 0:
        die(f"synth compile failed (rc={r.returncode}):\n{r.stdout}\n{r.stderr}")
    return out


def encode_thm_bl(pc, target):
    """Thumb-2 BL: encode (target - (pc+4)) in the S/J1/J2/imm10/imm11 form."""
    off = (target - (pc + 4)) & 0x1FFFFFF
    s = (off >> 24) & 1
    i1, i2 = (off >> 23) & 1, (off >> 22) & 1
    imm10, imm11 = (off >> 12) & 0x3FF, (off >> 1) & 0x7FF
    j1, j2 = (~i1 & 1) ^ s, (~i2 & 1) ^ s
    return 0xF000 | (s << 10) | imm10, 0xD000 | (j1 << 13) | (j2 << 11) | imm11


def load(path):
    """Return (symbols, .text with R_ARM_THM_CALL relocations applied, count)."""
    e = ELFFile(open(path, "rb"))
    symtab = [s for s in e.iter_sections() if s["sh_type"] == "SHT_SYMTAB"][0]
    syms = {s.name: s["st_value"] for s in symtab.iter_symbols() if s.name}
    text = bytearray(e.get_section_by_name(".text").data())

    nrel = 0
    for sec in e.iter_sections():
        if sec["sh_type"] not in ("SHT_REL", "SHT_RELA"):
            continue
        for r in sec.iter_relocations():
            t = r["r_info_type"]
            if t not in (R_ARM_THM_CALL, R_ARM_THM_JUMP24):
                die(f"unexpected reloc type {t}; this harness only resolves THM_CALL")
            name = symtab.get_symbol(r["r_info_sym"]).name
            if name not in syms:
                die(f"reloc names {name!r}, which is not a defined symbol")
            off = r["r_offset"]
            hw1, hw2 = encode_thm_bl(CODE + off, CODE + (syms[name] & ~1))
            struct.pack_into("<HH", text, off, hw1, hw2)
            nrel += 1
    return syms, bytes(text), nrel


def run(syms, text, name, args):
    """Execute one export under unicorn with the sub-SP stack POISONED."""
    addr = syms.get(name)
    if addr is None:
        return None, f"symbol {name} missing from .symtab"
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x20000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STACK_BASE, STACK_SIZE)
    mu.mem_write(CODE, text)
    # POISON the whole region the callee's frame can occupy, so an
    # uninitialised frame-slot read is legible instead of reading as a benign 0.
    mu.mem_write(STACK_BASE, struct.pack("<I", MEM_POISON) * ((SP0 - STACK_BASE) // 4))
    mu.reg_write(UC_ARM_REG_SP, SP0)
    mu.reg_write(UC_ARM_REG_R11, LIN)  # linear-memory base
    for i, a in enumerate(args[:4]):
        mu.reg_write(CORE_ARGS[i], a & M32)
    for i in range(len(args), 4):
        mu.reg_write(CORE_ARGS[i], REG_POISON)
    mu.reg_write(UC_ARM_REG_LR, RET_PAD | 1)
    try:
        mu.emu_start((CODE + (addr & ~1)) | 1, RET_PAD, count=20000)
    except UcError as ex:
        return None, str(ex)
    r0 = mu.reg_read(UC_ARM_REG_R0) & M32
    if name in RET_I64:
        r1 = mu.reg_read(UC_ARM_REG_R1) & M32
        return (r1 << 32) | r0, ""
    return r0, ""


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))

    with tempfile.TemporaryDirectory() as td:
        obj = compile_fixture(os.path.join(td, "bl990_arm.o"))
        syms, text, nrel = load(obj)
    print(f"resolved {nrel} R_ARM_THM_CALL relocation(s) in-process")

    fails = 0
    leaks = 0
    for name, args in CASES:
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        signed = [a - (1 << 32) if a >> 31 else a for a in args]
        mask = M64 if name in RET_I64 else M32
        want = inst.exports(store)[name](store, *signed) & mask
        got, err = run(syms, text, name, args)
        ok = got == want
        fails += 0 if ok else 1
        tag = ""
        if not ok and got is not None and (got & M32) in (
            MEM_POISON, (MEM_POISON + 1) & M32, (MEM_POISON - 1) & M32,
        ):
            leaks += 1
            tag = "   <- POISON (uninitialised stack slot)"
        width = 16 if name in RET_I64 else 8
        shown = f"0x{got:0{width}x}" if got is not None else f"ERR({err})"
        argstr = ", ".join(f"0x{a:x}" for a in args)
        print(f"{'ok ' if ok else 'BUG'} {name}({argstr}): "
              f"want=0x{want:0{width}x} got={shown}{tag}")

    print(f"\n#990 ARM CHECKS={len(CASES) - fails}/{len(CASES)}"
          f"  poison-leaks={leaks}")
    if fails:
        print("#990 ARM br_if-local zero-init ORACLE: FAIL")
    else:
        print("#990 ARM br_if-local zero-init ORACLE: PASS")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
