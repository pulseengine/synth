#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 38
"""#970 — ARM: a CONDITIONALLY-written parameter must keep its incoming argument.

Same defect as the RV32 sibling oracle, different symptom. `count_params`
(`arm_backend.rs`) counted only local indices READ BEFORE WRITTEN in LINEAR op
order, so a parameter written on ONE arm of an `if` was demoted to a non-param
local and its incoming argument register was forgotten.

ARM's symptom was NOT assumed from the RV32 one — it was MEASURED here, and the
measurement corrected the expectation. #970 predicted ARM would return param
0's value (an ordinary wrong value) because the demoted local's store looked, in
a flat disassembly listing, like it sat at the branch MERGE point. It does not:
the conditional branch jumps PAST it. Measured on cb80e60c, `--target cortex-m4
--relocatable`, `cond_write_param` lowers to

    push.w {r4, r5, r6, r7, r8, lr}
    sub.w  sp, sp, #8
    cmp    r0, #0
    beq    +8            ; -> the ldr, skipping the store below
    movw   r1, #5
    str.w  r1, [sp]      ; INSIDE the then-arm, not at the merge point
    ldr.w  r2, [sp]      ; <- on the fall-through path this slot was NEVER written
    mov    r0, r2

so ARM has the SAME uninitialised-frame-slot read as RV32, i.e. the same
information-disclosure shape, on the plain shape as well as the call one. The
`cw_call*` cases stay as separate evidence because they are the shape #970
reasoned about, and because their store is fed by a call-clobbered `r0`.

Two DISTINCT poison words make the mechanism provable rather than inferred:
every stack word below the entry SP is 0xDEADBEEF and every argument register
the signature does not use is 0xFEEDFACE, so "read an uninitialised slot" and
"read the wrong argument register" cannot be confused for one another.

Ground truth is wasmtime on the same `.wat`. Symbols come from the ELF
`.symtab`, never `synth disasm` text (host-dependent). The two `R_ARM_THM_CALL`
relocations to the in-module callees are resolved in-process by re-encoding the
BL, exactly as `ld` would.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/cond_write_param_970_arm_differential.py
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

WAT = Path(__file__).with_name("cond_write_param_970.wat")
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

# (export, args) — the same matrix the RV32 sibling runs, so the two backends'
# evidence is directly comparable while staying independently measured.
CASES = [
    ("cond_write_param", [0, 0x2A]),
    ("cond_write_param", [1, 0x2A]),
    ("cond_write_param", [0, 0x07]),
    ("cond_write_param", [0, 0x11112222]),
    ("cond_write_param", [0, 0xFFFFFFFF]),
    ("cond_write_param", [0, 0]),
    # The shape #970 reasoned about for ARM: the written value comes from a
    # call, so `bl` has clobbered r0-r3 by the time the slot is read.
    ("cw_call", [0, 0x2A]),
    ("cw_call", [1, 0x2A]),
    ("cw_call", [0, 0xABCDEF01]),
    ("cw_call_arg", [0, 0x2A]),
    ("cw_call_arg", [1, 0x2A]),
    ("cw_call_arg", [0, 0x7FFFFFFF]),
    ("cw_tee", [0, 0x2A]),
    ("cw_tee", [1, 0x2A]),
    ("cw_tee", [0, 0x80000000]),
    ("cw_brif", [0, 0x2A]),
    ("cw_brif", [1, 0x2A]),
    ("cw_brif", [0, 0xDEADBEEF]),
    ("cw_loop", [0, 0x2A]),
    ("cw_loop", [3, 0x2A]),
    ("cw_loop", [0, 0xFFFFFFFF]),
    ("cw_last_of_three", [0, 3, 4]),
    ("cw_last_of_three", [1, 3, 4]),
    ("cw_last_of_three", [0, 0x10, 0xFFFF]),
    # Six params: indices 4 and 5 are AAPCS STACK-passed on ARM, so this is the
    # case where `min(referenced, declared)` WIDENS the count — index 5 must be
    # read from the caller's frame, not from a zero-init local slot.
    ("cw_high_param", [0, 1, 2, 3, 4, 5]),
    ("cw_high_param", [1, 1, 2, 3, 4, 5]),
    ("cw_high_param", [0, 9, 9, 9, 0x1000, 0x2000]),
    # ── guards: the shapes the fix must NOT change ────────────────────────────
    ("guard_rbw_local", [7]),  # #457: non-param local reads the mandated 0
    ("guard_rbw_local", [0]),
    ("guard_rbw_local", [0xFFFFFFFF]),
    ("guard_rbw_local_mixed", [0, 0x2A]),
    ("guard_rbw_local_mixed", [1, 0x2A]),
    ("guard_both_arms", [0, 0x2A]),
    ("guard_both_arms", [1, 0x2A]),
    ("guard_write_then_read", [3, 0x2A]),
    ("guard_write_then_read", [0, 0]),
    ("guard_plain_params", [11, 31]),
    ("guard_plain_params", [0xFFFFFFFF, 1]),
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
    # AAPCS: args 0..3 in r0..r3, the rest on the incoming stack from [sp,#0].
    for i, a in enumerate(args[:4]):
        mu.reg_write(CORE_ARGS[i], a & M32)
    for i in range(len(args), 4):
        mu.reg_write(CORE_ARGS[i], REG_POISON)  # unused arg regs carry a DISTINCT poison
    for k, a in enumerate(args[4:]):
        mu.mem_write(SP0 + 4 * k, struct.pack("<I", a & M32))
    mu.reg_write(UC_ARM_REG_LR, RET_PAD | 1)
    try:
        mu.emu_start((CODE + (addr & ~1)) | 1, RET_PAD, count=20000)
    except UcError as ex:
        return None, str(ex)
    return mu.reg_read(UC_ARM_REG_R0) & M32, ""


def main():
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))

    with tempfile.TemporaryDirectory() as td:
        obj = compile_fixture(os.path.join(td, "cw970_arm.o"))
        syms, text, nrel = load(obj)
    print(f"resolved {nrel} R_ARM_THM_CALL relocation(s) in-process")

    fails = 0
    leaks = 0
    for name, args in CASES:
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        want = inst.exports(store)[name](store, *[a - (1 << 32) if a >> 31 else a
                                                  for a in args]) & M32
        got, err = run(syms, text, name, args)
        ok = got == want
        fails += 0 if ok else 1
        tag = ""
        if got == MEM_POISON and not ok:
            leaks += 1
            tag = "   <- POISON (uninitialised stack slot)"
        shown = f"0x{got:08x}" if got is not None else f"ERR({err})"
        argstr = ", ".join(f"0x{a:x}" for a in args)
        print(f"{'ok ' if ok else 'BUG'} {name}({argstr}): "
              f"want=0x{want:08x} got={shown}{tag}")

    print(f"\n#970 ARM CHECKS={len(CASES) - fails}/{len(CASES)}"
          f"  poison-leaks={leaks}")
    if fails:
        print("#970 ARM conditional-param-write ORACLE: FAIL")
    else:
        print("#970 ARM conditional-param-write ORACLE: PASS")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
