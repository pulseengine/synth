#!/usr/bin/env python3
"""#490 (epic #242) — EXECUTION-validate optimized-path callee-saved preservation.

The optimized ARM path (the default, non-`--relocatable` self-contained image)
uses r4-r8 as scratch / promoted locals but emitted NO prologue, silently
clobbering a caller's callee-saved registers — a systemic AAPCS violation. The
fix wraps a body that genuinely touches r4-r8 in `push {r4-r8,lr}` /
`pop {r4-r8,pc}` (sized down by `shrink_callee_saved_saves`).

This harness compiles the fixture via the OPTIMIZED path (no `--relocatable`),
runs each exported function under unicorn (UC_ARCH_ARM / Thumb) with r4-r8 set to
distinct SENTINELS, and asserts:
  1. the result matches wasmtime ground truth (computation unchanged), and
  2. every callee-saved register r4-r8 is RESTORED to its sentinel at return
     (the actual AAPCS property #490 fixes).

NON-VACUITY: each function's machine code must contain a `push {...,lr}` /
`pop {...,pc}` pair (else there is nothing preserving the sentinels and the
check is trivially true). A function that touches no callee-saved register is
exempt — but both fixtures are constructed to use them.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python scripts/repro/callee_saved_490_differential.py
Exits nonzero on any mismatch, clobbered sentinel, or vacuity failure.
"""
import os
import subprocess
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
    UC_ARM_REG_R4,
    UC_ARM_REG_R5,
    UC_ARM_REG_R6,
    UC_ARM_REG_R7,
    UC_ARM_REG_R8,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("callee_saved_490.wat")
SYNTH = os.environ.get("SYNTH", "./target/release/synth")
CS_REGS = [
    (UC_ARM_REG_R4, "r4", 0xCA5E0004),
    (UC_ARM_REG_R5, "r5", 0xCA5E0005),
    (UC_ARM_REG_R6, "r6", 0xCA5E0006),
    (UC_ARM_REG_R7, "r7", 0xCA5E0007),
    (UC_ARM_REG_R8, "r8", 0xCA5E0008),
]
ARG_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]
# (name, [argument vectors]); each vector is masked to u32 going in.
CASES = {
    "low": [(0,), (1,), (100,), (0x7FFFFFFF,), (0xFFFFFFFF,)],
    "mid": [(0, 0), (1, 2), (3000, 50), (0x7FFFFFFF, 1), (0xFFFFFFFF, 0x80000000)],
    "wide": [(0, 0, 0), (1, 2, 3), (3000, 50, 7), (0x7FFFFFFF, 1, 2),
             (0xFFFFFFFF, 0x80000000, 5)],
}


def compile_optimized(out):
    """Compile via the optimized path (NO --relocatable) — the path #490 fixes.

    Forwards the range-realloc / dead-frame-elim knobs so the prologue wrap can
    be exercised in every configuration that reaches it: default (realloc-on →
    shrink trims), `SYNTH_RANGE_REALLOC=0` (no shrink → full save kept), and
    `SYNTH_DEAD_FRAME_ELIM=1`."""
    env = {"PATH": "/usr/bin:/bin"}
    for k in ("SYNTH_RANGE_REALLOC", "SYNTH_DEAD_FRAME_ELIM"):
        if k in os.environ:
            env[k] = os.environ[k]
    r = subprocess.run(
        [SYNTH, "compile", str(WAT), "-o", out, "--target", "cortex-m4",
         "--all-exports"],
        capture_output=True, text=True, env=env,
    )
    if r.returncode != 0:
        sys.exit(f"compile failed: {r.stderr}")


def load(elf):
    f = ELFFile(open(elf, "rb"))
    text = f.get_section_by_name(".text")
    data, base = text.data(), text["sh_addr"]
    syms = {}
    for s in f.iter_sections():
        if s.header.sh_type == "SHT_SYMTAB":
            for sym in s.iter_symbols():
                if sym.name:
                    syms[sym.name] = sym["st_value"]
    return data, base, syms


def has_push_pop(code, off, limit=256):
    """Structural non-vacuity: the function at byte `off` contains a prologue
    PUSH and an epilogue POP. Recognises both the 16-bit Thumb forms (PUSH
    {...,lr} = 0xB5xx, POP {...,pc} = 0xBDxx) and the 32-bit Thumb-2 wide forms
    the assembler must use when the list includes a high register such as r8
    (PUSH.W = 0xE92D <list>, POP.W = 0xE8BD <list>)."""
    push = pop = False
    i = off
    end = min(off + limit, len(code))
    while i + 1 < end:
        hw = code[i] | (code[i + 1] << 8)
        if (hw & 0xFF00) == 0xB500 or hw == 0xE92D:  # PUSH / PUSH.W
            push = True
        if (hw & 0xFF00) == 0xBD00 or hw == 0xE8BD:  # POP {pc} / POP.W
            pop = True
            break
        i += 2
    return push and pop


def main():
    if not os.path.exists(SYNTH):
        sys.exit(f"{SYNTH} not found — build synth first")
    elf = "/tmp/cs490.elf"
    compile_optimized(elf)
    code, base, syms = load(elf)

    eng = wasmtime.Engine()
    mod = wasmtime.Module(eng, WAT.read_bytes())
    st = wasmtime.Store(eng)
    inst = wasmtime.Instance(st, mod, [])

    CODE_LO, CODE_HI = base & ~0xFFFF, 0x20000
    STK = 0x90000
    RET = STK + 0x100
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE_LO, CODE_HI)
    mu.mem_write(base, code)
    mu.mem_map(STK, 0x10000)
    mu.mem_write(RET, b"\x00\xbf\x00\xbf")  # nop; nop landing pad

    fails = 0
    for name, vectors in CASES.items():
        addr = syms[name]
        foff = (addr - base) & ~1
        if not has_push_pop(code, foff):
            print(f"VACUOUS: {name} has no push/pop pair — nothing preserves "
                  "the callee-saved sentinels")
            fails += 1
            continue
        export = inst.exports(st)[name]
        for vec in vectors:
            signed = [v - (1 << 32) if v >= 1 << 31 else v for v in vec]
            exp = export(st, *signed) & 0xFFFFFFFF
            for r in ARG_REGS:
                mu.reg_write(r, 0)
            for r, v in zip(ARG_REGS, vec):
                mu.reg_write(r, v & 0xFFFFFFFF)
            for reg, _, sentinel in CS_REGS:
                mu.reg_write(reg, sentinel)
            mu.reg_write(UC_ARM_REG_SP, STK + 0x8000)
            mu.reg_write(UC_ARM_REG_LR, RET | 1)
            mu.emu_start(addr | 1, RET, timeout=5_000_000)
            got = mu.reg_read(UC_ARM_REG_R0)
            clobbered = [
                nm for reg, nm, sentinel in CS_REGS
                if mu.reg_read(reg) != sentinel
            ]
            ok = got == exp and not clobbered
            if not ok:
                fails += 1
            tag = "OK  " if ok else "FAIL"
            detail = f"= {got:#010x} expect {exp:#010x}"
            if clobbered:
                detail += f"  CLOBBERED {','.join(clobbered)}"
            print(f"{tag} {name}{vec} {detail}")

    print("ORACLE:", "PASS" if fails == 0 else f"FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
