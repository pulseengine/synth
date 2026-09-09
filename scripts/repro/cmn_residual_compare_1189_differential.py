#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 2500
"""RQ-66-WATCHED (#1189) — the direct selector's hand-written `cmn` residual,
EXECUTED against wasmtime on both self-contained legs.

# The gap this closes

`select_with_stack` lowers an i32 comparison whose right operand is an
immediately-preceding `i32.const c`, c in [-0xFF, -1], as `cmn a, #|c|`
followed by a hand-written `SetCond dst, <cond>` — the NEGATIVE half of the
immediate fold. The positive half and the reg-reg path are Rocq-proved
`sel_dsl` rules; this residual is not (its add-derived NZCV needs a sub<->add
flag-correspondence lemma family the model does not carry), and until this
oracle nothing executed it. The v0.65 mutation survey inverted
`I32Eq => Condition::EQ` in that table and the entire named suite stayed
green: the only corpus object that changed was gust_kernel's `x == -1`
sentinel check inside `gust_poll`, which nothing executes. RQ-65-PARITY had
predicted the region from the other direction.

# What it does

`cmn_residual_compare_1189.wat` carries all ten conditions at three
magnitudes (-1, the gust_poll sentinel; -37; -255, the fold boundary), the
SetCond value consumed arithmetically and as a select condition, and controls
on the two PROVED paths (positive immediate, reg-reg) plus the -256 just
outside the byte fold. It is compiled in the survey's two self-contained
configurations — `--no-optimize` (every function on the direct selector: the
leg the residual lives on) and the default (the optimized path's own compare
lowering, so the two shipped selectors are held to the same values) — each
image is booted through its own shipped `Reset_Handler`, and every export is
executed under unicorn on a boundary-heavy vector set straddling each
magnitude, against wasmtime.

# Non-vacuity

Every fixture export must be present in BOTH images' symtabs (a function one
leg declined would silently vanish from the comparison), the compared-vector
floor is measured, and `# ci-checks: emulations` counts emulator entries.

# Red-first

The RQ-66-WATCHED PR transcript applies the survey's recorded mutant
(`I32Eq => Condition::EQ` -> `NE`, `mutation_survey.py`'s Edit context
manager) and shows this oracle naming `eq_m1` / `eq_m37` / `eq_m255` /
`used_eq_m1` / `sel_eq_m1` on the `--no-optimize` leg with the two values,
then green on the restored tree.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/cmn_residual_compare_1189_differential.py
"""

from __future__ import annotations

import os
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_HOOK_CODE, UC_HOOK_INTR, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R3,
    UC_ARM_REG_R9,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WAT = Path(__file__).with_name("cmn_residual_compare_1189.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
M32 = 0xFFFFFFFF
LEGS = {
    "self-noopt": ["--all-exports", "--target", "cortex-m4", "--no-optimize"],
    "self": ["--all-exports", "--target", "cortex-m4"],
}
RET = 0x0F00_0000
BOOT_LIMIT = 1_000_000
CALL_LIMIT = 100_000
REG_POISON = 0xFEEDFACE
ARG_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]

# Straddles every magnitude the fixture uses (1, 5, 9, 37, 200, 255, 256):
# the value itself, both neighbours, zero, the signed extremes, and values
# whose SIGNED and UNSIGNED orderings against a negative immediate differ.
VECTORS = [
    0, 1, -1, -2, 2,
    -4, -5, -6, -8, -9, -10,
    -36, -37, -38, 37, 36,
    -199, -200, -201, 200,
    -254, -255, -256, -257, 255, 256,
    0x7FFFFFFF, -0x80000000, 0x7FFFFF00, 0x80000001 - (1 << 32), 0x12345678, -0x12345678,
]
PAIRS = [(a, b) for a in (0, 1, -1, -37, 37, 0x7FFFFFFF, -0x80000000) for b in (-1, -37, 0, 37, 0x7FFFFFFF)]

# Measured on the v0.66 tree at a73d5ac2: 41 exports, 2 legs, 2,636 vectors;
# set under the measurement.
COMPARED_FLOOR = 2_500


class Image:
    def __init__(self, elf_path: Path):
        with elf_path.open("rb") as fh:
            elf = ELFFile(fh)
            st = next(s for s in elf.iter_sections() if s["sh_type"] == "SHT_SYMTAB")
            self.syms = {s.name: s["st_value"] for s in st.iter_symbols() if s.name}
            segs = [(sg["p_vaddr"], sg["p_memsz"], sg.data())
                    for sg in elf.iter_segments() if sg["p_type"] == "PT_LOAD"]
        text_va, _, text = min(segs, key=lambda s: s[0])
        sp0, reset = struct.unpack_from("<II", text, 0)
        self.sp0 = sp0
        ram = [(va, sz) for va, sz, _ in segs if va != text_va]
        self.ram_lo = min((va for va, _ in ram), default=sp0 - 0x20000) & ~0xFFF
        ram_hi = max(sp0, max((va + sz for va, sz in ram), default=0))
        self.ram_hi = (ram_hi + 0xFFF) & ~0xFFF
        self.mu = mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
        text_lo = text_va & ~0xFFF
        mu.mem_map(text_lo, ((text_va + len(text) + 0xFFF) & ~0xFFF) - text_lo)
        mu.mem_write(text_va, text)
        mu.mem_map(self.ram_lo, self.ram_hi - self.ram_lo)  # zeroed: only the reset path populates it
        mu.mem_map(RET & ~0xFFF, 0x1000)
        mu.mem_map(0xE000E000, 0x1000)
        self.trapped = False
        trap = self.syms.get("Trap_Handler", 0) & ~1

        def on_trap(uc, *_):
            self.trapped = True
            uc.emu_stop()

        if trap:
            mu.hook_add(UC_HOOK_CODE, on_trap, begin=trap, end=trap + 1)
        mu.hook_add(UC_HOOK_INTR, on_trap)
        pc = reset & ~1
        while True:
            hw = struct.unpack_from("<H", text, pc - text_va)[0]
            if hw == 0x4780:
                break
            pc += 4 if (hw >> 11) in (0b11101, 0b11110, 0b11111) else 2
        mu.reg_write(UC_ARM_REG_SP, sp0)
        mu.emu_start(reset | 1, pc, count=BOOT_LIMIT)
        if (mu.reg_read(UC_ARM_REG_PC) & ~1) != pc or self.trapped:
            sys.exit(f"boot did not reach the entry scaffold (pc={mu.reg_read(UC_ARM_REG_PC):#x})")
        self.regs = {r: mu.reg_read(r) & M32 for r in (UC_ARM_REG_R9, UC_ARM_REG_R10, UC_ARM_REG_R11)}
        self.snap = bytes(mu.mem_read(self.ram_lo, self.ram_hi - self.ram_lo))

    def call(self, fn: str, words: list[int]):
        mu = self.mu
        mu.mem_write(self.ram_lo, self.snap)
        for r, v in self.regs.items():
            mu.reg_write(r, v)
        for i, r in enumerate(ARG_REGS):
            mu.reg_write(r, (words[i] & M32) if i < len(words) else REG_POISON)
        mu.reg_write(UC_ARM_REG_SP, self.sp0)
        mu.reg_write(UC_ARM_REG_LR, RET | 1)
        self.trapped = False
        try:
            mu.emu_start(self.syms[fn] | 1, RET, count=CALL_LIMIT)
        except UcError as e:
            return f"fault:{e}"
        if self.trapped or (mu.reg_read(UC_ARM_REG_PC) & ~1) != RET:
            return "trap" if self.trapped else "timeout"
        for r, name in ((UC_ARM_REG_R9, "R9"), (UC_ARM_REG_R10, "R10"), (UC_ARM_REG_R11, "R11")):
            if (mu.reg_read(r) & M32) != self.regs[r]:
                return f"contract:{name}"
        if (mu.reg_read(UC_ARM_REG_SP) & M32) != self.sp0:
            return "contract:SP"
        return mu.reg_read(UC_ARM_REG_R0) & M32


def to_signed(v: int) -> int:
    v &= M32
    return v - (1 << 32) if v >= (1 << 31) else v


def main() -> int:
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    exports = [(e.name, len(e.type.params)) for e in module.exports if isinstance(e.type, wasmtime.FuncType)]
    fails, compared = [], 0
    with tempfile.TemporaryDirectory() as td:
        for leg, flags in LEGS.items():
            out = Path(td) / f"cmn.{leg}.elf"
            r = subprocess.run([SYNTH, "compile", str(WAT), *flags, "-o", str(out)],
                               capture_output=True, text=True)
            if r.returncode != 0:
                print(f"RESULT: FAIL — {leg} did not compile: {r.stderr[-300:]}")
                return 1
            img = Image(out)
            missing = [n for n, _ in exports if n not in img.syms]
            if missing:
                fails.append(f"{leg}: exports missing from the image: {missing}")
                continue
            n = 0
            for name, arity in exports:
                vecs = [(v,) for v in VECTORS] if arity == 1 else PAIRS
                for args in vecs:
                    want = inst.exports(store)[name](store, *[to_signed(a) for a in args]) & M32
                    got = img.call(name, [a & M32 for a in args])
                    compared += 1
                    n += 1
                    if got != want:
                        fails.append(f"{leg}:{name}{tuple(to_signed(a) for a in args)}: want={want:#x} got={got if isinstance(got, str) else hex(got)}")
            print(f"  {leg}: {len(exports)} exports, {n} vectors compared")
    if compared < COMPARED_FLOOR:
        fails.append(f"FLOOR: only {compared} vectors compared, floor {COMPARED_FLOOR}")
    for f in fails:
        print(f"FAIL {f}")
    print(f"#1189 CMN CHECKS={compared - len([f for f in fails if not f.startswith('FLOOR')])}/{compared}")
    print("RESULT: " + ("PASS" if not fails else f"FAIL ({len(fails)})"))
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
