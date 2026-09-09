#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 1000
"""RQ-66-WATCHED (#1189) — the OPTIMIZED path's i64-result epilogue pair
move, EXECUTED on the self-contained image against wasmtime.

# The gap this closes

`ir_to_arm` lets an i64 result live in any register pair and, in the
function's epilogue, moves the halves into the AAPCS return pair — `mov r1,
<hi>` first (so a lo half already in R1 is not clobbered), then `mov r0,
<lo>`. The v0.65 mutation survey DELETED the hi move and the whole named
suite stayed green: eight self-contained OPTIMIZED-path objects lost a `mov`
and nothing executed one, because every existing i64 differential runs the
RELOCATABLE object — the direct selector, whose epilogue is a different code
path. A caller of such a function reads whatever R1 held: the second
argument, or stack garbage.

# What it does

`i64_result_pair_1189.wat` carries i64-result exports with ONLY i32 params
(an i64 parameter diverts the function to the direct selector via
`has_wide_param`, exactly the path that would not exercise the move): the
#791 const, the #615/#851 extends, the #916 shifts/clz/ctz + popcnt,
carry/borrow/product arithmetic, the #317 software div/rem, and — as
controls that the direct selector lowers instead (RQ-65-DECLINE) — an i64
select, an i64 local and two i64 loads from a data segment. Compiled in the
survey's two self-contained configurations, each image booted through its
own shipped `Reset_Handler`; every export executed under unicorn with R1
POISONED when it is not an argument register (the dropped move returns the
poison), and the R0:R1 pair compared with wasmtime's 64-bit result. A vector
wasmtime traps on (division by zero, an out-of-range load) is never a value
comparison: the image trapping too is `ok-trap`; the image returning is the
compliance envelope (`trap-miss`, recorded — default images emit no
out-of-bounds trap). R9/R10/R11 and SP are checked after every call; a
value MISMATCH outranks a contract violation on the same vector, so a pinned
clobber can never hide a wrong result.

# Known-open, pinned by exact count (red when a count moves either way)

The first run of this fixture on the v0.66 tree found the optimized path's
i64 arithmetic parking pairs in R8:R9 (#1204's class: R9 written and never
saved — `contract` on the default leg for every carry/shift/div shape) and
`i64.popcnt` leaving the sign-extension in the high word (#1240, found by
RQ-66-WATCHED). Both are pinned below so the oracle stays a wrongness
detector for everything else.

# Non-vacuity

Every fixture export must be present in BOTH images' symtabs, the
compared-vector floor is measured, and `# ci-checks: emulations` counts
emulator entries.

# Red-first

The RQ-66-WATCHED PR transcript applies the survey's recorded mutant (the
`arm_instrs.push(ArmOp::Mov { rd: Reg::R1, .. })` deleted, via
`mutation_survey.py`'s Edit context manager) and shows this oracle naming
`const64`, `extend_s`, `shru`, `divs`, ... on the default leg with the
poisoned hi half, then green on the restored tree.

Run (needs wasmtime + unicorn + pyelftools):
  SYNTH=./target/debug/synth python3 scripts/repro/i64_result_pair_1189_differential.py
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

WAT = Path(__file__).with_name("i64_result_pair_1189.wat")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")
M32, M64 = 0xFFFFFFFF, (1 << 64) - 1
LEGS = {
    "self": ["--all-exports", "--target", "cortex-m4"],
    "self-noopt": ["--all-exports", "--target", "cortex-m4", "--no-optimize"],
}
RET = 0x0F00_0000
BOOT_LIMIT = 1_000_000
CALL_LIMIT = 200_000
REG_POISON = 0xFEEDFACE
ARG_REGS = [UC_ARM_REG_R0, UC_ARM_REG_R1, UC_ARM_REG_R2, UC_ARM_REG_R3]

# Shift counts straddling 32 (both arms of the #916 expansions), sign
# boundaries, and a zero divisor (wasmtime traps; the image must too).
ONE = [0, 1, -1, 5, 31, 32, 33, 40, 63, 64, 100, 0x7FFFFFFF, -0x80000000, 0x12345678, -12345, 0xFFFF]
TWO = [(a, b) for a in (0, 1, -1, 7, 0x7FFFFFFF, -0x80000000, 0x12345678) for b in (1, -1, 3, 0, 0x7FFFFFFF, -7)]

# Measured on the v0.66 tree at a73d5ac2: 22 exports, 2 legs, 1,030 vectors
# (54 of them wasmtime traps). Set under the measurement.
COMPARED_FLOOR = 1_000

# (leg, export, kind) -> (issue, exact count). See the docstring.
KNOWN: dict[tuple[str, str, str], tuple[str, int]] = {
    ("self", "popcnt64", "mismatch"): ("#1240", 3),
    ("self", "add64", "contract"): ("#1204", 14),
    ("self", "sub64", "contract"): ("#1204", 19),
    ("self", "mul64", "contract"): ("#1204", 18),
    ("self", "xor64", "contract"): ("#1204", 42),
    ("self", "shl", "contract"): ("#1204", 12),
    ("self", "shru", "contract"): ("#1204", 7),
    ("self", "shrs", "contract"): ("#1204", 16),
    ("self", "divs", "contract"): ("#1204", 11),
    ("self", "rems", "contract"): ("#1204", 6),
}


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

    def at_udf(self) -> bool:
        """unicorn reports the image's inline `udf` as UC_ERR_INSN_INVALID."""
        try:
            pc = self.mu.reg_read(UC_ARM_REG_PC) & ~1
            hw1, hw2 = struct.unpack("<HH", bytes(self.mu.mem_read(pc, 4)))
        except UcError:
            return False
        return (hw1 & 0xFF00) == 0xDE00 or ((hw1 & 0xFFF0) == 0xF7F0 and (hw2 & 0xF000) == 0xA000)

    def call(self, fn: str, words: list[int]):
        """-> ('ok', R0 | R1 << 32) | ('trap',) | ('timeout',) | ('fault', msg), violations"""
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
            if self.at_udf():
                return ("trap",), []
            return ("fault", str(e)), []
        if self.trapped:
            return ("trap",), []
        if (mu.reg_read(UC_ARM_REG_PC) & ~1) != RET:
            return ("timeout",), []
        viol = []
        for r, name in ((UC_ARM_REG_R9, "R9"), (UC_ARM_REG_R10, "R10"), (UC_ARM_REG_R11, "R11")):
            got = mu.reg_read(r) & M32
            if got != self.regs[r]:
                viol.append(f"{name} clobbered: {got:#010x} != {self.regs[r]:#010x}")
        if (mu.reg_read(UC_ARM_REG_SP) & M32) != self.sp0:
            viol.append("SP imbalance")
        return ("ok", (mu.reg_read(UC_ARM_REG_R0) & M32) | ((mu.reg_read(UC_ARM_REG_R1) & M32) << 32)), viol


def to_signed(v: int) -> int:
    v &= M32
    return v - (1 << 32) if v >= (1 << 31) else v


def main() -> int:
    engine = wasmtime.Engine()
    module = wasmtime.Module.from_file(engine, str(WAT))
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, module, [])
    exports = [(e.name, len(e.type.params)) for e in module.exports if isinstance(e.type, wasmtime.FuncType)]
    fails, compared, ok_trap, trap_miss = [], 0, 0, 0
    seen: dict[tuple[str, str, str], int] = {}
    with tempfile.TemporaryDirectory() as td:
        for leg, flags in LEGS.items():
            out = Path(td) / f"i64pair.{leg}.elf"
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
                vecs = [()] if arity == 0 else ([(v,) for v in ONE] if arity == 1 else TWO)
                for args in vecs:
                    try:
                        want = inst.exports(store)[name](store, *[to_signed(a) for a in args]) & M64
                    except wasmtime.Trap:
                        want = None
                    got, viol = img.call(name, [a & M32 for a in args])
                    compared += 1
                    n += 1
                    if want is None:
                        if got[0] == "trap":
                            ok_trap += 1
                        else:
                            trap_miss += 1
                        continue
                    kind = None
                    if got[0] == "ok":
                        if got[1] != want:
                            kind = "mismatch"
                        elif viol:
                            kind = "contract"
                    elif got[0] == "trap":
                        kind = "img-trap"
                    else:
                        kind = got[0]
                    if kind is None:
                        continue
                    key = (leg, name, kind)
                    seen[key] = seen.get(key, 0) + 1
                    if key not in KNOWN:
                        shown = f"{got[1]:#018x}" if got[0] == "ok" else str(got)
                        fails.append(f"{leg}:{name}{tuple(to_signed(a) for a in args)}: {kind} "
                                     f"want={want:#018x} got={shown} {'; '.join(viol)}")
            print(f"  {leg}: {len(exports)} exports, {n} vectors compared")
    for key, (issue, want_n) in sorted(KNOWN.items()):
        have = seen.get(key, 0)
        if have != want_n:
            fails.append(f"PIN MOVED {key} ({issue}): recorded {want_n}, now {have} — "
                         + ("fixed: delete the pin" if have < want_n else "a new instance: file it"))
    if compared < COMPARED_FLOOR:
        fails.append(f"FLOOR: only {compared} vectors compared, floor {COMPARED_FLOOR}")
    for f in fails:
        print(f"FAIL {f}")
    pinned = sum(seen.get(k, 0) for k in KNOWN)
    print(f"#1189 I64PAIR CHECKS={compared - pinned - len([f for f in fails if not f.startswith(('FLOOR', 'PIN'))])}/{compared} "
          f"(ok-trap {ok_trap}, trap-miss {trap_miss}, pinned {pinned})")
    print("RESULT: " + ("PASS" if not fails else f"FAIL ({len(fails)})"))
    return 0 if not fails else 1


if __name__ == "__main__":
    sys.exit(main())
