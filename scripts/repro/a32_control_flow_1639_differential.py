#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 905
"""#1639 / #1641 — A32 control-flow execution differential (unicorn vs wasmtime).

WHAT WAS WRONG (measured at v0.89.0 dd2b791a and main df847a16):

  * #1639: on the A32 path (`--target cortex-r5`, and every ARM build with no
    `--target`, whose default ISA is Arm32) the local label branches
    (`B`/`Bcc`/`Bhs`/`Blo`) were never resolved. `arm_backend` ran the label
    resolver only under `use_thumb2`; the A32 encoder emitted its placeholder
    words (`<cond>A000000`, i.e. `b pc+8`) and no relocation patched them.
    `br_if` landed one instruction past itself, a loop back-edge became a
    forward skip, `br_table`/`if`/`else` took the wrong arm. Exit 0.
  * #1641: the NUMERIC branches the selectors write (`--safety-bounds
    software` guard skips, and — found by this oracle's author while fixing
    #1639 — the i32 div/rem trap guards and the optimized path's pre-resolved
    branches) are in THUMB units, `(target - branch - 4) / 2` halfwords. The
    A32 encoder reads the same field as `(target - branch) / 4` words, so the
    guards' `offset: 0` encoded as a branch to ITSELF: every guarded load, and
    every `i32.div_u`/`div_s`/`rem_u`/`rem_s` with a non-zero runtime divisor,
    spun forever on A32.

THE FIX this gates: `arm_backend::resolve_a32_branches` resolves label
branches against A32 positions and RETARGETS numeric branches (Thumb offset ->
target instruction, by the real Thumb-2 encoder's sizes -> A32 word offset);
`validate_a32_branch_targets` then refuses any surviving label branch, any
target that is not an A32 instruction start, and any imm24 overflow.

THE ORACLE. Two fixtures, every export `(i32, i32) -> i32`:

  * `a32_control_flow_1639.wat` — block/br_if, loop back-edges (incl. nested
    and a do-while whose only back-edge is conditional), br_table, if/else, a
    call inside a loop, a value-carrying block, two params-only shapes the
    OPTIMIZED path accepts, and the four i32 div/rem trap guards.
  * `a32_safety_bounds_1641.wat` — guarded i32 and byte accesses, in bounds
    and out of bounds, with and without a static offset, one inside a loop.
  * `optloop_backedge_1206.wat` (shared with the Thumb-2 #1206 oracle) — the
    eight OPTIMIZED-path loops whose back-edges are numeric branches the
    size estimator places before encoding (#1206's countdown, count-up and
    count-down by const and by param, from zero, a memory.size bound, and
    the R7 control). On A32 those
    back-edges are the #1641 unit class: before this fix every one of them
    left its function on cortex-r5 (v0.89.2 cold review, F3).

compiled on these legs, every vector executed under unicorn and compared with
wasmtime (fresh instance and fresh zeroed memory per vector on both sides):

  a32 r5-rel      `-b arm --target cortex-r5 --relocatable`   (direct selector)
  a32 notgt-rel   `-b arm --relocatable` (no target -> Arm32)  (direct selector)
  a32 r5-image    `-b arm --target cortex-r5` self-contained   (OPTIMIZED path
                  where it accepts). The image is NOT BOOTED: #1640 (its
                  symbols and entry carry the Thumb bit) is out of scope, so
                  `.text` is mapped at its address and entered at
                  `symbol & ~1` in ARM state. The no-target self-contained
                  build is not a leg: since #1640 every no-target
                  self-contained image is refused (A32 bodies behind a
                  Cortex-M Thumb startup cannot run).
  a32 r5-sb       cortex-r5 --relocatable --safety-bounds software (#1641)
  a32 r5-image-1206
                  `optloop_backedge_1206.wat`, self-contained cortex-r5,
                  entered at `symbol & ~1` like r5-image. Every export must
                  compile on the OPTIMIZED path (SYNTH_PATH_DEBUG), or the leg
                  would stop exercising the estimator-resolved branches it
                  exists for; 80 vectors per export, the Thumb oracle's set,
                  R10 = one page for msize_loop. Its no-target twin
                  (notgt-image-1206) was DROPPED with #1640: that image is now
                  refused, and before the refusal its eight function bodies
                  were byte-identical to this leg's (measured on f28f29b0), so
                  retargeting it to cortex-r5 would have run this leg twice.
  a32 notgt-sb    no-target --relocatable --safety-bounds software (#1641)
  thumb m4-rel / m4-sb   cortex-m4 controls: correct before and after, so a
                  red A32 leg is the A32 path and not the harness.

The relocatable objects are LINKED with arm-none-eabi-ld (hard-failing on any
diagnostic), so the `bl` inside `callsum` executes through a real relocation.
A wasmtime trap must be matched by the emulator reaching a `udf` (the trap
lowering); a hang (instruction budget exhausted) or any other fault where
wasmtime returned is a FAIL, as is any value disagreement.

Run (rebuild synth first):
  python3 scripts/repro/a32_control_flow_1639_differential.py
  SYNTH=path/to/synth python3 scripts/repro/a32_control_flow_1639_differential.py
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_PC,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R10,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

ROOT = Path(__file__).resolve().parents[2]
CF = ROOT / "scripts/repro/a32_control_flow_1639.wat"
SB = ROOT / "scripts/repro/a32_safety_bounds_1641.wat"
OPT = ROOT / "scripts/repro/optloop_backedge_1206.wat"
OPT_EXPORTS = ("countdown", "up_const", "up_param", "down_param", "down_const",
               "up_from_zero", "msize_loop", "countdown_r7")
SYNTH = os.environ.get("SYNTH", "./target/debug/synth")

M32 = (1 << 32) - 1
INT_MIN = 0x80000000
TEXT_BASE = 0x10000
MEM_BASE, MEM_SIZE = 0x20000000, 0x10000   # R11 / R10 under --relocatable
STK_BASE, STK_SIZE = 0x30000000, 0x10000
RET = STK_BASE + STK_SIZE - 0x100
BUDGET = 200000  # instructions; the longest vector here runs a few thousand

CF_VECTORS = [
    ("f", 0, 0), ("f", 1, 0), ("f", 7, 0),
    ("sum", 0, 0), ("sum", 1, 0), ("sum", 3, 0), ("sum", 10, 0),
    ("tbl", 0, 0), ("tbl", 1, 0), ("tbl", 2, 0), ("tbl", 9, 0), ("tbl", M32, 0),
    ("ife", 0, 0), ("ife", 1, 0), ("ife", 5, 0),
    ("nest", 0, 0), ("nest", 3, 0), ("nest", 3, 4), ("nest", 7, 5), ("nest", 4, 1),
    ("callsum", 0, 0), ("callsum", 1, 0), ("callsum", 4, 0), ("callsum", 9, 0),
    ("dowhile", 0, 0), ("dowhile", 1, 0), ("dowhile", 6, 0),
    ("blkval", 5, 3), ("blkval", 3, 5), ("blkval", 4, 4), ("blkval", 9, 2),
    ("optloop", 0, 7), ("optloop", 1, 7), ("optloop", 5, 7), ("optloop", 0x30, 3),
    ("optif", 2, 9), ("optif", 9, 2), ("optif", 5, 5),
    ("du", 17, 5), ("du", M32, 2), ("du", 3, 0), ("du", 0, 1),
    ("ds", 17, 5), ("ds", (-17) & M32, 5), ("ds", INT_MIN, M32), ("ds", INT_MIN, 1),
    ("ds", 3, 0), ("ds", INT_MIN, 2),
    ("ru", 17, 5), ("ru", M32, 7), ("ru", 3, 0),
    ("rs", (-17) & M32, 5), ("rs", INT_MIN, M32), ("rs", 3, 0), ("rs", 17, (-5) & M32),
]
SB_VECTORS = [
    ("ld", 0, 0), ("ld", 8, 0), ("ld", 0xFFFC, 0), ("ld", 0xFFFD, 0),
    ("ld", 0x10000, 0), ("ld", 0x7FFFFFFF, 0),
    ("rt", 0, 0x11223344), ("rt", 0x100, 5), ("rt", 0xFFF8, 0xCAFE),
    ("rt", 0xFFF9, 1), ("rt", 0x10000, 1),
    ("bytes", 0, 0x20000), ("bytes", 5, 100), ("bytes", 4, 0xFFFC),
    ("bytes", 3, 0xFFFE),
]

# The Thumb #1206 oracle's vector set, (a, b); a one-param export ignores b.
OPT_VECTORS = [(fn, a, b) for fn in OPT_EXPORTS
               for a in (0, 1, 2, 5, 9, 10, 15, 37, 100, 200)
               for b in (0, 1, 3, 9, 10, 64, 100, 200)]

# The image leg's SCOPE, a positive list: what it exists to execute is the
# OPTIMIZED path's numeric (Thumb-unit) branches retargeted to A32, which only
# a non-relocatable build reaches. `callsum` (a call inside a loop) joined
# this list with #1645: the self-contained A32 builder now patches its `bl`
# (it shipped as a `bl` to itself before), so the image leg executes the
# loop's branches and the patched call together.
IMAGE_LEG_EXPORTS = (
    "f", "sum", "tbl", "ife", "nest", "dowhile", "blkval",
    "optloop", "optif", "du", "ds", "ru", "rs", "callsum",
)

# (name, fixture, synth flags, execution kind)
LEGS = [
    ("a32 r5-rel", CF, ["-b", "arm", "--target", "cortex-r5", "--relocatable"], "a32"),
    ("a32 notgt-rel", CF, ["-b", "arm", "--relocatable"], "a32"),
    ("a32 r5-image (entered at symbol, not booted)", CF,
     ["-b", "arm", "--target", "cortex-r5"], "a32-image"),
    ("a32 r5-sb", SB, ["-b", "arm", "--target", "cortex-r5", "--relocatable",
                       "--safety-bounds", "software"], "a32"),
    ("a32 notgt-sb", SB, ["-b", "arm", "--relocatable",
                          "--safety-bounds", "software"], "a32"),
    ("a32 r5-image-1206 (entered at symbol, not booted)", OPT,
     ["-b", "arm", "--target", "cortex-r5"], "a32-image"),
    ("thumb m4-rel (control)", CF,
     ["-b", "arm", "--target", "cortex-m4", "--relocatable"], "thumb"),
    ("thumb m4-sb (control)", SB, ["-b", "arm", "--target", "cortex-m4",
                                   "--relocatable", "--safety-bounds", "software"],
     "thumb"),
]


def truth(fixture, fn, a, b):
    engine = wasmtime.Engine()
    store = wasmtime.Store(engine)
    inst = wasmtime.Instance(store, wasmtime.Module(engine, fixture.read_text()), [])
    f = inst.exports(store)[fn]
    args = [a & M32 if a < INT_MIN else a - (1 << 32),
            b if b < INT_MIN else b - (1 << 32)][:len(f.type(store).params)]
    try:
        return f(store, *args) & M32
    except wasmtime.Trap:
        return "TRAP"


def need(tool):
    p = shutil.which(tool)
    if p is None:
        sys.exit(f"FAIL: {tool} not found — a skipped link is a vacuous gate")
    return p


def compile_leg(fixture, flags, out):
    cmd = [SYNTH, "compile", str(fixture), "-o", out, "--all-exports", *flags]
    r = subprocess.run(cmd, capture_output=True, text=True,
                       env={**os.environ, "SYNTH_PATH_DEBUG": "1"})
    log = r.stdout + r.stderr
    optimized = {int(i) for i in re.findall(
        r"\[path-debug\] optimized \(ir_to_arm ok\) func=(\d+)", log)}
    return r.returncode, log[-2000:], optimized


def link(obj, out, entry):
    cmd = [need("arm-none-eabi-ld"), "-e", entry,
           f"-Ttext={TEXT_BASE:#x}", obj, "-o", out]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0 or r.stderr.strip():
        return r.stderr.strip() or f"exit {r.returncode}"
    return None


def load(path):
    with open(path, "rb") as fh:
        e = ELFFile(fh)
        t = e.get_section_by_name(".text")
        syms = {}
        for s in e.iter_sections():
            if s["sh_type"] != "SHT_SYMTAB":
                continue
            for sy in s.iter_symbols():
                if sy.name and sy["st_info"]["type"] == "STT_FUNC" \
                        and sy["st_shndx"] != "SHN_UNDEF":
                    syms[sy.name] = sy["st_value"]
        return t.data(), t["sh_addr"], syms


EMULATIONS = 0


def emulate(text, base, addr, a, b, thumb):
    global EMULATIONS
    uc = Uc(UC_ARCH_ARM, UC_MODE_THUMB if thumb else UC_MODE_ARM)
    page = base & ~0xFFF
    uc.mem_map(page, (len(text) + (base - page) + 0xFFF) & ~0xFFF or 0x1000)
    uc.mem_write(base, text)
    uc.mem_map(MEM_BASE, MEM_SIZE)
    uc.mem_map(STK_BASE, STK_SIZE)
    uc.reg_write(UC_ARM_REG_SP, RET)
    uc.reg_write(UC_ARM_REG_LR, (RET | 1) if thumb else RET)
    uc.reg_write(UC_ARM_REG_R0, a & M32)
    uc.reg_write(UC_ARM_REG_R1, b & M32)
    uc.reg_write(UC_ARM_REG_R2, 0x1234)  # sentinel: a result read from an unwritten reg
    uc.reg_write(UC_ARM_REG_R10, MEM_SIZE)
    uc.reg_write(UC_ARM_REG_R11, MEM_BASE)
    EMULATIONS += 1
    try:
        uc.emu_start((addr | 1) if thumb else (addr & ~1), RET, count=BUDGET)
    except UcError as e:
        pc = uc.reg_read(UC_ARM_REG_PC)
        try:
            if thumb:
                hw = int.from_bytes(uc.mem_read(pc & ~1, 2), "little")
                if hw >> 8 == 0xDE:
                    return "TRAP"
            else:
                w = int.from_bytes(uc.mem_read(pc, 4), "little")
                if w & 0xFFF000F0 == 0xE7F000F0:
                    return "TRAP"
        except UcError:
            pass
        return f"FAULT({e}) pc={pc:#x}"
    pc = uc.reg_read(UC_ARM_REG_PC)
    if pc != RET:
        return f"HANG pc={pc:#x} (budget {BUDGET} exhausted)"
    return uc.reg_read(UC_ARM_REG_R0) & M32


def fmt(v):
    return v if isinstance(v, str) else f"{v:#x}"


def main():
    need("arm-none-eabi-ld")
    expected = {}
    for fixture, vecs in ((CF, CF_VECTORS), (SB, SB_VECTORS), (OPT, OPT_VECTORS)):
        for fn, a, b in vecs:
            expected[(fixture, fn, a, b)] = truth(fixture, fn, a, b)
    traps = sum(1 for v in expected.values() if v == "TRAP")
    print(f"wasmtime: {len(expected)} vectors ({traps} trap)")

    failed_legs = []
    with tempfile.TemporaryDirectory() as tmp:
        for name, fixture, flags, kind in LEGS:
            tag = {CF: "cf", SB: "sb", OPT: "opt"}[fixture]
            obj = str(Path(tmp) / f"{tag}_{LEGS.index((name, fixture, flags, kind))}.o")
            print(f"== {name}: synth compile {fixture.name} {' '.join(flags)}")
            rc, out, optimized = compile_leg(fixture, flags, obj)
            if rc != 0:
                print(f"  COMPILE FAILED (rc={rc}):\n{out}")
                failed_legs.append(name)
                continue
            if fixture == OPT and optimized != set(range(len(OPT_EXPORTS))):
                print(f"  NOT ON THE OPTIMIZED PATH: funcs {sorted(optimized)} of "
                      f"{len(OPT_EXPORTS)} — the leg no longer exercises "
                      f"estimator-resolved back-edges")
                failed_legs.append(name)
                continue
            exe = obj
            if kind in ("a32", "thumb"):
                exe = obj + ".elf"
                err = link(obj, exe, "f" if fixture == CF else "ld")
                if err:
                    print(f"  LINK FAILED: {err}")
                    failed_legs.append(name)
                    continue
            text, base, syms = load(exe)
            vecs = {CF: CF_VECTORS, SB: SB_VECTORS, OPT: OPT_VECTORS}[fixture]
            if kind == "a32-image" and fixture == CF:
                vecs = [v for v in vecs if v[0] in IMAGE_LEG_EXPORTS]
                print("  scope: IMAGE_LEG_EXPORTS (see header)")
            bad = 0
            for fn, a, b in vecs:
                want = expected[(fixture, fn, a, b)]
                if fn not in syms:
                    print(f"  MISSING symbol {fn}")
                    bad += 1
                    continue
                got = emulate(text, base, syms[fn], a, b, kind == "thumb")
                if got != want:
                    bad += 1
                    print(f"  MISMATCH {fn}({a:#x}, {b:#x}): wasmtime={fmt(want)} "
                          f"synth={fmt(got)}")
            print(f"  {len(vecs) - bad}/{len(vecs)} vectors match")
            if bad:
                failed_legs.append(name)

    print(f"emulations: {EMULATIONS}")
    if failed_legs:
        print(f"ORACLE: FAIL  <-- #1639/#1641 ({', '.join(failed_legs)})")
        sys.exit(1)
    print("ORACLE: PASS")
    sys.exit(0)


if __name__ == "__main__":
    main()
