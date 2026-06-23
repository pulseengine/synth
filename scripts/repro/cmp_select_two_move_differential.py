#!/usr/bin/env python3
"""VCR-SEL-004 / VCR-ORACLE-001 (#428, #242) — EXECUTION-validate the two-move arm.

gale's gust_codegen_bench follow-up (#428) proved that no real fixture — gust_mix
included — exercises the cmp→select *two-move* form (`mov{c} dst,v1; mov{invert(c)}
dst,v2`). Every fused site on real code is the in-place single-move form. The only
thing that exercises the `mov{invert(c)}` arm anywhere is this synthetic fixture,
and until now it had only ever been IR-unit- and objdump-checked — NEVER executed.

This harness closes that gap: it runs `two_move_sel` under unicorn (faithful Thumb-2
IT-block predication) in BOTH flag-off (unfused) and flag-on (#7 fused, two-move)
builds and asserts both equal wasmtime ground truth across an input sweep. The sweep
deliberately straddles the comparison so BOTH predicated arms fire:

    sel = (a <_s b) ? a : lo          ; movlt (c=LT)  fires when a <  b
    result = sel*lo + (a - b)         ; movge (inv c) fires when a >= b  <-- the arm

NON-VACUITY: the run aborts unless (1) the flag-on build reports >=1 two-move fusion
(SYNTH_FUSE_STATS), and (2) the sweep contains at least one a<b vector AND at least
one a>=b vector — otherwise the `mov{invert(c)}` arm would never execute and the
"validation" would be theater.

Run (needs wasmtime + unicorn + pyelftools, e.g. a venv):
  python scripts/repro/cmp_select_two_move_differential.py

Exits nonzero on any mismatch or vacuity failure.
"""
import re
import subprocess
import sys

import wasmtime
from elftools.elf.elffile import ELFFile
from unicorn import UC_ARCH_ARM, UC_MODE_THUMB, Uc, UcError
from unicorn.arm_const import (
    UC_ARM_REG_LR,
    UC_ARM_REG_R0,
    UC_ARM_REG_R1,
    UC_ARM_REG_R2,
    UC_ARM_REG_R11,
    UC_ARM_REG_SP,
)

WASM = "scripts/repro/cmp_select_two_move.wat"
SYNTH = "./target/debug/synth"
ELF_OFF, ELF_ON = "/tmp/two_move_off.elf", "/tmp/two_move_on.elf"
CODE, LIN, STK, RET = 0x200000, 0x40000, 0x90000, 0x300000

# (a, b, lo). Straddles a<b (movlt, sel=a) and a>=b (movge / mov{invert(c)}, sel=lo),
# including i32.lt_s SIGNED edges (negatives) and i32 wrap (mul/sub overflow).
VECTORS = [
    (10, 20, 5),       # a<b   -> sel=a
    (0, 100, 7),       # a<b   -> sel=a
    (-5, 0, 3),        # a<b   (signed) -> sel=a
    (-2147483648, 2147483647, 9),  # a<b extreme
    (20, 10, 5),       # a>=b  -> sel=lo   (movge arm)
    (5, 5, 3),         # a==b  -> sel=lo   (movge arm)
    (100, 0, 7),       # a>=b  -> sel=lo
    (-3, -10, 2),      # a>=b  (signed) -> sel=lo
    (2147483647, -2147483648, 4),  # a>=b extreme -> wrap in mul/sub
    (123, 45, 0),      # lo=0  -> sel*lo=0
    (0, 0, 0),         # all zero
]


def to_s32(x):
    x &= 0xFFFFFFFF
    return x - 0x100000000 if x & 0x80000000 else x


def arm_branch(a, b):
    """Which predicated arm fires: 'movlt' (a<b, sel=a) or 'movge' (a>=b, sel=lo)."""
    return "movlt" if to_s32(a) < to_s32(b) else "movge"


def compile_elf(out, fused):
    env = {"PATH": "/usr/bin:/bin"}
    if fused:
        env["SYNTH_CMP_SELECT_FUSE"] = "1"
        env["SYNTH_FUSE_STATS"] = "1"
    r = subprocess.run(
        [SYNTH, "compile", WASM, "-o", out, "--target", "cortex-m4",
         "--all-exports", "--relocatable"],
        capture_output=True, text=True, env={**env},
    )
    if r.returncode != 0:
        sys.exit(f"compile failed (fused={fused}): {r.stderr}")
    two_move = 0
    for line in (r.stdout + r.stderr).splitlines():
        if "[cmp-select-fuse]" in line:
            m = re.search(r"\((\d+) two-move", line)
            if m:
                two_move += int(m.group(1))
    return two_move


def load(elf):
    # The fixture has exactly ONE function (two_move_sel), so it is at .text
    # offset 0 — no disasm symbol-table round-trip needed (that subprocess's
    # output format is environment-sensitive; the single-function invariant is
    # not). fa == sh_addr ⇒ the unicorn entry is CODE + (fa - base) == CODE.
    text = ELFFile(open(elf, "rb")).get_section_by_name(".text")
    code, base = text.data(), text["sh_addr"]
    if not code:
        sys.exit(f"{elf}: .text is empty")
    return code, base, base


def run_arm(code, base, fa, a, b, lo):
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)
    mu.mem_map(CODE, 0x10000)
    mu.mem_map(LIN, 0x20000)
    mu.mem_map(STK - 0x8000, 0x10000)
    mu.mem_map(RET, 0x1000)
    mu.mem_write(CODE, code)
    mu.reg_write(UC_ARM_REG_SP, STK)
    mu.reg_write(UC_ARM_REG_R11, LIN)
    mu.reg_write(UC_ARM_REG_R0, a & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R1, b & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_R2, lo & 0xFFFFFFFF)
    mu.reg_write(UC_ARM_REG_LR, RET | 1)
    try:
        mu.emu_start((CODE + fa - base) | 1, RET, count=10000)
    except UcError as e:
        return f"ERR:{e}"
    return mu.reg_read(UC_ARM_REG_R0) & 0xFFFFFFFF


def main():
    # Non-vacuity (1): the flag-on build must actually contain a two-move fusion.
    compile_elf(ELF_OFF, fused=False)
    two_move = compile_elf(ELF_ON, fused=True)
    if two_move < 1:
        sys.exit(f"VACUOUS: flag-on build has 0 two-move fusions "
                 f"(the mov{{invert(c)}} arm is not even present)")

    # Non-vacuity (2): the sweep must straddle the compare so both arms fire.
    arms = {arm_branch(a, b) for (a, b, _lo) in VECTORS}
    if arms != {"movlt", "movge"}:
        sys.exit(f"VACUOUS: sweep exercises only {arms}; need both movlt and movge")

    engine = wasmtime.Engine()
    module = wasmtime.Module(engine, open(WASM, "rb").read())

    def wt(a, b, lo):
        store = wasmtime.Store(engine)
        inst = wasmtime.Instance(store, module, [])
        return inst.exports(store)["two_move_sel"](store, a, b, lo) & 0xFFFFFFFF

    off = load(ELF_OFF)
    on = load(ELF_ON)

    fails = 0
    movge_checked = 0
    for (a, b, lo) in VECTORS:
        gt = wt(a, b, lo)
        r_off = run_arm(*off, a, b, lo)
        r_on = run_arm(*on, a, b, lo)
        arm = arm_branch(a, b)
        ok = isinstance(r_off, int) and isinstance(r_on, int) and r_off == gt and r_on == gt
        # The crucial cases: a>=b runs the mov{invert(c)} arm flag-on.
        if arm == "movge" and isinstance(r_on, int) and r_on == gt:
            movge_checked += 1
        fails += 0 if ok else 1
        so = f"0x{r_off:08X}" if isinstance(r_off, int) else r_off
        sn = f"0x{r_on:08X}" if isinstance(r_on, int) else r_on
        print(f"two_move_sel{(a, b, lo)} [{arm}] off={so} on={sn} "
              f"wasmtime=0x{gt:08X}{'' if ok else '  <-- MISMATCH'}")

    print(f"\n{len(VECTORS) - fails}/{len(VECTORS)} match (off==on==wasmtime); "
          f"{two_move} two-move fusion(s); {movge_checked} mov{{invert(c)}}-arm vectors validated")
    if movge_checked < 1:
        sys.exit("VACUOUS: no a>=b vector validated the mov{invert(c)} arm at runtime")
    print("ORACLE: PASS" if fails == 0 else f"ORACLE: FAIL ({fails})")
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
