#!/usr/bin/env python3
# ci-checks: stdout /([0-9]+) assertions/ >= 9
# ci-status: wired — `--self-test` runs in the required `claim-check` job and is the
# POTENCY evidence: it injects each of the three mechanisms this lane refuted, plus a
# dropped term, and refuses a derived population of zero. The COMPARISON itself cannot be
# wired and that is a property of the input, not an omission: the module it compares lives
# in pulseengine/jess (`repro/synth-1436/c.loom.wasm`), so a CI run here would have nothing
# to compare and would pass VACUOUSLY — the exact shape this gate exists to prevent. The
# reporter has the module and the hardware and can run the comparison; what can rot in THIS
# repo is the oracle's own power, so that is what CI asserts.
"""RQ-81-JESSDIVERGE3 (#1436): is the GRAVITY-COMPENSATION addend lowered faithfully?

The reporter's measurement named ONE MISSING OR ZERO-VALUED ADDEND — `+ g_nav`,
the gravity compensation of a strapdown inertial update
`v_nav += (R(q)*a_body + g_nav)*dt`. The artifact listed three candidate
mechanisms and said synth's own disassembly was needed to choose between them:
the addend is ABSENT, it is ZEROED, or it is LANDING ON ANOTHER AXIS.

THIS SCRIPT ANSWERS THAT QUESTION AND THE ANSWER IS **NONE OF THE THREE**. It
re-derives the comparison rather than asserting it, so the refutation can be
re-run by the reporter, who has the module and the hardware.

WHAT IT COMPARES, both sides derived, neither hand-copied:

  INPUT  — every `localA + localB * 9.81 -> f32.store offset=N` triple in the
           wat, with A, B and N read out of the text.
  OUTPUT — every `movw/movt 0x411cf5c3 ; vmov ; vmul ; vadd ; str` block in the
           ARM disassembly, with its two source operands and its store offset.

A faithful lowering must agree on the CONSTANT, the OPERAND PAIRING (which side
of the product the addend is on), the STORE OFFSETS and their ORDER. Those are
exactly the four things the three candidate mechanisms would break: an ABSENT
addend loses the `vadd`, a ZEROED one loses the operand, and a WRONG AXIS
permutes the store offsets.

MEASURED at the v0.81 cut on `c.loom.wasm` (791ab6b5..), lowered by synth 0.79.0
with the reporter's own compile line (jess confirmed 0.77.0 and 0.79.0 produce
BYTE-IDENTICAL output for this module, so the version is not a variable):

    offset 940 <- local19 + local10 * 9.81     ARM: [sp,200] + [sp,152] * 9.81
    offset 936 <- local21 + local23 * 9.81     ARM: [sp,216] + [sp,232] * 9.81
    offset 944 <- local17 + local20 * 9.81     ARM: [sp,192] + [sp,208] * 9.81

Three terms, same order, same offsets, same pairing, correct constant — and the
neighbouring `f32.store offset=932` and `i32.store offset=980` match too, which
is what shows the window is aligned rather than coincidentally similar.

SO THE DIVERGENCE IS NOT IN THE EXPRESSION, AND THAT IS THE FINDING. The
lowering computes the right formula from the right slots. What remains is the
VALUE a multiplicand slot holds at run time — which this static comparison
cannot see and which the reporter's memtrace plugin can, windowed to
`[sp,#152]`, `[sp,#208]` and `[sp,#232]`. Naming that is the lane's deliverable;
claiming the cause would not be.

NOT CLAIMED, stated so the next reader does not inherit a wider result than was
measured: this compares the gravity-compensation site ONLY. The pcs the reporter
traced (`.text+0x1f6c/+0x1f90/+0x1fb4`) are a DIFFERENT computation —
`mem[X] += sN` accumulations, and at `+0x1fb4` `mem[0xad18] += (s2 * mem[sp+152])
* 0.001` where `0x3a83126f` is exactly dt = 1 ms. Those are not checked here.

A LIVENESS CHECK WAS ALSO RUN AND CAME BACK EMPTY, recorded because an empty
result is not a pass: all six operand slots are both written and read
(`vstr` > 0 for each), so "a slot read but never written" is refuted too.

USAGE (the module lives in pulseengine/jess, not here, so this takes paths):

    jessdiverge3_gravity_faithful_1436.py --wat c.wat --dis full.dis

where `c.wat` is `wasm-tools print c.loom.wasm` and `full.dis` is
`arm-none-eabi-objdump -d -M force-thumb cascade.o`. `--self-test` runs the
NEGATIVE CONTROLS on synthetic text, which is what keeps this from being a
comparison that cannot fail.
"""

from __future__ import annotations

import argparse
import re
import sys

# 9.81f. The ARM materializes an f32 constant as a movw/movt immediate PAIR, not
# as literal-pool bytes -- so a byte search for `c3f51c41` in the object finds
# ZERO and means nothing. That false negative is why this script matches the
# instruction pair instead: it was measured, on 0.001f, which a byte search also
# reports absent from an object that demonstrably materializes it 22 times.
G_HI, G_LO = 0x411C, 0xF5C3

WAT_TRIPLE = re.compile(
    r"local\.get (\d+)\s*\n\s*local\.get (\d+)\s*\n\s*"
    r"f32\.const [^\n]*\(;=9\.81;\)\s*\n\s*f32\.mul\s*\n\s*f32\.add\s*\n\s*"
    r"f32\.store offset=(\d+)")

ARM_BLOCK = re.compile(
    r"vldr\s+s\d+, \[sp, #(\d+)\][^\n]*\n"       # the ADDEND
    r"[^\n]*vldr\s+s\d+, \[sp, #(\d+)\][^\n]*\n"  # the MULTIPLICAND
    r"[^\n]*movw\s+\w+, #\d+\s*@ 0x%04x[^\n]*\n"
    r"[^\n]*movt\s+\w+, #\d+\s*@ 0x%04x[^\n]*\n"
    r"[^\n]*vmov[^\n]*\n"
    r"[^\n]*vmul\.f32[^\n]*\n"
    r"[^\n]*vadd\.f32[^\n]*\n"
    r"[^\n]*vmov[^\n]*\n"
    r"[^\n]*addw\s+\w+, \w+, #(\d+)" % (G_LO, G_HI))


def wat_triples(text: str):
    """[(addend_local, multiplicand_local, store_offset)] in source order."""
    return [(int(a), int(b), int(n)) for a, b, n in WAT_TRIPLE.findall(text)]


def arm_triples(text: str):
    """[(addend_slot, multiplicand_slot, store_offset)] in program order."""
    return [(int(a), int(b), int(n)) for a, b, n in ARM_BLOCK.findall(text)]


def compare(wat: list, arm: list) -> list[str]:
    """Findings. EMPTY means the lowering is faithful at this site."""
    out: list[str] = []
    if not wat:
        return ["REFUSED: zero gravity triples found in the wat. A population of "
                "zero is a refusal, not a pass -- either the input does not apply "
                "gravity here or this matcher has rotted"]
    if not arm:
        return [f"ABSENT: the wat applies gravity {len(wat)} time(s) and the ARM "
                f"disassembly contains NO matching mul-add block. This is the "
                f"'addend ABSENT' mechanism and it would be the finding"]
    if len(wat) != len(arm):
        out.append(f"COUNT: wat applies gravity {len(wat)} time(s), ARM has "
                   f"{len(arm)} block(s)")
    # The AXIS check: the store offsets, IN ORDER. A permutation here is exactly
    # the "landing on another axis" mechanism.
    w_off = [n for _a, _b, n in wat]
    a_off = [n for _a, _b, n in arm]
    if w_off != a_off:
        if sorted(w_off) == sorted(a_off):
            out.append(f"WRONG AXIS: same offsets, DIFFERENT ORDER -- wat {w_off} "
                       f"vs ARM {a_off}. The addend lands on another component")
        else:
            out.append(f"OFFSETS DIFFER: wat {w_off} vs ARM {a_off}")
    # The PAIRING check: a distinct addend slot per term, and distinct from the
    # multiplicand. Collapsing them is how a term reads as zero.
    for i, (_wa, _wb, woff) in enumerate(wat):
        if i >= len(arm):
            break
        aa, ab, _ = arm[i]
        if aa == ab:
            out.append(f"ZEROED/PAIRING: offset {woff}: the ARM reads its addend "
                       f"and its multiplicand from the SAME slot [sp,#{aa}]")
    if len({a for a, _b, _n in arm}) != len(arm):
        out.append(f"PAIRING: ARM addend slots are not distinct: "
                   f"{[a for a, _b, _n in arm]}")
    return out


def self_test() -> int:
    """NEGATIVE CONTROLS. A comparison that cannot fail is not a comparison."""
    fails = 0
    ran = 0

    def check(name, cond, detail=""):
        nonlocal fails, ran
        ran += 1
        if cond:
            print(f"  ok   {name}")
        else:
            fails += 1
            print(f"  FAIL {name}{(' -- ' + detail) if detail else ''}")

    good_wat = [(19, 10, 940), (21, 23, 936), (17, 20, 944)]
    good_arm = [(200, 152, 940), (216, 232, 936), (192, 208, 944)]
    check("FAITHFUL: the measured pair reports NO findings",
          compare(good_wat, good_arm) == [], str(compare(good_wat, good_arm)))

    # the three mechanisms the artifact named, each injected
    check("ABSENT: no ARM block at all is reported",
          any("ABSENT" in x for x in compare(good_wat, [])))
    permuted = [(200, 152, 936), (216, 232, 940), (192, 208, 944)]
    check("WRONG AXIS: a PERMUTATION of the store offsets is reported",
          any("WRONG AXIS" in x for x in compare(good_wat, permuted)),
          str(compare(good_wat, permuted)))
    collapsed = [(152, 152, 940), (216, 232, 936), (192, 208, 944)]
    check("ZEROED: addend and multiplicand from ONE slot is reported",
          any("ZEROED" in x for x in compare(good_wat, collapsed)),
          str(compare(good_wat, collapsed)))
    check("a DROPPED term is reported",
          any("COUNT" in x for x in compare(good_wat, good_arm[:2])),
          str(compare(good_wat, good_arm[:2])))
    # and the vacuity refusal, because a derived population of zero is a refusal
    check("VACUITY: zero wat triples is a REFUSAL, not a pass",
          any("REFUSED" in x for x in compare([], good_arm)))

    # the TEXT matchers, against real shapes rather than tuples
    wat_sample = (
        "        local.get 6\n        local.get 19\n        local.get 10\n"
        "        f32.const 0x1.39eb86p+3 (;=9.81;)\n        f32.mul\n"
        "        f32.add\n        f32.store offset=940\n")
    check("the WAT matcher reads a real triple out of real text",
          wat_triples(wat_sample) == [(19, 10, 940)], str(wat_triples(wat_sample)))
    arm_sample = (
        "    2490:\ted9d 4a32 \tvldr\ts8, [sp, #200]\t@ 0xc8\n"
        "    2494:\teddd 4a26 \tvldr\ts9, [sp, #152]\t@ 0x98\n"
        "    2498:\tf24f 5cc3 \tmovw\tip, #62915\t@ 0xf5c3\n"
        "    249c:\tf2c4 1c1c \tmovt\tip, #16668\t@ 0x411c\n"
        "    24a0:\tee05 ca10 \tvmov\ts10, ip\n"
        "    24a4:\tee64 5a85 \tvmul.f32\ts11, s9, s10\n"
        "    24a8:\tee74 4a25 \tvadd.f32\ts9, s8, s11\n"
        "    24ac:\tee14 7a90 \tvmov\tr7, s9\n"
        "    24b0:\tf206 3cac \taddw\tip, r6, #940\t@ 0x3ac\n")
    check("the ARM matcher reads a real block out of real objdump text",
          arm_triples(arm_sample) == [(200, 152, 940)], str(arm_triples(arm_sample)))
    # and it must NOT match a block whose constant is something else
    check("the ARM matcher IGNORES a mul-add by a different constant",
          arm_triples(arm_sample.replace("0x411c", "0x3a83")) == [])

    # The COUNT is printed and floored in the `# ci-checks:` header, not just the
    # failure total: a body that stopped running early prints "0 failure(s)" and
    # looks identical to a green suite. That is the #1435 digit-class defect, and
    # the floor is arithmetic here rather than a `grep -qE '[0-9]+ assertions'`,
    # which accepts ZERO.
    #
    # WHAT IT DOES AND DOES NOT CATCH, measured rather than assumed. Deleting the
    # last three assertions gives `6 assertions` then REFUSED, rc=1 — that is the
    # rot this floor is for. It does NOT catch an early `return` placed ABOVE this
    # line, which skips the guard entirely: the first probe written for it did
    # exactly that, returned 0, and looked like a passing control. Saying so here
    # is cheaper than the next reader re-deriving it.
    print(f"jessdiverge3-self-test: {ran} assertions, {fails} failure(s)")
    if ran < 9:
        print(f"REFUSED: only {ran} assertions ran; the suite did not complete")
        return 1
    return 1 if fails else 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--wat", help="wasm-tools print c.loom.wasm")
    ap.add_argument("--dis", help="arm-none-eabi-objdump -d -M force-thumb cascade.o")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    if not (args.wat and args.dis):
        ap.error("--wat and --dis are required unless --self-test")
    wat = wat_triples(open(args.wat).read())
    arm = arm_triples(open(args.dis).read())
    print(f"  input  applies gravity {len(wat)} time(s): {wat}")
    print(f"  output has {len(arm)} matching block(s): {arm}")
    findings = compare(wat, arm)
    for f in findings:
        print(f"FINDING {f}")
    if findings:
        print("jessdiverge3: the gravity-compensation lowering DIVERGES from its input")
        return 1
    print("jessdiverge3: the gravity-compensation addend is lowered FAITHFULLY -- "
          "ABSENT, ZEROED and WRONG-AXIS are all refuted at this site")
    return 0


if __name__ == "__main__":
    sys.exit(main())
