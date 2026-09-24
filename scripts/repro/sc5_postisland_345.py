#!/usr/bin/env python3
# ci-status: wired
# ci-checks: compiles >= 2
"""RQ-73-SC5 (#345): SC-5 branch targets, checked on the FINAL bytes.

SC-5 says "branch offset calculation shall account for Thumb instruction
alignment and variable instruction widths". Thumb-2 mixes 16- and 32-bit
encodings, so a target off by one halfword lands on the SECOND halfword of a
wide instruction and the CPU executes something that was never an instruction —
silent garbage, exit 0. Both known escapes (#740's halved `B<cond>.W` offset,
#930's dropped end label) were of exactly that shape.

WHAT v0.72's COLD REVIEW FOUND. `validate_branch_targets` claims to gate "the
instruction-start set of THE FINAL STREAM", but it ran immediately after branch
resolution and BEFORE inline literal islands were inserted, and nothing
re-validated. The defence-in-depth gate had quietly narrowed to a PREFIX of the
pipeline, at exactly the moment the island placement guard became the only thing
standing between a spanning branch and a wrong target.

RQ-73-ISLANDPASS (#1331) fixed the coordinate system: the gate now derives
positions from `island_walk`, the same walk the offsets are resolved against.
This file is the part that cannot be argued — the DEMONSTRATION the artifact
asks for, because "moving the existing call site without such a demonstration
would restore the wording and not the guarantee".

WHY IT DECODES RATHER THAN ASKS. The in-compiler gate consults the compiler's
own instruction list. An oracle that did the same would agree with the compiler
precisely when the compiler is wrong — the v0.72 lesson that "a checker which
consults the same bookkeeping that was wrong will agree with it". So this walks
the emitted `.text` by Thumb-2 decoding rules and builds the instruction-start
set INDEPENDENTLY, then requires every branch target to be a member.

WHAT THIS DOES NOT DUPLICATE, since the artifact says a constraint enforced
twice badly is worse than once well. `island_offset_invariant_345.py` checks
RELOCATION and LITERAL invariants — a `R_ARM_THM_CALL` must land on a BL, a
literal load must resolve to a relocated word. It says nothing about branch
targets, and the v0.72 miscompile proves the gap is real in that direction too:
INV1 PASSED on an object whose `br_if` pointed 8 bytes early. Branch targets and
relocation targets are different properties of the same bytes.
"""

import os
import struct
import subprocess
import sys
import tempfile

SYNTH = os.environ.get("SYNTH_BIN", "./target/debug/synth")
REPRO = os.path.dirname(os.path.abspath(__file__))
ARGS = ["--target", "cortex-m7", "--relocatable", "--all-exports",
        "--native-pointer-abi"]

# The modules that carry an island BETWEEN a branch and its target. Only these
# can exercise the post-island coordinate system at all; a module needing no
# island would pass this check no matter which side of #1331 it was built on,
# which is the definition of a vacuous population.
SPANNING = [
    "litpool_islands_345_branchspan.wat",
    "islandpass_1331_spanning.wat",
]


def decode_starts(text: bytes) -> set:
    """Instruction-start offsets, derived from the BYTES.

    Thumb-2: a halfword in 0xE800..0xFFFF opens a 32-bit instruction; anything
    else is a complete 16-bit one. Deliberately independent of anything the
    compiler recorded.
    """
    starts, i = set(), 0
    while i + 1 < len(text):
        starts.add(i)
        (hw,) = struct.unpack_from("<H", text, i)
        i += 4 if 0xE800 <= hw <= 0xFFFF else 2
    return starts


def branch_targets(text: bytes, starts: set):
    """(offset, target, mnemonic) for every local branch in the stream.

    Only encodings whose target is a PC-relative displacement in the bytes are
    considered — a `bl` is a relocation site, not a resolved local branch, and
    belongs to the invariant oracle instead.
    """
    out = []
    for off in sorted(starts):
        if off + 1 >= len(text):
            continue
        (hw1,) = struct.unpack_from("<H", text, off)
        # B T2: unconditional, 11 bits, 0xE000..0xE7FF
        if 0xE000 <= hw1 <= 0xE7FF:
            imm11 = hw1 & 0x7FF
            if imm11 & 0x400:
                imm11 -= 0x800
            out.append((off, off + 4 + 2 * imm11, "b.n"))
        # B T1: conditional, 8 bits, 0xD000..0xDDFF (0xDE/0xDF are UDF/SVC)
        elif 0xD000 <= hw1 <= 0xDDFF:
            imm8 = hw1 & 0xFF
            if imm8 & 0x80:
                imm8 -= 0x100
            out.append((off, off + 4 + 2 * imm8, "b<c>.n"))
        # B T3: conditional wide, 0xF000..0xF3FF with hw2 0x8000..0xBFFF (op1=0)
        elif 0xF000 <= hw1 <= 0xF3FF and off + 3 < len(text):
            (hw2,) = struct.unpack_from("<H", text, off + 2)
            if (hw2 & 0xD000) == 0x8000:
                s = (hw1 >> 10) & 1
                j1, j2 = (hw2 >> 13) & 1, (hw2 >> 11) & 1
                imm6, imm11 = hw1 & 0x3F, hw2 & 0x7FF
                v = (s << 20) | (j2 << 19) | (j1 << 18) | (imm6 << 12) | (imm11 << 1)
                if s:
                    v -= 1 << 21
                out.append((off, off + 4 + v, "b<c>.w"))
    return out


def check_object(path: str, label: str):
    from elftools.elf.elffile import ELFFile

    e = ELFFile(open(path, "rb"))
    sec = e.get_section_by_name(".text")
    if sec is None:
        return [f"{label}: object has no .text"], 0
    text = sec.data()
    starts = decode_starts(text)
    problems = []
    checked = 0
    for off, tgt, mnem in branch_targets(text, starts):
        # A branch out of .text is a relocation's business, not SC-5's.
        if tgt < 0 or tgt >= len(text):
            continue
        checked += 1
        if tgt not in starts:
            problems.append(
                f"{label}: SC-5 VIOLATION — {mnem} at 0x{off:x} targets "
                f"0x{tgt:x}, which is NOT an instruction start. The CPU would "
                f"execute the second halfword of a 32-bit instruction: silent "
                f"garbage, exit 0 (the #740/#930 class).")
    return problems, checked


# THE FROZEN RED HALF. A checker that only ever sees correct bytes cannot be
# shown to discriminate, and this one runs on a compiler that is expected to be
# right — so on its own it would be a gate nobody has watched fail. These bytes
# are the `.text` of `litpool_islands_345_branchspan.wat` emitted by a build
# with `island_walk`'s size arithmetic perturbed by +2
# (`pos += b.len() + pad2 + 4 * n + 2`), which drives branch targets two bytes
# off into the SECOND halfword of a 32-bit instruction. Producing it also
# required neutering the in-compiler SC-5 gate — which is itself the evidence
# that gate now covers the post-island stream, since nothing else would emit
# such an object.
#
# FROZEN on purpose: it is an input, not an expectation, so it keeps proving
# this decoder discriminates no matter how the compiler changes. Same role as
# the `PINNED_WRONG` fixtures elsewhere in this directory, and excluded from
# `known_open_pins` by the same rule — a recorded wrong value of frozen pre-fix
# bytes is potency evidence, not a live suppression.
RED_HALF = "sc5_postisland_345_red.text.bin"
RED_HALF_SHA256 = "2a94a1d5a87855d9"  # first 16 hex chars; provenance, not a gate


def check_red_half():
    """The frozen wrong bytes MUST be flagged. Silence here means this oracle
    has stopped discriminating, whatever it says about the live objects."""
    import hashlib

    path = os.path.join(REPRO, RED_HALF)
    if not os.path.isfile(path):
        return [f"POTENCY: frozen red half {RED_HALF} is missing — this gate "
                f"can no longer be shown to fail on anything"]
    text = open(path, "rb").read()
    got = hashlib.sha256(text).hexdigest()[:16]
    if got != RED_HALF_SHA256:
        return [f"POTENCY: frozen red half changed ({got} != "
                f"{RED_HALF_SHA256}) — a FROZEN input that moved is not frozen"]
    starts = decode_starts(text)
    bad = [t for _, t, _ in branch_targets(text, starts)
           if 0 <= t < len(text) and t not in starts]
    if not bad:
        return ["POTENCY: the frozen MIS-TARGETED stream was accepted — this "
                "decoder no longer detects an off-by-one-halfword target, so "
                "its PASS on the live objects means nothing"]
    print(f"  potency: frozen red half flagged ({len(bad)} mis-targeted "
          f"branch(es)), so this decoder discriminates")
    return []


def main() -> int:
    if not os.path.isfile(SYNTH):
        print(f"FAIL: {SYNTH} not built")
        return 1

    problems = check_red_half()
    total_branches, compiled = 0, 0
    with tempfile.TemporaryDirectory() as td:
        for name in SPANNING:
            src = os.path.join(REPRO, name)
            if not os.path.isfile(src):
                print(f"FAIL: missing spanning fixture {name}")
                return 1
            obj = os.path.join(td, name + ".o")
            r = subprocess.run([SYNTH, "compile", src, *ARGS, "-o", obj],
                               capture_output=True, text=True)
            if r.returncode != 0 or not os.path.isfile(obj):
                problems.append(
                    f"{name}: did not compile, so the post-island stream was "
                    f"never produced. Since #1331 these shapes MUST compile; a "
                    f"refusal here means the island fixed point regressed and "
                    f"this gate has silently stopped covering anything.")
                continue
            compiled += 1
            p, n = check_object(obj, name)
            problems += p
            total_branches += n
            print(f"  {name}: {n} local branch target(s) on instruction starts")

    # ANTI-VACUITY. This gate can only mean something if it saw post-island
    # streams carrying real branches. Both are refused, not reported.
    if compiled != len(SPANNING):
        problems.append(
            f"VACUITY: {compiled} of {len(SPANNING)} spanning modules compiled")
    if total_branches == 0:
        problems.append(
            "VACUITY: zero local branch targets were checked — the fixtures "
            "carry no resolved branch, so this gate proves nothing")

    print(f"sc5-postisland: {compiled} object(s), {total_branches} branch "
          f"target(s) checked against a DECODED instruction-start set")
    if problems:
        for p in problems:
            print(f"REFUSE: {p}")
        print("RESULT: FAIL")
        return 1
    print("RESULT: PASS — every branch target in a post-island stream lands on "
          "an instruction start")
    return 0


if __name__ == "__main__":
    sys.exit(main())
