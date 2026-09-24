#!/usr/bin/env python3
"""RQ-72-ISLANDS follow-up: every offset the encode loop RECORDS must still
point at the instruction it was recorded for, after an inline literal island
has been inserted.

# ci-status: wired
# ci-checks: stdout /^objects checked: ([0-9]+)$/ >= 308

WHAT THIS ORACLE CANNOT SEE (RQ-74-ISLANDREACH, v0.74) — disclosed here rather
than left for the next reviewer to rediscover. INV1/INV2 check that a RECORDED
offset still points at the instruction it was recorded for. They do NOT check
that a branch's TARGET is the right instruction. v0.73's round-2 gate review
advanced every local branch target by one WHOLE instruction — so every target
remained a legal instruction start, and every recorded offset still pointed at
its own instruction — and this file reported "306 objects checked, 306 clean,
0 violations" with exit 0. Re-measured at the v0.74 cut: still MISSED.

`sc5_postisland_345.py` is blind to the same mutation for the same reason (it
checks MEMBERSHIP in the instruction-start set, and the moved target is a member).
What covers the class is
`scripts/repro/islandpass_1331_execution_differential.py`, which EXECUTES the
emitted bytes against wasmtime instead of reasoning about their layout — and as
of v0.74 it does so over three span shapes rather than one.

A second, narrower note: a DECLINE is booked here as a correct outcome, so a
change that made modules stop compiling would shrink `objects checked` rather
than red. That is why the declared floor is pinned at the measured population
(308 at the v0.74 cut, up from 306 because RQ-74-ISLANDREACH added two
spanning fixtures to this sweep) and not a round number below it.

WHY THIS EXISTS. v0.72's first island guard reasoned only about BRANCH offsets
(`BOffset`/`BCondOffset`) and missed that the same loop records FOUR other
offsets from `code.len()` — the `Bl` relocation, `MovwSym`, `MovtSym`, and
`LdrSym`'s `ldr_offset`. Inserting an island moved the instruction and left
every one of those pointing at the island instead. Both reproductions compiled
at rc=0 on shapes v0.71 had refused LOUDLY:

    INV1  R_ARM_THM_CALL@0x1014 sym=func_0 -> hw1=0xe002 not a BL
          (0xe002 is the island's own `b.n +8`; the real BL is at 0x101c)
    INV2  LDR.W lit@0x1010 imm12=0 -> 0x1014 no relocation
          (the imm12 patch went to 0x1008, inside the island)

A loud refusal traded for a silent wrong answer — twice, in the fix for the
first instance of exactly that trade. The ordering fix is one thing; this
oracle is the other, because the defect was INVISIBLE to every gate the lane
shipped. The byte-identity differential cannot see it (the affected modules
previously REFUSED, so they have no byte baseline) and the execution
differential's islanded module has no calls and one literal.

THE TWO INVARIANTS, both read from the emitted ELF rather than from synth's
own bookkeeping — the point is to check the bytes against the relocations, so
a checker that consulted the same structures that were wrong would agree with
them:

  INV1  every `R_ARM_THM_CALL` relocation offset lands on a BL/BLX first
        halfword (`hw1 & 0xF800 == 0xF000`). A relocation pointing anywhere
        else means the linker will write a call over something that is not a
        call.

  INV2  every `LDR.W rd,[pc,#imm12]` (hw1 == 0xF8DF) resolves to an address
        that CARRIES a relocation — i.e. to a real pool word. A literal load
        whose target has no relocation is loading whatever bytes are there,
        which for a mis-recorded offset is executable code.

Both are properties of the SHIPPED object, read from the ELF rather than from
synth's own bookkeeping — a checker that consulted the structures that were
wrong would simply agree with them.

ONLY ONE `# ci-checks:` line is permitted per oracle, and it is spent on the
POPULATION rather than the verdict. The verdict already reds the step through
the exit code (`return 1 if hits else 0`); what an exit code cannot see is a
run that checked NOTHING and exited 0. So CI floors the corpus size, the
process exit carries correctness, and the in-script `checked == 0` guard
refuses the same vacuity a second time, independently.

Usage:  island_offset_invariant_345.py [<synth>] [<glob>]
"""

from __future__ import annotations

import glob
import os
import struct
import subprocess
import sys
import tempfile

from elftools.elf.elffile import ELFFile

R_ARM_THM_CALL = 10
BL_MASK, BL_BITS = 0xF800, 0xF000   # T1 BL / BLX first halfword
LDR_LITERAL_HW1 = 0xF8DF            # LDR.W rd,[pc,#imm12]

# THREE dirnames: this file lives at <root>/scripts/repro/<name>.py, so two
# lands on `scripts/` and the default glob becomes `scripts/scripts/repro/*.wat`
# — which matches nothing. That is exactly how this shipped the first time: the
# local run passed the glob EXPLICITLY as argv[2] and never exercised the
# default, while CI invokes the script with NO arguments. The oracle "passed"
# locally for a different reason than the one CI asks about.
#
# It went red rather than green, because both anti-vacuity guards fired:
#     objects checked: 0
#     FAIL: zero objects checked — the corpus or the compiler is broken
#     FAIL ...: VACUOUS — declared floor stdout >= 150, measured 0
# An oracle that silently checks nothing is the failure this file exists to
# prevent, so it is fitting that its own first CI run was caught by it.
ROOT = os.path.dirname(
    os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SYNTH = sys.argv[1] if len(sys.argv) > 1 else os.environ.get(
    "SYNTH_BIN", os.path.join(ROOT, "target", "debug", "synth"))
PATTERN = sys.argv[2] if len(sys.argv) > 2 else os.path.join(
    ROOT, "scripts", "repro", "*.wat")


def violations(path: str) -> list[str]:
    bad: list[str] = []
    with open(path, "rb") as fh:
        elf = ELFFile(fh)
        text = elf.get_section_by_name(".text")
        if text is None:
            return bad
        blob = text.data()
        rels: dict[int, tuple[int, str]] = {}
        rel_sec = elf.get_section_by_name(".rel.text")
        if rel_sec is not None:
            symtab = elf.get_section_by_name(".symtab")
            for r in rel_sec.iter_relocations():
                sym = symtab.get_symbol(r["r_info_sym"]).name
                rels[r["r_offset"]] = (r["r_info_type"], sym)

        for off, (kind, sym) in sorted(rels.items()):
            if kind == R_ARM_THM_CALL and off + 4 <= len(blob):
                hw1 = struct.unpack_from("<H", blob, off)[0]
                if (hw1 & BL_MASK) != BL_BITS:
                    bad.append(f"INV1 R_ARM_THM_CALL@0x{off:x} sym={sym} "
                               f"-> hw1=0x{hw1:04x} is not a BL")

        i = 0
        while i + 4 <= len(blob):
            hw1, hw2 = struct.unpack_from("<HH", blob, i)
            if hw1 == LDR_LITERAL_HW1:
                target = ((i + 4) & ~3) + (hw2 & 0xFFF)
                if target not in rels:
                    bad.append(f"INV2 LDR.W lit@0x{i:x} imm12={hw2 & 0xFFF} "
                               f"-> 0x{target:x} carries no relocation")
            i += 2
    return bad


def main() -> int:
    checked = clean = skipped = 0
    hits = []
    with tempfile.TemporaryDirectory() as td:
        out = os.path.join(td, "obj.o")
        for wat in sorted(glob.glob(PATTERN)):
            # BOTH relocatable legs: `--native-pointer-abi` is the route that
            # emits `LdrSym`, and the plain one still emits calls.
            for extra in ([], ["--native-pointer-abi"]):
                if os.path.exists(out):
                    os.remove(out)
                r = subprocess.run(
                    [SYNTH, "compile", wat, "-o", out, "--target", "cortex-m7",
                     "--relocatable", "--all-exports"] + extra,
                    capture_output=True, text=True, timeout=300)
                if r.returncode != 0 or not os.path.exists(out):
                    skipped += 1        # a LOUD refusal is a correct outcome
                    continue
                checked += 1
                bad = violations(out)
                if bad:
                    hits.append((os.path.basename(wat), extra, bad))
                else:
                    clean += 1

    print(f"objects checked: {checked}")
    print(f"objects clean: {clean}")
    print(f"declined legs (a refusal is a correct outcome): {skipped}")
    for name, extra, bad in hits:
        for b in bad:
            print(f"  VIOLATION {name} {' '.join(extra) or '(default abi)'}: {b}")
    print(f"invariant violations: {len(hits)}")
    if checked == 0:
        print("FAIL: zero objects checked — the corpus or the compiler is "
              "broken; this must never read as success")
        return 1
    return 1 if hits else 0


if __name__ == "__main__":
    sys.exit(main())
