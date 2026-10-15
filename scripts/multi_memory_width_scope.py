#!/usr/bin/env python3
"""RQ-87-MEMLAYER4 (#1145) — is the multi-memory layering scoped to the widths
the reporter ACTUALLY uses?

BOTH SIDES OF THE COMPARISON ARE DERIVED, which is this repository's first
invariant: never hand-write a mirror of a shipped thing.

  the reporter's exercised widths  <- parsed from the COMMITTED FIXTURE
                                      (`mem_isolation_two_tenant_1145.wat`),
                                      which was adopted VERBATIM from the
                                      reporter's own kill criterion
  phase-one's reach                <- parsed from the SELECTOR SOURCE, out of
                                      the `MultiMemory` arm's own inner match,
                                      so widening or narrowing the family moves
                                      this number without anyone updating a list

WHAT THE MEASUREMENT FOUND, and it HALF-REFUTES the artifact's premise. The
premise was that phase-one reaches "the i32 access family ONLY -- so lifting the
two refusals moves the blocker for any other width". The reporter uses NO other
width: their entire #1145 thread and the verbatim fixture exercise `i32.load8_u`
and `i32.store8` and nothing else, both inside the i32 family. So the WIDTH
refusal does not bite this reporter at all, and costing a width lift would spend
effort on input they never exercise.

THE TWO REFUSALS ARE NOT SYMMETRIC, which is the scoping conclusion:

  width refusal   -- i64/f32/f64/v128 on memory k decline loudly. DOES NOT
                     REACH THE REPORTER: zero of their accesses are non-i32.
  bounds refusal  -- `--safety-bounds software|mask` declines for ANY memory-k
                     access REGARDLESS OF WIDTH. This is the reporter's entire
                     remaining blocker, and it is WIDTH-INDEPENDENT: the root
                     cause is that the guard compares against R10, which holds
                     MEMORY 0's size by the register contract, and memory k has
                     no size register at all.

So the lift to cost is a PER-MEMORY SIZE SOURCE (`__synth_mem_size_k`), not
width coverage. Verified by execution, not by reading: the pinned repro
`mem_isolation_red_1145.py` compiles this fixture on the plain `--relocatable`
path today and records software/mask loud-skipping memory 1.

"THE TWO REFUSALS" IS READ OFF THE SOURCE, not inferred. The selector's own
phase-1 comment names exactly two: "i64/f32/f64/v128 accesses AND
`--safety-bounds` on memory k decline LOUDLY". The configuration refusals in
`multi_memory_pages` (non-relocatable, native-pointer ABI) are a different pair
and are not what the width claim is about.

AND THE OBVIOUS OBJECTION IS MEASURED RATHER THAN WAVED OFF: the fixture is
minimal, so does the reporter's REAL workload use a width it omits? Their actual
kernel is available locally
(`.rivet/repos/gale/benches/gust/wasm-kernel/fused.wasm`), and a walk of its
section table shows it declares exactly ONE memory. A single-memory module has
no memory-k access at any width, so it contributes nothing to this census and
cannot be a counter-example. The two-tenant fixture remains the only
multi-memory evidence in existence for this reporter, which is why it is the
right subject.

WHAT THIS PIN IS FOR. It reds when either side moves -- if the reporter's
fixture grows a width phase one does not reach, or if the family narrows under
one the fixture uses. Either event means the scoping decision above needs
re-examining, which is the only thing a pin can usefully guarantee here.

BOTH NEGATIVE CONTROLS WERE EXECUTED against mutated copies, with the real
fixture and selector untouched. Growing the fixture an `i64.load` breaks the
subset pin, as intended. Removing the selector's `other =>` cut does NOT make
the family slice over-read -- it RAISES, so the derivation fails closed. That is
a sound outcome and not the one the control was written to expect, and it is
recorded here because an unexecuted control would have shipped the wrong claim
about its own mechanism.
"""
import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURE = ROOT / "scripts/repro/mem_isolation_two_tenant_1145.wat"
SELECTOR = ROOT / "crates/synth-synthesis/src/instruction_selector/select_with_stack.rs"

WAT_ACCESS = re.compile(r"\b(i32|i64|f32|f64)\.(load|store)(8|16|32)?(?:_([su]))?\b")


def wat_to_variant(ty: str, kind: str, width: str | None, sign: str | None) -> str:
    """`i32.load8_u` -> `I32Load8U`, mechanically rather than by a lookup table."""
    return f"{ty.upper()}{kind.capitalize()}{width or ''}{(sign or '').upper()}"


def reporter_widths() -> dict[str, int]:
    """The access widths the committed reporter fixture actually exercises."""
    counts: dict[str, int] = {}
    for ty, kind, width, sign in WAT_ACCESS.findall(FIXTURE.read_text()):
        v = wat_to_variant(ty, kind, width, sign)
        counts[v] = counts.get(v, 0) + 1
    return counts


def phase_one_family() -> set[str]:
    """The variants the selector's MultiMemory arm actually lowers.

    Derived by slicing the arm out of the source and reading the PATTERNS of its
    inner match, stopping at the `other =>` fallthrough that declines the rest.
    A hand-written list here would be the mirror the North Star names first.
    """
    src = SELECTOR.read_text()
    start = src.index("                MultiMemory {")
    body = src[start:]
    inner = body.index("match inner_op.as_ref() {")
    body = body[inner:]
    end = body.index("other => {")
    region = body[:end]
    # Pattern position only: a variant followed by a brace-destructure. The
    # `=> ArmOp::` mapping lines reuse the same names, which is harmless for a
    # SET, and the `other =>` cut keeps the declining widths out.
    return set(re.findall(r"\b((?:I32|I64|F32|F64|V128)[A-Za-z0-9]*)\s*\{", region))


def report() -> int:
    used = reporter_widths()
    family = phase_one_family()
    print(f"REPORTER'S EXERCISED WIDTHS, derived from {FIXTURE.name}:")
    for v, n in sorted(used.items()):
        print(f"  {v:14s} x{n}   {'IN phase-one reach' if v in family else 'NOT REACHED'}")
    print(f"\nPHASE-ONE REACH, derived from {SELECTOR.name}'s MultiMemory arm: "
          f"{len(family)} op(s)")
    loads = sorted(v for v in family if "Load" in v)
    stores = sorted(v for v in family if "Store" in v)
    print(f"  loads  ({len(loads)}): {', '.join(loads)}")
    print(f"  stores ({len(stores)}): {', '.join(stores)}")
    gap = sorted(set(used) - family)
    print(f"\nGAP (reporter uses, phase one does not reach): {gap or 'NONE'}")
    print(f"UNEXERCISED REACH (phase one covers, reporter never uses): "
          f"{len(family - set(used))} op(s)")
    print("\nTHE TWO REFUSALS ARE NOT SYMMETRIC:")
    print("  width refusal  -- non-i32 on memory k declines loudly; reporter uses "
          f"{sum(1 for v in used if not v.startswith('I32'))} such access(es)")
    print("  bounds refusal -- --safety-bounds software|mask declines for ANY "
          "memory-k access, width-independent (the guard reads R10 = memory 0's size)")
    print("\nSCOPING CONCLUSION: the lift to cost is a per-memory size source "
          "(`__synth_mem_size_k`), NOT width coverage.")
    return 0 if not gap else 1


def self_test() -> int:
    fails = 0

    def ok(cond: bool, what: str) -> None:
        nonlocal fails
        print(f"  {'ok  ' if cond else 'FAIL'} {what}")
        if not cond:
            fails += 1

    # Both derivations must be NON-EMPTY, or the pin passes over nothing -- the
    # vacuity shape this repository has shipped once and now guards for.
    used, family = reporter_widths(), phase_one_family()
    ok(len(used) > 0, f"the reporter's exercised widths derive non-empty ({len(used)} kind(s))")
    ok(len(family) > 0, f"phase-one's reach derives non-empty ({len(family)} op(s))")

    # THE PIN: the reporter's widths are a SUBSET of phase one's reach, which is
    # what makes the width refusal irrelevant to them.
    ok(set(used) <= family,
       "every width the reporter exercises is INSIDE phase-one's reach")

    # And the asymmetry that carries the scoping conclusion.
    ok(all(v.startswith("I32") for v in used),
       "the reporter exercises NO non-i32 width, so the width refusal cannot reach them")

    # The mechanical wat->variant transform, controlled on shapes the fixture
    # does and does not contain, so it is not merely echoing the fixture.
    ok(wat_to_variant("i32", "load", "8", "u") == "I32Load8U", "wat->variant: load8_u")
    ok(wat_to_variant("i32", "store", "8", None) == "I32Store8", "wat->variant: store8")
    ok(wat_to_variant("i64", "load", None, None) == "I64Load",
       "wat->variant: a width the fixture does NOT use still maps correctly")

    # NEGATIVE CONTROL on the family derivation: the declining widths live past
    # the `other =>` cut, so they must NOT appear in the derived family.
    #
    # EXECUTED, and it fired by a DIFFERENT MECHANISM than first written down,
    # which is why it is recorded rather than described. Removing the `other =>`
    # cut from a mutated copy does NOT make the slice over-read into the
    # declining widths: `str.index` RAISES, the derivation fails closed, and the
    # self-test ERRORS rather than FAILS. Both red CI, so the gate is potent
    # either way -- but the claim "if the slice over-reads, this reds" was not
    # the behaviour, and an unexecuted control is how that goes unnoticed.
    ok(not any(v.startswith(("I64", "F32", "F64", "V128")) for v in family),
       "NEGATIVE CONTROL: the derived family contains no declining width (and "
       "removing the `other =>` cut makes the derivation RAISE, not over-read)")

    # POSITIVE CONTROL that the family derivation reads the SOURCE and is not a
    # constant: the i32 family must contain the sign-extending loads, which no
    # fixture exercises and only the source names.
    ok({"I32Load8S", "I32Load16S"} <= family,
       "POSITIVE CONTROL: the family includes sign-extending loads the fixture "
       "never uses, so it is read from the source rather than from the fixture")
    return 0 if fails == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--self-test", action="store_true")
    a = ap.parse_args()
    return self_test() if a.self_test else report()


if __name__ == "__main__":
    sys.exit(main())
