#!/usr/bin/env python3
# ci-status: wired
# ci-checks: emulations >= 1200
"""VCR-TIER-001 increment 1 (#1021/#1048) — the pseudo-op expansion canary gate.

WHY THIS EXISTS. 52 of the 80 Rocq-proved VCR-SEL-001 rules emit a PSEUDO-OP
whose multi-instruction ENCODER EXPANSION the proof never sees: `ArmSemantics`
executes e.g. `POPCNT` atomically (writes rd only), so a scratch register
borrowed by the expansion is UNREPRESENTABLE in the model. An atomic model of
a multi-instruction expansion is a silent claim that the expansion is
scratch-free — and that claim shipped false twice, across two register tiers:

  * reserved-global tier — #1021: `i32.popcnt` borrowed R11, the WASM
    linear-memory base, and leaked it to every caller (memory corruption
    through a proved rule; fixed #1039);
  * caller-operand tier — #1048: the i64 shifts masked the amount IN PLACE and
    wrote amt-32 into the amount's home high register, and the i64 bit-counts
    cleared the OPERAND's home high register (fixed with #1054). The wired
    `i64_shr_599` value differential PASSED on the miscompiling binary — every
    fixture consumed the result immediately and never re-read the destroyed
    registers, so the value tier is STRUCTURALLY BLIND to this class.

THE GATE. Every `ArmOp` variant the shipped rule table emits (the census dump
example, completeness-gated against `sel_dsl/generated.rs`) is encoded by the
REAL Thumb-2 and A32 encoders and EXECUTED under unicorn with every
non-operand register holding a distinctive canary (R11 = 0xB11B11B1, one
recognizable value per register) over the census's operand valuations —
including the non-fixed-point shift amount (0x67) that exposes in-place amount
masking. After completion the gate asserts, per instance, per backend:

  1. every register outside {declared results} ∪ {declared scratch contract}
     ∪ {R12, the globally sanctioned encoder scratch} holds its exact seeded
     value — nothing else moved;
  2. SP is restored, and memory writes land only in the expansion's own stack
     red-zone below the seeded SP (a store through a corrupted base lands on
     an unmapped canary address and faults the emulator: also red);
  3. the bytes decode completely (capstone) and both backends encode — an
     unencodable variant is a HOLE, not a pass;
  4. every register a contract DECLARES is actually written by at least one
     valuation — an over-broad contract cannot silently hollow the gate.

The contract source is `synth_backend::arm_encoder::expansion_scratch_contract`
— the single declaration site next to the expansions, serialized into the dump
(`scratch_contract`) — never a hand list in this script. A missing declaration
means the STRICTEST contract, results only: exactly the claim the atomic model
already makes. Today every contract is EMPTY (post-#1039/#1054 all expansions
are R12-only), so the census's unguarded-clobber set is pinned at EMPTY here —
stronger than the "does not grow" the census header promised.

POTENCY (the two-reds-two-tiers negative control, run on EVERY invocation):
the committed fixtures expansion_canary_1021_red_pre1039.json (encoders at
708ae34b: #1021 + #1048 both live) and ..._red_pre1054.json (origin/main
c960903e: #1039 in, #1048 not) hold the REAL old encoders' bytes. The gate
must red the first on Popcnt/{r11} and the second on the operand tier while
NOT redding Popcnt there (fix discrimination) — with the observed violation
sets matching the pinned expectations EXACTLY in both directions. A gate that
cannot fail, or that fails on the wrong register, exits 1 itself.

KNOWN NOT COVERED, stated per the census method note: representative-operand
coverage (one non-aliased operand assignment per variant shape — an expansion
defect reachable only under a specific register ALIASING is outside this
instance table; the #1048 home-register defects were operand-POSITION defects,
which non-aliased operands catch); CPSR/flag effects (SetCond consumers read
flags immediately, and the atomic model carries no flag state to contract
against); and the fixed operand valuations (three census sets; a clobber
gated on a value outside them — beyond the masked/large/zero shift paths they
were chosen to cover — would need a new valuation, added in the census, not
here).

Usage:
  python scripts/repro/expansion_canary_gate_1021.py            # all 3 legs
  python scripts/repro/expansion_canary_gate_1021.py --dump F   # gate a dump file
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))

import tier_census_1021 as census  # noqa: E402  (the shared unicorn/capstone runner)

# One recognizable value per non-operand register; R11's is the one the task
# is named for (the #1021 mechanism register). Operand registers r0-r8 take
# the census INPUT_SETS values, distinct per register within the sets.
CANARIES = {
    "r9": 0xB99B99B9,
    "r10": 0xB10B10B1,
    "r11": 0xB11B11B1,
    "r12": 0xB12B12B1,  # sanctioned scratch — seeded for visibility, not asserted
    "lr": 0xB14B14B1,
}
SANCTIONED = {"r12"}
# Push/pop traffic must stay in the expansion's own red-zone below seeded SP.
STACK_WINDOW = range(census.SP_INIT - 0x200, census.SP_INIT)

FIX_PRE1039 = ROOT / "scripts/repro/expansion_canary_1021_red_pre1039.json"
FIX_PRE1054 = ROOT / "scripts/repro/expansion_canary_1021_red_pre1054.json"

# The pinned expectations for the negative-control fixtures: variant ->
# exact violating-register set, identical on both backends (measured from the
# real old encoders' bytes at fixture creation; see each fixture's provenance).
EXPECT_PRE1039 = {
    "Popcnt": {"r11"},  # reserved-global tier — the #1021 mechanism
    "I64Shl": {"r4", "r5"},  # caller-operand tier — the #1048 mechanism
    "I64ShrU": {"r4", "r5"},
    "I64ShrS": {"r4", "r5"},
    "I64Clz": {"r3"},
    "I64Ctz": {"r3"},
    "I64Popcnt": {"r3"},
}
EXPECT_PRE1054 = {k: v for k, v in EXPECT_PRE1039.items() if k != "Popcnt"}


def load_instances(path: Path) -> list[dict]:
    data = json.loads(path.read_text())
    return data["instances"] if isinstance(data, dict) else data


def run_leg(instances: list[dict], leg: str) -> tuple[dict[str, set[str]], list[str], int]:
    """Execute every instance on both backends under canaries.

    Returns (violations per variant, structural failures, pseudo-variant count).
    A violation is a net register change outside the instance's declared
    results + scratch contract + sanctioned R12.
    """
    violations: dict[str, set[str]] = {}
    structural: list[str] = []
    max_insns: dict[str, int] = {}
    contract_hit: dict[str, set[str]] = {}
    contract_all: dict[str, set[str]] = {}

    for inst in instances:
        v = inst["variant"]
        # Missing declaration == the strictest contract: results only.
        contract = set(inst.get("scratch_contract", []))
        allowed = set(inst["outputs"]) | contract | SANCTIONED
        contract_all.setdefault(v, set()).update(contract)
        for isa, key in (("thumb2", "thumb"), ("a32", "a32")):
            where = f"{leg}:{v}:{inst['shape']}:{isa}"
            if not inst[key]:
                structural.append(f"{where}: ENCODE FAILED ({inst[key + '_err']}) — an unencodable variant is a hole, not a pass")
                continue
            code = bytes.fromhex(inst[key])
            n, _, _ = census.static_writes(code, thumb=isa == "thumb2")
            max_insns[v] = max(max_insns.get(v, 0), n)
            ex = census.execute(code, thumb=isa == "thumb2", ambient=CANARIES)
            if ex["errors"]:
                structural.append(f"{where}: emulation fault {ex['errors']} (a store through a clobbered base faults on the unmapped canary address)")
                continue
            if not ex["sp_restored"]:
                structural.append(f"{where}: SP not restored")
            bad_mem = [a for a in ex["mem_writes"] if a not in STACK_WINDOW]
            if bad_mem:
                structural.append(f"{where}: memory writes outside the stack red-zone: {[hex(a) for a in bad_mem]}")
            contract_hit.setdefault(v, set()).update(ex["net_clobbers"] & contract)
            bad = ex["net_clobbers"] - allowed
            if bad:
                violations.setdefault(v, set()).update(bad)
    # Anti-over-declaration: a declared scratch register the expansion never
    # actually writes would let a future defect hide under a stale contract.
    for v, declared in contract_all.items():
        unused = declared - contract_hit.get(v, set())
        if unused:
            structural.append(
                f"{leg}:{v}: contract declares {sorted(unused)} but no valuation observed a write — an over-broad contract hollows the gate; tighten the declaration"
            )
    pseudo = sum(1 for v, n in max_insns.items() if n > 1)
    return violations, structural, pseudo


def fmt(viol: dict[str, set[str]]) -> str:
    return "; ".join(f"{v}:{sorted(r)}" for v, r in sorted(viol.items())) or "NONE"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--dump", help="gate an existing dump JSON (skips the live + fixture legs)")
    args = ap.parse_args()
    failures: list[str] = []

    if args.dump:
        inst = load_instances(Path(args.dump))
        viol, structural, pseudo = run_leg(inst, "dump")
        print(f"dump leg: {len(inst)} instances, {pseudo} pseudo variants")
        print(f"violations: {fmt(viol)}")
        for s in structural:
            print(f"structural: {s}")
        sys.exit(1 if viol or structural else 0)

    # ---- leg 1: the LIVE encoders (cargo run of the census dump example) ----
    live = census.run_dump(None)
    viol, structural, pseudo = run_leg(live, "live")
    print(f"live leg: {len(live)} instances, {pseudo} pseudo variants (both backends, canaried)")
    print(f"live violations beyond contract: {fmt(viol)}")
    if viol:
        failures.append(f"LIVE RED — undeclared expansion clobbers: {fmt(viol)}")
    failures.extend(f"LIVE STRUCTURAL — {s}" for s in structural)
    # Non-vacuity floors: the dump example is completeness-gated against
    # generated.rs, so shrinkage here means the gate lost its subject.
    if len(live) < 70:
        failures.append(f"VACUOUS — only {len(live)} instances (expected >= 70)")
    if pseudo < 19:
        failures.append(f"VACUOUS — only {pseudo} pseudo-op variants executed (expected >= 19)")
    for anchor in ("Popcnt", "I64Shl"):
        if not any(i["variant"] == anchor for i in live):
            failures.append(f"VACUOUS — anchor variant {anchor} missing from the dump")

    # ---- legs 2+3: the negative controls (two tiers, run every time) -------
    for path, expect, tier in (
        (FIX_PRE1039, EXPECT_PRE1039, "reserved-global tier (pre-#1039, R11)"),
        (FIX_PRE1054, EXPECT_PRE1054, "caller-operand tier (pre-#1054, operand regs)"),
    ):
        inst = load_instances(path)
        viol, structural, _ = run_leg(inst, path.stem)
        print(f"{path.name}: violations = {fmt(viol)}")
        if viol != expect:
            missing = {v: r for v, r in expect.items() if viol.get(v, set()) != r}
            extra = {v: sorted(r) for v, r in viol.items() if v not in expect}
            failures.append(
                f"POTENCY FAILED on {tier}: expected exactly {fmt(expect)}, "
                f"observed {fmt(viol)} (unmet: {missing or '-'}; unexpected: {extra or '-'})"
            )
        # The fixtures' structural findings must stay empty too — old
        # expansions restored SP and stayed in-window; a drift here means the
        # checker changed, not the fixture.
        failures.extend(f"{path.name} STRUCTURAL — {s}" for s in structural)

    print()
    if failures:
        print("EXPANSION CANARY GATE: RED")
        for f in failures:
            print(f"  {f}")
        sys.exit(1)
    print(
        "EXPANSION CANARY GATE: GREEN — every rule-emitted expansion is "
        "contract-clean on both backends, and both negative-control tiers red "
        "exactly as pinned"
    )


if __name__ == "__main__":
    main()
