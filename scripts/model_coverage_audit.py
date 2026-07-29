#!/usr/bin/env python3
"""model_coverage_audit — coverage OF the ISA semantics model (#867, phase 2).

The third leg of Sail's own validation methodology (Armstrong et al., POPL
2019 §7: provenance / differential validation / MODEL COVERAGE): measure which
parts of the semantics model any proof actually exercises, and report the
COMPLEMENT loudly — modelled ISA behaviours that no proof touches are the
candidate list for the next #682-class silent miscompile (the Kind 2
`--print_ivc_complement` analogy: everything the proof did not need is
unverified).

HONESTY, up front (kept verbatim from #867): "is my semantics model faithful?"
has no formal solution — provenance + differential validation + model coverage
is the state of the art, not a proof.  And "covered" ≠ "faithful": a
definition exercised by a proof against a simplified model is still only as
good as that model.  This script emits a coverage MAP, not an adequacy metric.

METHOD — static, textual, a heuristic labelled as one:

  Universe 1: the `arm_instr` constructors of `coq/Synth/ARM/ArmInstructions.v`
  (the modelled ISA-behaviour surface of the simplified model). Per
  constructor, three tiers:

    bridge-validated  the constructor token appears (word-boundary, after
                      comment-stripping) in the STATEMENT of a Qed'd
                      `sail_bridge_*` theorem in SailArmBridge.v — i.e. the
                      simplified executor's behaviour for (some form of) this
                      instruction is proven to agree with an ASL-transcribed
                      recomputation. Evidence toward faithfulness, NOT proof
                      of it (the transcription itself is trusted).
    simplified-only   referenced by at least one PROOF-LAYER file (the
                      Correctness*/VcrSel*/Tactics/Compilation/ArmFlagLemmas
                      files) but by NO bridge theorem — a proof exercises the
                      modelled behaviour, but only against the simplified
                      model's own say-so: exactly the #682 shape.
    uncovered         referenced by NO proof-layer file at all — modelled
                      behaviour that no proof exercises.  THE COMPLEMENT.

  Universe 2: the `sail_*` Definitions/Fixpoints of SailArmBridge.v (the
  ASL-transcribed semantic definitions themselves). Tiers: `proof-exercised`
  (referenced outside their own definition by some lemma/theorem in the file)
  vs `unexercised`.

  Tests: NO test executes the Rocq model (the differential/emulation suites
  exercise the COMPILER'S OUTPUT, not the model — the ⚠️ middle row of #867's
  methodology table).  Coverage sources here are therefore Rocq proofs only;
  the artifact records this explicitly rather than implying test coverage.

KNOWN APPROXIMATION ERRORS (both directions, deliberately disclosed):

  * Token matching over comment-stripped source can FALSE-POSITIVE on short
    constructor names (`B`, `AND`, `MOV`...) colliding with binder names — a
    false positive OVERSTATES coverage, so the reported complement is an
    UNDER-approximation of the truly unexercised surface: the real problem
    can only be as big or bigger.
  * It cannot see indirect exercise (a lemma about `exec_instr`'s output used
    by a theorem that never names the constructor) — this direction
    UNDERSTATES coverage.
  * "References in a proof-layer file" includes references from the
    compile-function definitions (Compilation.v, VcrSelRulesGenerated.v):
    an emitted-but-never-proven instruction still counts simplified-only if
    some correctness theorem file mentions it.  The per-entry `refs` list
    says exactly which files matched; judge borderline cases from there.

USAGE:
  scripts/model_coverage_audit.py            re-derive, print the loud report,
                                             and REWRITE artifacts/model-coverage.json
  scripts/model_coverage_audit.py --check    re-derive and FAIL (exit 1) if the
                                             committed artifact differs — the CI
                                             freshness gate (claim-check job)
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ARTIFACT = ROOT / "artifacts" / "model-coverage.json"

ARM_INSTRUCTIONS = "coq/Synth/ARM/ArmInstructions.v"
SAIL_BRIDGE = "coq/Synth/ARM/SailArmBridge.v"

# The proof layer: files whose job is to PROVE things about compiled sequences
# (not the model-definition files themselves — ArmInstructions/ArmSemantics/
# ArmState define the universe being measured and would trivially cover it).
PROOF_LAYER = [
    "coq/Synth/Synth/Compilation.v",
    "coq/Synth/Synth/Correctness.v",
    "coq/Synth/Synth/CorrectnessComplete.v",
    "coq/Synth/Synth/CorrectnessConversions.v",
    "coq/Synth/Synth/CorrectnessF32.v",
    "coq/Synth/Synth/CorrectnessF64.v",
    "coq/Synth/Synth/CorrectnessI32.v",
    "coq/Synth/Synth/CorrectnessI64.v",
    "coq/Synth/Synth/CorrectnessI64Comparisons.v",
    "coq/Synth/Synth/CorrectnessMemory.v",
    "coq/Synth/Synth/CorrectnessSimple.v",
    "coq/Synth/Synth/Tactics.v",
    "coq/Synth/Synth/VcrSelExpansion.v",
    "coq/Synth/Synth/VcrSelPilot.v",
    "coq/Synth/Synth/VcrSelRules.v",
    "coq/Synth/Synth/VcrSelRulesGenerated.v",
    "coq/Synth/ARM/ArmFlagLemmas.v",
    "coq/Synth/ARM/SailArmBridge.v",
]


def strip_coq_comments(text):
    """Remove (* ... *) comments, nesting-aware. Strings are not handled
    specially (Coq string literals are rare in this tree and none contain
    comment delimiters)."""
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("(*", i):
            depth += 1
            i += 2
        elif depth and text.startswith("*)", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


def arm_instr_constructors(text):
    """Constructor names of `Inductive arm_instr`, in declaration order."""
    code = strip_coq_comments(text)
    # capture to the Inductive's terminating period: every constructor line
    # ends `... -> arm_instr` and only the last ends `arm_instr.`
    m = re.search(r"Inductive arm_instr\s*:\s*Type\s*:=(.*?arm_instr\.)", code, re.S)
    if not m:
        raise SystemExit("model_coverage_audit: could not parse Inductive arm_instr")
    body = m.group(1)
    names = re.findall(r"^\s*\|\s*([A-Za-z0-9_']+)\s*:", body, re.M)
    if len(names) < 40:
        raise SystemExit(
            f"model_coverage_audit: implausibly few arm_instr constructors "
            f"({len(names)}) — parser drift, refusing to green"
        )
    return names


def qed_blocks(text):
    """(name, statement, kind) for every Theorem/Lemma ending in Qed."""
    code = strip_coq_comments(text)
    blocks = []
    for m in re.finditer(
        r"^(Theorem|Lemma)\s+([A-Za-z0-9_']+)\s*:(.*?)(Qed\.|Admitted\.|Defined\.)",
        code,
        re.S | re.M,
    ):
        kind, name, body, ending = m.groups()
        # statement = up to the Proof. marker (or the whole body if inlined)
        stmt = body.split("Proof", 1)[0]
        if ending == "Qed.":
            blocks.append((name, stmt))
    return blocks


def sail_definitions(text):
    code = strip_coq_comments(text)
    return re.findall(r"^(?:Definition|Fixpoint)\s+(sail_[A-Za-z0-9_']+)", code, re.M)


def build():
    instr_text = (ROOT / ARM_INSTRUCTIONS).read_text()
    bridge_text = (ROOT / SAIL_BRIDGE).read_text()

    constructors = arm_instr_constructors(instr_text)

    # bridge theorems (Qed only) and the constructors their statements name
    bridge_thms = [(n, s) for n, s in qed_blocks(bridge_text) if n.startswith("sail_bridge_")]

    proof_layer_code = {}
    for rel in PROOF_LAYER:
        p = ROOT / rel
        if not p.exists():
            raise SystemExit(f"model_coverage_audit: proof-layer file missing: {rel}")
        proof_layer_code[rel] = strip_coq_comments(p.read_text())

    entries = []
    for name in constructors:
        rx = re.compile(r"\b%s\b" % re.escape(name))
        bridge_hits = sorted(t for t, stmt in bridge_thms if rx.search(stmt))
        refs = sorted(rel for rel, code in proof_layer_code.items() if rx.search(code))
        if bridge_hits:
            tier = "bridge-validated"
        elif refs:
            tier = "simplified-only"
        else:
            tier = "uncovered"
        entries.append(
            {
                "name": name,
                "tier": tier,
                "bridge_theorems": bridge_hits,
                "proof_layer_refs": refs,
            }
        )

    # universe 2: sail_* definitions, exercised by any Qed statement/proof
    # beyond their own definition
    sail_defs = sail_definitions(bridge_text)
    bridge_code = strip_coq_comments(bridge_text)
    sail_entries = []
    for name in sail_defs:
        # occurrences beyond the defining occurrence itself
        uses = len(re.findall(r"\b%s\b" % re.escape(name), bridge_code)) - 1
        sail_entries.append(
            {"name": name, "tier": "proof-exercised" if uses > 0 else "unexercised", "uses": uses}
        )

    def tally(items):
        t = {}
        for e in items:
            t[e["tier"]] = t.get(e["tier"], 0) + 1
        return dict(sorted(t.items()))

    return {
        "_meta": {
            "issue": 867,
            "generated_by": "scripts/model_coverage_audit.py (re-run it; do not hand-edit)",
            "method": "STATIC textual heuristic — see the script docstring for "
            "exactly what is matched and the disclosed false-positive/"
            "false-negative directions. NOT a mechanical adequacy metric.",
            "honesty": [
                '"is my semantics model faithful?" has no formal solution — '
                "provenance + differential validation + model coverage is the "
                "state of the art, not a proof.",
                '"covered" != "faithful": a definition exercised by a proof '
                "against a simplified model is still only as good as that model.",
                "bridge-validated means agreement with an ASL-transcribed "
                "recomputation was PROVEN for some form of the instruction; the "
                "transcription itself is trusted, and coverage of one form does "
                "not cover all forms (the #682 LSL_reg bug was in a covered-"
                "looking family).",
                "The uncovered complement is an UNDER-approximation: token "
                "false-positives can only shrink it, never grow it.",
            ],
            "coverage_sources": {
                "rocq_proofs": True,
                "tests": False,
                "tests_note": "No test executes the Rocq model. The differential/"
                "emulation/silicon suites exercise the COMPILER'S OUTPUT, not the "
                "model (#867's middle methodology row). Model-level differential "
                "against a vendor suite is #867 item 4, explicitly out of scope "
                "for v0.52.",
            },
        },
        "targets": {
            "arm-thumb2-simplified-model": {
                "universe": "arm_instr constructors (coq/Synth/ARM/ArmInstructions.v)",
                "summary": {"total": len(entries), **tally(entries)},
                "entries": entries,
            },
            "sail-bridge-definitions": {
                "universe": "sail_* Definitions/Fixpoints (coq/Synth/ARM/SailArmBridge.v)",
                "summary": {"total": len(sail_entries), **tally(sail_entries)},
                "entries": sail_entries,
            },
        },
    }


def render(data):
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def report(data):
    arm = data["targets"]["arm-thumb2-simplified-model"]
    sail = data["targets"]["sail-bridge-definitions"]
    print("model_coverage_audit (#867) — coverage OF the ISA semantics model")
    print("  method: static textual heuristic (see script docstring); "
          '"covered" != "faithful"')
    print(f"  arm_instr constructors: {arm['summary']}")
    print(f"  sail_* definitions:     {sail['summary']}")

    uncovered = [e["name"] for e in arm["entries"] if e["tier"] == "uncovered"]
    simponly = [e["name"] for e in arm["entries"] if e["tier"] == "simplified-only"]
    unex = [e["name"] for e in sail["entries"] if e["tier"] == "unexercised"]

    print()
    print("  ==== THE COMPLEMENT — modelled ISA behaviours NO proof exercises ====")
    print("  (candidate list for the next #682-class silent miscompile; an")
    print("   UNDER-approximation — heuristic false-positives only shrink it)")
    if uncovered:
        for n in uncovered:
            print(f"    UNCOVERED  {n}")
    else:
        print("    (empty at the constructor granularity — see honesty notes:")
        print("     form-level gaps inside covered families are NOT ruled out)")
    print()
    print(f"  simplified-only (proved, but only against the simplified model — "
          f"the #682 shape): {len(simponly)}")
    print("    " + " ".join(simponly) if simponly else "    (none)")
    if unex:
        print()
        print(f"  unexercised sail_* definitions ({len(unex)}):")
        print("    " + " ".join(unex))


def main():
    check = "--check" in sys.argv[1:]
    data = build()
    text = render(data)
    report(data)
    if check:
        if not ARTIFACT.exists():
            print(f"\nFAIL: {ARTIFACT.relative_to(ROOT)} missing — run "
                  f"scripts/model_coverage_audit.py and commit it")
            sys.exit(1)
        if ARTIFACT.read_text() != text:
            print(f"\nFAIL: {ARTIFACT.relative_to(ROOT)} is STALE or hand-edited — "
                  f"re-run scripts/model_coverage_audit.py and commit the result")
            sys.exit(1)
        print(f"\nok: {ARTIFACT.relative_to(ROOT)} matches re-derivation")
    else:
        ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
        ARTIFACT.write_text(text)
        print(f"\nwrote {ARTIFACT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
