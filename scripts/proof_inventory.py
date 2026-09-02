#!/usr/bin/env python3
"""proof_inventory — the WASM-op -> correctness-theorem manifest (#1057, RQ-60-CFOBLIG inc 2).

WHY THIS EXISTS: gale's `fathom` (and any other consumer) measured proof
coverage of real objects by GUESSING theorem names from WASM rule kinds
(CamelCase -> snake_case: LocalGet -> local_get_correct). Measured against the
tree, that guess FINDS 40 of the 138 `wasm_instr` constructors and MISSES 29
whose theorem exists under a FUSED name (i32_divs_correct, i32_shru_correct,
..., brif_correct — every signed/unsigned div/rem/shift/comparison, both
widths, plus BrIf). `brif_correct` is not the odd one out; it is the 29th
member of a class, so renaming it alone (or all 29) would re-establish a
hand-maintained naming convention for a consumer to re-implement — exactly the
hand-written-mirror failure the North Star forbids ("derive what you check
against from the artifact you ship"). Worse for any name-based guess:

  * theorem names are NOT unique — `i64_shl_correct` names BOTH the T1
    result-correspondence theorem (CorrectnessI64.v) and a T2 existence
    statement (CorrectnessI64Comparisons.v); the (file, name) pair is the key;
  * the `_correct` suffix does not delimit the proof surface — the f32/f64/
    conversion/memory tier lives under `*_executes`, so a `*_correct`-only
    reading calls 69 proven-to-execute ops "absent".

So instead: this script DERIVES a machine-readable inventory from the proof
tree itself and commits it as `artifacts/proof-inventory.json`
(schema `synth-proof-inventory-v2`, following `synth-wcet-v1` practice).
A consumer reads the manifest instead of guessing names; theorem names stop
being load-bearing.

v1 -> v2 (#1057, RQ-61-WASMOP): the v1 universe was the Rocq model's own
constructor set, so every op the model does NOT have — exactly gale's measured
frontier (`End` 64, `Block` 38, `Call` 31, byte-memory 34, `Br` 7,
`Unreachable` 6 of their 180-instance gap) — got NO ROW AT ALL rather than an
explicit "unmodeled" row. In a manifest whose purpose is that absence should
be legible, a missing row is the one thing it must not do. v2's universe is
the shipped `WasmOp` enum (crates/synth-core/src/wasm_op.rs) — the IR every
accepted function is decoded into — so every op a consumer can meet in a
synth-compiled object has a row; rows whose op has no `wasm_instr` constructor
carry `"modeled": false`. Row key is `"op"`; `"constructor"` remains (the
Rocq constructor when modeled, null otherwise) so a v1 consumer keyed on
`constructor` reads v2 unchanged for every modeled op.

METHOD — static, textual, a heuristic labelled as one (the
model_coverage_audit.py / #867 shape):

  Universe: the `WasmOp` variants of crates/synth-core/src/wasm_op.rs, PARSED
  from the file (never hand-listed — a hand-kept list would be one more
  mirror), in declaration order, with the same tokenization as the tested
  scanner in selector_stack_effect_no_wildcard_946.rs. Scope, stated: this is
  "every op an ACCEPTED module can carry", not "every op wasm 3.0 defines" —
  an operator with no `WasmOp` variant (reference types, table ops,
  memory.init/data.drop, atomics, most of SIMD) falls through the decoder's
  `_ => None` and loud-skips its function at decode, so it can produce no
  instance for a consumer to meet. `MultiMemory` is decoder-synthesized (it
  wraps a non-zero-memory-index access), not a wasm opcode itself.

  Model join: a `WasmOp` variant is `modeled` iff a `wasm_instr` constructor
  of coq/Synth/WASM/WasmInstructions.v (still PARSED, still declaration-order)
  carries the identical name — an exact-name JOIN of two parsed shipped
  artifacts, not a derived naming convention (nothing is CamelCase-mangled).
  Every constructor MUST name a variant or this script REFUSES: a model
  constructor with no shipped op (a rename, a model-only addition) is a loud
  red, never a silently dropped row.

  Binding — by what the statement APPLIES, never by deriving a name: a
  Theorem/Lemma/Example DISCHARGES a constructor C when its STATEMENT (the
  text between the name and `Proof`, comment-stripped) BOTH

    (a) applies the WASM-side executor or compiler to C as a SINGLE
        instruction:
          exec_wasm_instr C ...      exec_wasm_instr (C ...) ...
          compile_wasm_to_arm C      compile_wasm_to_arm (C ...)
          exec_wasm_seq [C ...]      exec_wasm_seq ([C ...])   (singleton)
    (b) runs the ARM-side executor (exec_program / exec_program_br /
        exec_program_pc) — i.e. it states a WASM->ARM correspondence.

  (b) excludes WASM-side-only lemmas (WasmCertBridge refinements, type
  preservation) that execute C but say nothing about compiled code.
  Multi-instruction `exec_wasm_seq` program examples deliberately do NOT
  bind: a concrete-program theorem must not mark an op "covered".

  Strength — SEMANTIC, per binding theorem: "existence-only" when the
  conclusion's existential over the ARM result state asserts nothing beyond
  `exec_program ... = Some astate'` (the T2 shape of coq/STATUS.md);
  "result-correspondence" when it further constrains the post-state
  (a `/\\` conjunction, `get_reg`, or `state_correspondence` in the
  existential's scope, or no bare existential at all — the T1 shape).
  Measured against the tree this classifier exposes what the suffix
  convention hides: some `*_correct` names carry existence-only statements.

  Per op:
    modeled               true iff the Rocq model has the constructor.
    status                "unmodeled" when modeled is false (no constructor,
                          so no obligation is even statable — the honest row
                          #1057 asked for);
                          "qed" if >= 1 binding theorem ends `Qed.`;
                          "admitted" if bindings exist but none reach Qed;
                          "absent" if a constructor exists but nothing binds
                          (today: none — every constructor is bound at least
                          at existence tier).
    result_correspondence true iff >= 1 Qed'd binding theorem is
                          result-correspondence — the honest per-op frontier
                          (69 of the 138 modeled ops today are existence-only
                          or weaker; the 141 unmodeled rows are false by
                          construction).

HONESTY / RESIDUAL, stated up front:

  * This parser is a SECOND READER of the proof tree. It can print "Qed" for
    text the Rocq kernel would reject. The manifest is only meaningful
    alongside a green `bazel test //coq:verify_proofs` — the kernel is the
    oracle; this file is an index into it, not a substitute for it.
  * What bounds parser drift: (1) `_meta.cross_check.rocq_qed_total` re-counts
    `Qed.` over coq/Synth/**/*.v in THIS script's own code path, and is
    pinned EQUAL to the claim ledger's independent rocq_qed derivation
    by claims.yaml (SYNTH-PROOF-INVENTORY-CROSSCHECK-1057, `fields-equal`) —
    if the two readers disagree, CI is RED, not reconciled by hand.
    (2) `_meta.cross_check.wasm_op_total` is likewise pinned EQUAL to the
    independently hand-pinned `WASM_OP_VARIANT_COUNT` of
    crates/synth-synthesis/tests/selector_stack_effect_no_wildcard_946.rs
    (SYNTH-PROOF-INVENTORY-UNIVERSE-1057) — a broken variant parser here
    disagrees with a constant a Rust test re-verifies against the same
    source, and CI is RED. (3) The committed artifact is byte-compared
    against re-derivation on every CI run (`--check`, claim-check job), so a
    renamed/added/removed theorem — or a new `WasmOp` variant — without a
    regenerated manifest is RED.
  * Non-vacuity floors (this script REFUSES to green): >= 250 WasmOp
    variants parsed (no duplicates), >= 100 constructors parsed, every
    constructor naming a variant, >= 50 bound, >= 40 result-correspondence,
    >= 1 qed. An empty or gutted manifest cannot pass, and neither half of
    the universe (modeled or unmodeled) can silently vanish — the #1113
    class of a floor that sees only half of what it asserts.
  * The strength classifier is textual: an existential phrased through an
    alias, or a post-state constraint spelled without `/\\`/get_reg/
    state_correspondence, would misclassify (none exist today). The per-entry
    theorem list is the audit trail for borderline cases; tier language
    (T1/T2) is coq/STATUS.md's.

USAGE:
  scripts/proof_inventory.py            re-derive, print the report, and
                                        REWRITE artifacts/proof-inventory.json
  scripts/proof_inventory.py --check    re-derive and FAIL (exit 1) if the
                                        committed artifact differs — the CI
                                        freshness gate (claim-check job)
"""

import json
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
ARTIFACT = ROOT / "artifacts" / "proof-inventory.json"
WASM_INSTRUCTIONS = "coq/Synth/WASM/WasmInstructions.v"
WASM_OP_RS = "crates/synth-core/src/wasm_op.rs"
COQ_GLOB = "coq/Synth"

SCHEMA = "synth-proof-inventory-v2"

# Non-vacuity floors — the manifest must refuse to green when gutted.
MIN_WASM_OPS = 250
MIN_CONSTRUCTORS = 100
MIN_BOUND = 50
MIN_RESULT = 40


def strip_coq_comments(text):
    """Remove (* ... *) comments, nesting-aware (same routine shape as
    model_coverage_audit.py). Coq string literals are not handled specially —
    none in this tree contain comment delimiters."""
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


def wasm_instr_constructors(text):
    """Constructor names of `Inductive wasm_instr`, in declaration order."""
    code = strip_coq_comments(text)
    m = re.search(r"Inductive wasm_instr\s*:\s*Type\s*:=(.*?wasm_instr\.)", code, re.S)
    if not m:
        raise SystemExit("proof_inventory: could not parse Inductive wasm_instr")
    names = re.findall(r"^\s*\|\s*([A-Za-z0-9_']+)\s*:", m.group(1), re.M)
    if len(names) < MIN_CONSTRUCTORS:
        raise SystemExit(
            f"proof_inventory: implausibly few wasm_instr constructors "
            f"({len(names)} < {MIN_CONSTRUCTORS}) — parser drift, refusing to green"
        )
    return names


def wasm_op_variants(text):
    """Top-level variant names of `pub enum WasmOp`, in declaration order.

    Same tokenization as the tested Rust scanner in
    selector_stack_effect_no_wildcard_946.rs: strip `//` comments, walk the
    enum body line by line tracking `{`/`}` depth, and at depth 0 take a
    leading identifier that starts uppercase and is followed by `{`, `(`,
    `,` or `}`. The count is cross-pinned against that test's hand-pinned
    WASM_OP_VARIANT_COUNT via claims.yaml (fields-equal), so the two readers
    cannot drift apart silently."""
    body = text.split("pub enum WasmOp {", 1)
    if len(body) != 2:
        raise SystemExit("proof_inventory: could not find `pub enum WasmOp {`")
    names = []
    depth = 0
    for line in body[1].splitlines():
        line = line.split("//", 1)[0]
        stripped = line.strip()
        if depth == 0:
            m = re.match(r"([A-Za-z0-9_]+)\s*([{(,}])", stripped)
            if m and m.group(1)[0].isupper():
                names.append(m.group(1))
        depth += line.count("{") - line.count("}")
        if depth < 0:
            break
    else:
        raise SystemExit("proof_inventory: `pub enum WasmOp` body never closed")
    if len(names) != len(set(names)):
        raise SystemExit(
            "proof_inventory: duplicate WasmOp variant names parsed — "
            "the scanner is confused, refusing to green"
        )
    if len(names) < MIN_WASM_OPS:
        raise SystemExit(
            f"proof_inventory: implausibly few WasmOp variants "
            f"({len(names)} < {MIN_WASM_OPS}) — parser drift, refusing to green"
        )
    return names


def theorem_blocks(code):
    """(name, statement, terminator) for every Theorem/Lemma/Example in
    comment-stripped source. Statement = text up to the `Proof` marker."""
    blocks = []
    for m in re.finditer(
        r"^\s*(?:Theorem|Lemma|Example)\s+([A-Za-z0-9_']+)\s*:(.*?)(Qed\.|Admitted\.|Defined\.|Abort\.)",
        code,
        re.S | re.M,
    ):
        name, body, ending = m.groups()
        stmt = body.split("Proof", 1)[0]
        blocks.append((name, stmt, ending.rstrip(".")))
    return blocks


ARM_SIDE = re.compile(r"\bexec_program(?:_br|_pc)?\b")


def anchors_constructor(stmt, ctor):
    """True iff the statement applies the WASM executor/compiler to `ctor` as
    a single instruction (see module docstring for the exact forms)."""
    c = re.escape(ctor)
    # exec_wasm_instr C | exec_wasm_instr (C ...)
    # compile_wasm_to_arm C | compile_wasm_to_arm (C ...)
    single = re.compile(r"\b(?:exec_wasm_instr|compile_wasm_to_arm)\s*\(?\s*%s\b" % c)
    if single.search(stmt):
        return True
    # exec_wasm_seq over a SINGLETON list literal: [C ...] with no `;` inside.
    for m in re.finditer(r"\bexec_wasm_seq\s*\(?\s*\[([^\]]*)\]", stmt):
        inner = m.group(1)
        if ";" in inner:
            continue  # multi-instruction program — deliberately non-binding
        if re.match(r"\s*\(?\s*%s\b" % c, inner):
            return True
    return False


def strength(stmt):
    """SEMANTIC strength of a binding statement — see module docstring."""
    m = re.search(r"exists [^,]*astate'[^,]*,", stmt)
    if not m:
        # no bare existential over the ARM result state: the conclusion is a
        # direct executor equation (brif_correct's exec_program_pc shape)
        return "result-correspondence"
    tail = stmt[m.end() :]
    if "/\\" in tail or "get_reg" in tail or "state_correspondence" in tail:
        return "result-correspondence"
    return "existence-only"


def build():
    constructors = wasm_instr_constructors((ROOT / WASM_INSTRUCTIONS).read_text())
    ops = wasm_op_variants((ROOT / WASM_OP_RS).read_text())

    # The model join is exact-name over two PARSED artifacts. A constructor
    # that names no shipped op would silently drop a row — refuse instead.
    orphans = [c for c in constructors if c not in set(ops)]
    if orphans:
        raise SystemExit(
            f"proof_inventory: wasm_instr constructor(s) with no WasmOp "
            f"variant of the same name: {' '.join(orphans)} — a model-side "
            f"rename or model-only op; the join is broken, refusing to green"
        )

    rocq_qed_total = 0
    blocks = []  # (name, stmt, terminator, relpath)
    for p in sorted((ROOT / COQ_GLOB).rglob("*.v")):
        raw = p.read_text()
        rocq_qed_total += len(re.findall(r"Qed\.", raw))
        code = strip_coq_comments(raw)
        rel = str(p.relative_to(ROOT))
        for name, stmt, term in theorem_blocks(code):
            if ARM_SIDE.search(stmt):
                blocks.append((name, stmt, term, rel))

    modeled_set = set(constructors)
    entries = []
    for op in ops:
        modeled = op in modeled_set
        if modeled:
            thms = [
                {
                    "name": name,
                    "file": rel,
                    "terminator": term,
                    "strength": strength(stmt),
                }
                for name, stmt, term, rel in blocks
                if anchors_constructor(stmt, op)
            ]
            thms.sort(key=lambda t: (t["file"], t["name"]))
            if any(t["terminator"] == "Qed" for t in thms):
                status = "qed"
            elif thms:
                status = "admitted"
            else:
                status = "absent"
            result = any(
                t["terminator"] == "Qed" and t["strength"] == "result-correspondence"
                for t in thms
            )
        else:
            thms = []
            status = "unmodeled"
            result = False
        entries.append(
            {
                "op": op,
                "constructor": op if modeled else None,
                "modeled": modeled,
                "status": status,
                "result_correspondence": result,
                "theorems": thms,
            }
        )

    summary = {"total": len(entries)}
    for e in entries:
        summary[e["status"]] = summary.get(e["status"], 0) + 1
    summary["modeled"] = sum(1 for e in entries if e["modeled"])
    summary["result_correspondence"] = sum(
        1 for e in entries if e["result_correspondence"]
    )

    if summary["modeled"] != len(constructors):
        raise SystemExit(
            f"proof_inventory: {summary['modeled']} modeled rows != "
            f"{len(constructors)} parsed constructors — the join lost a row, "
            f"refusing to green"
        )

    bound = summary["modeled"] - summary.get("absent", 0)
    if bound < MIN_BOUND:
        raise SystemExit(
            f"proof_inventory: only {bound} constructors bound to a theorem "
            f"(< {MIN_BOUND}) — either the proof tree collapsed or the binding "
            f"heuristic broke; refusing to green"
        )
    if summary["result_correspondence"] < MIN_RESULT:
        raise SystemExit(
            f"proof_inventory: only {summary['result_correspondence']} "
            f"result-correspondence constructors (< {MIN_RESULT}) — refusing to green"
        )
    if summary.get("qed", 0) < 1:
        raise SystemExit("proof_inventory: zero qed bindings — refusing to green")

    return {
        "_meta": {
            "schema": SCHEMA,
            "issue": 1057,
            "generated_by": "scripts/proof_inventory.py (re-run it; do not hand-edit)",
            "universe": "WasmOp variants (crates/synth-core/src/wasm_op.rs), "
            "parsed from the file in declaration order — the shipped IR every "
            "accepted function is decoded into; rows are modeled:true iff a "
            "wasm_instr constructor of the same name exists in "
            "coq/Synth/WASM/WasmInstructions.v (also parsed; every constructor "
            "must name a variant or generation refuses)",
            "binding": "a theorem discharges a constructor when its STATEMENT "
            "applies exec_wasm_instr / compile_wasm_to_arm / singleton "
            "exec_wasm_seq to that constructor AND runs the ARM-side executor "
            "(exec_program / _br / _pc) — bound by what the statement APPLIES, "
            "never by deriving a name (the fused-vs-underscored naming split, "
            "brif_correct included, is deliberately irrelevant here)",
            "honesty": [
                "This manifest is an INDEX into the proof tree, produced by a "
                "second textual reader. It can say Qed about text the Rocq "
                "kernel would reject: it is only meaningful alongside a green "
                "`bazel test //coq:verify_proofs`.",
                "cross_check.rocq_qed_total is pinned EQUAL to the claim "
                "ledger's independent rocq_qed derivation (claims.yaml "
                "fields-equal) — two readers of the tree that disagree turn "
                "CI red rather than being reconciled by hand.",
                "Theorem names are NOT unique across files (i64_shl_correct "
                "names two different statements); the (file, name) pair is "
                "the key. Do not match on names.",
                '"modeled": false means the Rocq model has NO constructor for '
                "this op — no correctness obligation is even statable about "
                "it yet. That is the honest per-op frontier one tier below "
                '"existence-only": unproved because unmodeled, stated as a '
                "row instead of as a missing row (#1057).",
                "Universe scope: WasmOp is every op an ACCEPTED module can "
                "carry, not every op wasm 3.0 defines — an operator with no "
                "WasmOp variant loud-skips its function at the decoder's "
                "`_ => None` and can produce no instance for a consumer to "
                "meet. MultiMemory is decoder-synthesized (a non-zero-memory-"
                "index wrapper), not a wasm opcode itself.",
                '"result_correspondence": false with status "qed" means the '
                "op is proven to EXECUTE (the T2 tier of coq/STATUS.md) but "
                "no Qed'd theorem pins its result — the honest per-op "
                "frontier. strength is a semantic classification of each "
                "statement, not a reading of its name: some *_correct names "
                "carry existence-only statements.",
                "Consumers: read this file (fetch it from the tagged tree, "
                "e.g. raw.githubusercontent.com/pulseengine/synth/<tag>/"
                "artifacts/proof-inventory.json) instead of deriving theorem "
                "names from rule kinds — 29 of the 138 constructors have "
                "fused names a CamelCase->snake_case guess misses, and the "
                "suffix conventions do not delimit the proof surface.",
                'v1 -> v2: the row key is "op" and the universe is the '
                "shipped WasmOp enum; \"constructor\" remains on every row "
                "(null when unmodeled), so a consumer keyed on constructor "
                "reads v2 unchanged for every modeled op.",
            ],
            "cross_check": {
                "rocq_qed_total": rocq_qed_total,
                "wasm_op_total": len(ops),
            },
        },
        "summary": summary,
        "entries": entries,
    }


def render(data):
    return json.dumps(data, indent=2, sort_keys=True) + "\n"


def report(data):
    s = data["summary"]
    print("proof_inventory (#1057) — WASM-op -> correctness-theorem manifest")
    print(f"  schema: {data['_meta']['schema']}")
    print(f"  ops: {s}")
    print(
        f"  cross-check rocq_qed_total: "
        f"{data['_meta']['cross_check']['rocq_qed_total']}"
        f"  wasm_op_total: {data['_meta']['cross_check']['wasm_op_total']}"
    )
    existence_only = [
        e["op"]
        for e in data["entries"]
        if e["status"] == "qed" and not e["result_correspondence"]
    ]
    print(
        f"  proven-to-execute but result unpinned "
        f"(existence-only frontier, {len(existence_only)}):"
    )
    for i in range(0, len(existence_only), 8):
        print("    " + " ".join(existence_only[i : i + 8]))
    unmodeled = [e["op"] for e in data["entries"] if not e["modeled"]]
    print(
        f"  no Rocq constructor — no obligation statable "
        f"(unmodeled frontier, {len(unmodeled)}):"
    )
    for i in range(0, len(unmodeled), 8):
        print("    " + " ".join(unmodeled[i : i + 8]))
    absent = [e["op"] for e in data["entries"] if e["status"] == "absent"]
    if absent:
        print(f"  absent ({len(absent)}): " + " ".join(absent))


def main():
    check = "--check" in sys.argv[1:]
    data = build()
    text = render(data)
    report(data)
    if check:
        if not ARTIFACT.exists():
            print(
                f"\nFAIL: {ARTIFACT.relative_to(ROOT)} missing — run "
                f"scripts/proof_inventory.py and commit it"
            )
            sys.exit(1)
        if ARTIFACT.read_text() != text:
            print(
                f"\nFAIL: {ARTIFACT.relative_to(ROOT)} is STALE or hand-edited — "
                f"re-run scripts/proof_inventory.py and commit the result"
            )
            sys.exit(1)
        print(f"\nok: {ARTIFACT.relative_to(ROOT)} matches re-derivation")
    else:
        ARTIFACT.parent.mkdir(parents=True, exist_ok=True)
        ARTIFACT.write_text(text)
        print(f"\nwrote {ARTIFACT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
