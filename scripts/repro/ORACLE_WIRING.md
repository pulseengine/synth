# Oracle wiring — every repro script declares its CI status (#890)

`scripts/repro/*.py` are synth's **execution oracles**: the differentials that
run compiled output under unicorn/wasmtime and catch silent miscompiles. They
are the reason several whole classes of defect (#757 wrong-segment static data,
#220 RV32 callee-saved, #518 i64 params) were found at all.

Writing an oracle and **wiring** an oracle are two separate steps, and the second
is the one that gets dropped under release pressure. Before this gate, **69 of
150** repro scripts were referenced by no workflow at all — and nothing in the
tree distinguished

> *manual by design* — needs gale's pinned vendor drop, real silicon, a licensed
> input, or a toolchain CI does not install

from

> *somebody forgot*.

A forgotten gate is indistinguishable from an intentional one, so the only way to
tell was to read all 150 scripts and reason about each — an audit that kept
rediscovering the same defect one instance at a time. v0.53 hand-wired three of
them and **the unwired count still went up**: the instances were fixed, the
factory that produces them was not. One of the three had a green PR board while
its central gate was inert, so the claim it backed was hand-checked only.

## The mechanism

Every `scripts/repro/*.py` and `*.sh` carries **exactly one** declaration line,
conventionally on the line after the shebang:

```python
#!/usr/bin/env python3
# ci-status: wired
```
```python
# ci-status: manual (external-input) — needs gale's merged.both.loom.wat, fetched
# at run time from a gist that is not in-tree and not vendored; ...
```
```python
# ci-status: unwired — no blocker, just not wired yet: <what it would take>
```

`scripts/oracle_wiring_check.py` enforces it, and runs as a step of the
**`claim-check`** CI job.

### Why a header comment, not a manifest file

* **Locality.** The declaration lives in the file it describes, so it appears in
  the diff of the PR that adds the script. An author cannot add an oracle
  without meeting the convention.
* **No second source of truth.** A manifest entry can outlive its script (rename,
  delete) and is edited far from the thing it describes. A header cannot drift
  from its own file.
* The repo already reserves the central-ledger shape (`claims.yaml`) for claims
  that have *no natural home* — prose spread across many docs. A script's CI
  status has a natural home: the script. `claims.yaml` is still used here, but
  only for the one thing a header cannot express: the **ratchet** on the totals.

### Three statuses, on purpose

| status | meaning | checked |
|---|---|---|
| `wired` | at least one `.github/workflows/*.yml` references the file by name | **verified** — declaring `wired` with no workflow reference is a hard failure |
| `manual` | legitimately not CI-runnable | needs a category from a closed set **and** a real reason; must NOT be referenced by a workflow |
| `unwired` | known debt: no blocker, simply not wired yet | needs a reason saying what it would take |

`manual` and `unwired` are separate so that **honest blockers and backlog cannot
hide inside each other**. Undeclared is a failure: a new oracle is forced to
choose.

The `manual` categories are a closed set (`hardware`, `toolchain`,
`external-input`, `network`, `measurement`, `superseded`, `red-first`, `scratch`,
`slow`) declared in the gate script, so the manual surface stays groupable and
arguable instead of becoming a free-text dumping ground. Adding a category is a
deliberate code change.

## The ratchet

The totals are pinned in `claims.yaml` (`SYNTH-ORACLE-WIRING-890`) so they can be
argued **down** over time and cannot grow silently:

- **145 wired** — a floor (`count-min`). The surface cannot be emptied by
  deleting oracles instead of fixing them.
- **7 manual** — a ceiling (`count-max`). An eighth needs a conversation, not a
  commit.
- **0 unwired** — a ceiling of zero. Any new un-wired oracle is a **red build**,
  not a silent backlog entry.

The gate also writes a table (and the unwired-debt list) to
`$GITHUB_STEP_SUMMARY`, so the backlog is visible on every run rather than only
in a log nobody opens.

## The manual seven

| script | category | why |
|---|---|---|
| `wake_path_differential.py` | external-input | needs gale's `merged.both.loom.wat`, fetched from a gist; the WAKE path cannot be reproduced from any in-repo fixture (the debugger perturbs the race on silicon) |
| `size_attribution_390.py` | measurement | prints the #390 size-attribution table; the numbers are pinned by `crates/synth-cli/tests/size_attribution_390.rs`, which *is* the gate |
| `local_promotion_headroom.py` | measurement | #390 scoping spike; no expected values, no verdict. The lever it sized is gated by the wired `local_promote_i32_differential.py` |
| `vcr_dec_001_join_alloc_measure.py` | measurement | the #242 join-allocator ON-vs-OFF comparison deliverable; deliberately has no verdict |
| `spill_baseline_measure.sh` | measurement | VCR-PERF-001 Pass-1 spill-waste census; changes zero codegen bytes, no expected values |
| `run204_unicorn.py` | scratch | #204 bring-up probe, hardcoded `/tmp/gz.bin` + hand-transcribed stub offsets from one historical disassembly; asserts nothing |
| `i64_load_store_372_differential.py` | scratch | 25-line print-only probe; superseded as a gate by the wired `i64_large_offset_382` / `load_store_big_offset_382` differentials |

## Anti-vacuity — the gate must not become the thing it polices

The gate is CI-wired in the same commit that introduced it, as a step of the
**already-required** `claim-check` job. A brand-new job is not a required context
on `main`, so it could sit red for weeks without blocking anything — the same
failure mode the gate exists to kill.

The step uses `set -euo pipefail` **explicitly** and does not take its verdict
from exit 0: it re-reads the JSON summary the gate wrote and asserts a non-empty
script set, a non-zero `wired` count, and zero `undeclared` /
`wired_unreferenced` / `failures`.

`-e` is not decoration. It was added *because a mutation caught its absence*:
with `pipefail` alone, the shell's status is its **last** command's, so the
inert-gate mutation greened the step while the gate itself printed `FAIL` and
exited 1. `wired_unreferenced` was added to the summary in the same fix, so the
verdict is reachable from the summary alone.

### Red-first mutation evidence

Each run below executes the Oracle-wiring step **extracted verbatim from
`ci.yml`** (`yaml.safe_load` → the step's `run:` block → `bash -e`), so there is
no transcription drift between what was proved and what CI runs.

```
===== BASELINE =====
STEP EXIT=0
all repro scripts declare a CI status, and every `wired` one is wired.
oracle-wiring gate is non-vacuous: it classified 152 scripts, 145 of them wired,
7 manual, 0 unwired-debt, 0 inert.

===== MUTATION 1: un-declare mem757_ptr_base_copy_differential.py =====
STEP EXIT=1
FAIL scripts/repro/mem757_ptr_base_copy_differential.py: UNDECLARED — add a
`# ci-status:` header line ... An oracle nothing runs must SAY so.

===== MUTATION 2: declare `wired` on wake_path (no workflow reference) =====
STEP EXIT=1
FAIL scripts/repro/wake_path_differential.py: declares `wired` but NO workflow
references it — the gate is INERT.

===== MUTATION 3: delete a wired oracle's CI step (re-inert it) =====
STEP EXIT=1
FAIL scripts/repro/mem757_low_const_copy_differential.py: declares `wired` but NO
workflow references it — the gate is INERT.

===== MUTATION 4: gate measures nothing (glob matches no scripts) =====
STEP EXIT=1
oracle-wiring gate VACUOUS or DRIFTED ['total<100']: {'total': 2, 'wired': 1, ...}

===== RESTORED =====
STEP EXIT=0
```

Mutation 3 is the one that closes the loop the other way: deleting a CI step
without touching the script no longer silently re-inerts the oracle.

## Adding a repro script

1. Write the harness. Give it **exit-code discipline** — `sys.exit(0 if ok else 1)`.
   A harness that prints `MISMATCH` and exits 0 is a gate that cannot fail
   (`sret_decide_differential.py` was exactly that until #890).
2. Read the binary under test from `$SYNTH` (`os.environ.get("SYNTH", ...)`), so
   CI can point it at its own build.
3. Add a CI step and declare `# ci-status: wired`; or declare `manual (<category>)`
   / `unwired` with a real reason and bump `SYNTH-ORACLE-WIRING-890` in
   `claims.yaml`.
