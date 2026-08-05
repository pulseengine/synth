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

"Referenced by a workflow" means referenced by something a runner would
**execute** — a step's `run:` body, or a `with:`/`env:` value — derived from the
*parsed* workflow, not from a raw grep. A mention in a comment does not count: a
gate satisfiable by prose is the failure shape this check exists to reject. (A
workflow that will not parse is a hard error, never a silent pass.)

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

### Red-first evidence — in real CI

M1 and M2 were also proved on a throwaway branch whose only content was the two
mutations, so the failure is a genuine **`Claim Check` job** result on GitHub —
not a local reproduction. That branch was closed unmerged
([PR #895](https://github.com/pulseengine/synth/pull/895),
[run](https://github.com/pulseengine/synth/actions/runs/30545009045/job/90878830002)):

```
oracle wiring: 152 repro scripts — 145 wired, 6 manual, 0 unwired(debt), 1 UNDECLARED
FAIL scripts/repro/mem757_ptr_base_copy_differential.py: UNDECLARED — add a
     `# ci-status:` header line ... An oracle nothing runs must SAY so.
FAIL scripts/repro/wake_path_differential.py: declares `wired` but NO workflow
     references it — the gate is INERT ...
##[error]Process completed with exit code 1.
```

This matters for exactly the reason #890 exists: a gate that has never been seen
to fire is indistinguishable from one that cannot.

### Red-first mutation evidence — the full matrix

Each run below executes the Oracle-wiring step **extracted verbatim from
`ci.yml`** (`yaml.safe_load` → the step's `run:` block → `bash -e`), so there is
no transcription drift between what was proved and what CI runs.

```
===== BASELINE =====
STEP EXIT=0
oracle-wiring gate is non-vacuous: it classified 152 scripts, 145 of them wired,
7 manual, 0 unwired-debt, 0 inert.

===== M1: un-declare mem757_ptr_base_copy_differential.py =====
STEP EXIT=1
FAIL scripts/repro/mem757_ptr_base_copy_differential.py: UNDECLARED — add a
`# ci-status:` header line (wired | manual (<category>) — reason | unwired ...

===== M2: declare `wired` on wake_path (no reference at all) =====
STEP EXIT=1
FAIL scripts/repro/wake_path_differential.py: declares `wired` but NO workflow
STEP runs it — the gate is INERT. Wire it in .github/workflows/, or dow...

===== M3: delete a wired oracle's CI step =====
STEP EXIT=1
FAIL scripts/repro/mem757_low_const_copy_differential.py: declares `wired` but NO
workflow STEP runs it — the gate is INERT. Wire it in .github/workfl...

===== M4: gate glob matches nothing =====
STEP EXIT=1
oracle-wiring gate VACUOUS or DRIFTED ['total<100']: {'failures': 0, 'manual': 1,
'manual_by_category': {'measurement': 1}, 'total': 2, 'undeclared': ...

===== M5: reference demoted to a COMMENT =====
STEP EXIT=1
FAIL scripts/repro/mem757_memmove_param_differential.py: declares `wired` but NO
workflow STEP runs it — the gate is INERT. It IS mentioned in ci.yml, ...

===== M6: manual reason replaced with a placeholder =====
STEP EXIT=1
FAIL scripts/repro/run204_unicorn.py: `manual` needs a REAL reason (>= 20 chars,
not a placeholder); got 'TODO'

===== RESTORED =====
STEP EXIT=0
```

**M3** closes the loop the other way: deleting a CI step without touching the
script no longer silently re-inerts the oracle. **M5** closes it a third way: a
step demoted to a comment still *mentions* the script, and a raw grep would call
that wired — prose does not run an oracle.

`SYNTH-ORACLE-WIRING-890`'s ratchet legs are proved the same way: flipping one
wired script to `manual` fails **both** `count-min 145` (the floor) and
`count-max 7` (the ceiling).

---

# What a wired oracle ATTESTS — the check floors (#910)

`ci-status: wired` says a CI step runs the oracle. It says nothing about what
that step *attests*. Measured on the #890 result:

> **152 of the 160** workflow steps that run a `scripts/repro/` oracle asserted
> nothing beyond the process exit code. Exactly **8** asserted a printed verdict
> or count.

That is not a #890 leftover — the pre-#890 hand-wired steps are mostly in the
152 as well. And exit 0 does not distinguish

> compiled 40 fixtures, emulated 240 vectors, all bit-identical to wasmtime

from

> the fixture list came back empty, the loop body never ran, printed `PASS`

which is #890's inert gate one level down: wired, but silent about its own
content.

## The mechanism — `scripts/oracle_run.py`

Oracle steps run `python scripts/oracle_run.py scripts/repro/<oracle>.py …`
instead of invoking the harness directly. The driver executes it **in process**
(`runpy`) with three entry points wrapped:

| wrapped | counter | what it means |
|---|---|---|
| `unicorn.Uc.emu_start` | `emulations` | a real emulator entry |
| `wasmtime.Func.__call__` | `wasmtime_calls` | a real reference execution |
| `subprocess` `synth … compile …` | `compiles` | a real compilation |

The count comes from the emulator, not from the harness's own bookkeeping, so a
comparison loop that never runs cannot fake it. No harness was edited to get
this.

**Why a driver and not 152 greps.** A bespoke `grep` per step is 152 hand-written
patterns to keep in sync with 150 harnesses' output strings — the mirror-drift
shape this repo keeps paying for. One driver is one thing to maintain, and it
measures the *behaviour* rather than the prose describing it.

**Why not instrument the compiler instead** (#910 option 1: point the
differentials at an `llvm-cov` build and merge profiles). Two reasons. It
changes the artifact under test — these oracles exist to execute the *shipped*
bytes, and an instrumented binary is not those bytes. And it would buy precision
on an axis that is still the wrong instrument: a line percentage cannot answer
"what do the differentials not reach", which is the question worth asking.

## The declaration

One `# ci-checks:` header per oracle, next to its `# ci-status:` line — same
locality argument: it lives in the file it describes, appears in the diff of the
PR that adds the oracle, and cannot outlive its file.

```python
# ci-status: wired
# ci-checks: emulations >= 75
```

| form | use |
|---|---|
| `emulations >= N` | the normal case — a unicorn differential |
| `wasmtime >= N` | reference executions, where those are the countable work |
| `compiles >= N` | oracles whose work is not emulation: decline matrices, byte-identity legs, structural validators |
| `stdout /<rx>/ >= N` | the harness already prints a better count than any of the above; the regex must carry **exactly one** capture group holding an integer, so it asserts a *count* and not the presence of a happy-path string |
| `none — <reason>` | nothing can be bound; needs a real reason (>= 20 chars) |

Declare the **strongest mode that holds on every invocation** of that script.
Several oracles are run twice — once executing, once on a decline or
byte-identity leg that executes nothing by design — and a floor that only holds
for the good leg is not a floor. The weaker floor loses nothing: every counter
is still measured and recorded, so the ledger reports what ran while the gate
asserts what is guaranteed.

Floors are **`>=`, never equality**: adding a fixture must never redden a step.
The ratchet direction is up.

### Calibration — the floors are measured, not guessed

Every floor was obtained by executing each CI oracle step **verbatim** (parsed
out of `ci.yml`, so there is no transcription drift between what was measured
and what CI runs) with the invocation routed through the driver.

The unit is called `emulations`, not "checks", on purpose — but the four oracles
that self-report a check count agree with the driver **1:1**:

| oracle | its own report | driver |
|---|---|---|
| `gpio_thin_846_differential.py` | `#846 CHECKS=75/75` | 75 |
| `aarch64_call_indirect_851_differential.py` | `35 checks (23 trap, 12 value)` | 35 |
| `aarch64_globals_851_differential.py` | `17 checks across 6 exported functions` | 17 |
| `aarch64_float_completion_851_differential.py` | the 662 float-boundary checks | 662 |

Calling the aggregate "checks" on the strength of four agreements would still be
naming a measurement after something it does not measure — the exact defect this
whole lane is about. So the counter keeps the name of the thing it counts.

## The floors, and the ratchet

| mode | oracles | floor total |
|---|---|---|
| `emulations` | **133 oracles** | **294,914 emulator entries** |
| `stdout` | 7 oracles | 458 printed counts |
| `compiles` | 9 oracles | 43 compilations |
| `none` | **1 oracle** | — |

**Reported per mode and never summed across modes.** Emulator entries,
compilations and printed counts are three different units; one impressive
combined figure is precisely the instrument defect #910 is about.

`scripts/oracle_wiring_check.py --min-emulation-floor 294914` enforces the
emulations total, in the **already-required** `Claim Check` job. It shares the
driver's header parser by import rather than re-implementing the grammar. Pinned
in `claims.yaml` (`SYNTH-ORACLE-CHECK-FLOORS-910`) so the number here, the
number in `ci.yml`, and the declared headers move together.

Per job, `scripts/oracle_evidence.py` closes out with what that job **measured**
— asserting every record met its floor *and* that the expected number of oracles
reported at all, so a step deleted, commented out, or skipped by an early exit
leaves the ledger short and reddens the job instead of quietly shrinking the
number.

## This is not the coverage percentage, and must never be added to it

`Rust-test Line Coverage` (was: `Code Coverage`) measures `cargo llvm-cov
--workspace` — the Rust test suite, in process. It **cannot see any of the
above**: the oracles spawn `$SYNTH` as a separate, uninstrumented process, from
other jobs entirely, and an uninstrumented subprocess emits no profile data.

That is why `synth-backend-*/src/backend.rs` reads ~42 % line coverage while
being exercised end-to-end by nearly every differential in this table. The
percentage **understates** the testing that exists and is **not** a completeness
measure. Two populations, two units, reported side by side — never one number.

## The oracles whose floor is weak, itemized

An honest short list beats a uniform claim:

| oracle | floor | why not stronger |
|---|---|---|
| `aarch64_matrix.sh` | `none` | a POSIX shell oracle; the driver runs Python in process and cannot instrument it. Its step already carries its own count assertion (>= 32 accepted ops), written before this mechanism existed |
| `i64_param_518_riscv_loudskip.py` | `compiles >= 1` | asserts a LOUD SKIP — by construction nothing executes, and it compiles the whole fixture once. Its eight `[ok ]` rows carry no printed total to bind to |
| `postlink_359_oracle.py` | `compiles >= 1` | a symbol-address/link-layout assertion over one compile; it prints addresses, not a check count |
| `fact_spec_*_494_differential.py` (5) | `compiles >= 2` | each runs twice — once executing thousands of vectors, once on a `--expect-decline` byte-identity leg that emulates nothing. The floor is the weaker leg's guarantee; the executing leg's real counts (2 002 / 2 052 / 3 167 / 288) still reach the ledger |
| `call_indirect_275_selfcontained_differential.py` | `compiles >= 4` | a decline/emission-shape oracle across four target configurations; no execution by design |
| `reachable_callgraph_275_selfcontained_differential.py` (RED step only) | not routed | that step inverts its verdict (`! python …`) because RED is the expected result. Routing it would file a below-floor record for a run that is *supposed* to fail. Its GREEN step is routed and carries `emulations >= 8` |

Everything else — 133 of 150 wired oracles — asserts a real emulator-entry
floor.

## Red-first mutation evidence — the check floors

Same discipline as the #890 matrix above: each leg runs the step **extracted
verbatim from `ci.yml`** (`yaml.safe_load` → the step's `run:` block → `bash -e`),
so there is no transcription drift between what was proved and what CI runs.

```
===== BASELINE: wiring gate + floor ratchet =====
STEP EXIT=0
  ci-checks compiles       9 scripts, floor total 43
  ci-checks emulations   133 scripts, floor total 294914
  ci-checks none           1 scripts, floor total 0
  ci-checks stdout         7 scripts, floor total 458
oracle-wiring gate is non-vacuous: ... 150 of them wired ... and every wired
oracle declares a check floor (294914 emulator entries asserted across 133 of them).

===== BASELINE: one oracle step through the driver =====
STEP EXIT=0
ORACLE-EVIDENCE script=base_cse_differential.py mode=emulations floor=2
measured=2 emulations=2 wasmtime_calls=1 compiles=4 exit=0

===== M1: harness returns BEFORE its comparison loop (still prints PASS, exits 0) =====
STEP EXIT=1
ORACLE: PASS
ORACLE-EVIDENCE script=base_cse_differential.py mode=emulations floor=2
measured=0 emulations=0 wasmtime_calls=0 compiles=0 exit=0
FAIL scripts/repro/base_cse_differential.py: VACUOUS — declared floor
emulations >= 2, measured 0. The oracle exited 0 having executed nothing; that
is a gate that cannot fail, not a passing gate.

===== M2: one floor lowered to 0 -> --min-emulation-floor ratchet =====
STEP EXIT=1
FAIL check-floor RATCHET BROKEN: summed `ci-checks: emulations` floors 294912 <
recorded minimum 294914. An oracle lost execution, or a floor was lowered.

===== M3: `# ci-checks:` header deleted -> wiring gate =====
STEP EXIT=1
  ci-checks UNDECLARED: 1
FAIL scripts/repro/base_cse_differential.py: no `# ci-checks:` header. Every
oracle must declare what it attests ...

===== M4: a happy-path STRING instead of a count (no capture group) =====
STEP EXIT=1
oracle_run: ... `ci-checks: stdout` regex must have EXACTLY ONE capture group
holding the count (got 0) — a pattern with no group asserts a happy-path
STRING, not that anything ran.

===== M5: a routed oracle step demoted to a COMMENT -> wiring gate =====
STEP EXIT=1
FAIL scripts/repro/bulk_memory_374_differential.py: declares `wired` but NO
workflow STEP runs it — the gate is INERT. It IS mentioned in ci.yml, but only
in a COMMENT — prose does not run an oracle.

===== M6: oracle steps un-routed (exit-status-only again) -> claims ledger =====
STEP EXIT=1
track shrank below floor: 157 < recorded min 159
[/oracle_run\.py scripts/repro//] — update the claim, not just the number

===== M7: job ledger short (1 of 15 oracles reported, --min-oracles 15) =====
STEP EXIT=1
ORACLE-LEDGER job=... oracles=1 runs=1 emulations=16 ... below_floor=0
FAIL ledger SHORT: 1 distinct oracles reported, expected >= 15. A step is
missing, commented out, or the job exited early — its gate is inert (#890).

===== RESTORED =====
STEP EXIT=0
```

**M1 is the load-bearing one.** The mutated harness still prints its `ORACLE:
PASS` banner and still exits 0 — a `grep -q '^ORACLE: PASS'` assertion would
have greened it, and so would every one of the 152 exit-status-only steps this
mechanism replaces. Only the emulator count catches it, because that count does
not come from the harness.

**M5 re-proves the v0.54 fix under this lane's edits.** YAML eats `#` only in a
single-line plain scalar; in a `run: |` block the `#` survives into the script
body, so commenting a step out used to leave the script "referenced" and the
gate GREEN. 159 step bodies were rewritten here, which is exactly the surface
that fix covers, so it is re-run rather than assumed.

**M6 nuance, stated rather than rounded off:** the mutation substituted both the
`python3` and the `python` spelling, so it un-routed two step lines, not one
(159 → 157). The direction is what the leg proves — un-routing reddens.

**M7** is the runtime counterpart of M5: even if the static gate were bypassed,
a job whose oracle steps stopped running files a short ledger and goes red.

## Adding a repro script

1. Write the harness. Give it **exit-code discipline** — `sys.exit(0 if ok else 1)`.
   A harness that prints `MISMATCH` and exits 0 is a gate that cannot fail
   (`sret_decide_differential.py` was exactly that until #890).
2. Read the binary under test from `$SYNTH` (`os.environ.get("SYNTH", ...)`), so
   CI can point it at its own build.
3. Add a CI step and declare `# ci-status: wired`; or declare `manual (<category>)`
   / `unwired` with a real reason and bump `SYNTH-ORACLE-WIRING-890` in
   `claims.yaml`.
4. If `wired`: run it through the driver (`python scripts/oracle_run.py
   scripts/repro/<it>.py …`), declare a `# ci-checks:` floor, and bump the job's
   `--min-oracles`. Measure the floor — run it once with
   `scripts/oracle_run.py --report-only` and use what comes back.
