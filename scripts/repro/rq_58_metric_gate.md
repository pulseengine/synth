# RQ-58-METRIC — red-first evidence transcript (epic #242)

Frozen record of the demonstration required by the RQ-58-METRIC artifact:
*"adding a hand-written lowering arm without deleting one must turn the gate
red. Demonstrate it by adding one, watching it red, and reverting — do not
assert it."*

Same shape as `scripts/repro/vcr_ver_001_gate.md`. No script to wire: the gate
is `python3 scripts/claim_check.py claims.yaml --metric`, already a required CI
step in the `Claim Check` job.

Environment: worktree at `feat/subtraction-metric-242`, v0.57.0 + the v0.58 plan
merge, `CARGO_TARGET_DIR=$HOME/.cache/synth-v58-l1`, 2026-08-18.

---

## 0. Baseline — green, and the metric printed

```
$ python3 scripts/claim_check.py claims.yaml --metric

=== subtraction metric (epic #242) — 7 directed pins ===
metric                            now  baseline   delta  direction   waivers
selector_lines_code             18480     18480      +0  must FALL   0
selector_lines_total            29616         —       —  tracked     0
selector_wildcard_arms_code        62        62      +0  must FALL   0
selector_wildcard_arms_total      105         —       —  tracked     0
sel_dsl_rules                      50        50      +0  must RISE   0
mirror_marker_files                57        57      +0  must FALL   0
mirror_obligation_files            23        23      +0  must FALL   0

47/47 claims hold.                                                  (rc=0)
```

The two whole-file counts are `track`, not `down`, and the distinction is a
design decision worth stating: they include the file's TEST MODULE, so a PR that
only adds test coverage moves them. Making that demand a WAIVER would file
"added 40 lines of tests" next to "grew the patch pile" in the same list, and a
waiver channel full of noise is one nobody reads. `track` still forbids slack —
the ledger must carry the live number — it just declines to assert a direction
for a mixed population. Nothing is lost: total minus code IS the test module,
and code is pinned `down`.

Reference artefact, `flight_seam.wasm` compiled for `thumbv7em-none-eabi`:

```
a866e44beef45679f0a2d3fbc23f94949b47a9b91eb64c6b83c10058b3531e76  base.elf
```

## 1. RED — one hand-written lowering arm added, nothing deleted

Applied to `crates/synth-synthesis/src/instruction_selector.rs`, inside the
`I32Add` arm of `select_default` — a realistic strength-reduction special case
of exactly the kind epic #242 exists to stop accumulating:

```rust
I32Add => {
    // RED-FIRST PROBE (RQ-58-METRIC) — a hand-written lowering
    // special case added WITHOUT deleting one. Reverted below.
    if rn == rm {
        return Ok(vec![ArmOp::Lsl { rd, rn, shift: 1 }]);
    }
    ...unchanged hand-written body and DSL delegation...
}
```

Five lines: two of comment, three of lowering decision. Both count — the metric
measures the hand-maintained surface, and a comment explaining a special case is
part of what has to be kept true.

```
$ python3 scripts/claim_check.py claims.yaml --metric                  (rc=1)

selector_lines_code             18485     18480      +5  must FALL   0
selector_lines_total            29621         —       —  tracked     0

FAIL SYNTH-SUBTRACTION-SELECTOR
    ratchet 'selector_lines_code' MOVED the WRONG way: derived 18485 !=
    ledger value 18480 (baseline 18480, ceiling that must FALL) — update
    claims.yaml in the SAME PR; if it moved the wrong way add a waivers:
    entry saying why [...]
    tracked number 'selector_lines_total' MOVED: derived 29621 != ledger
    value 29616 — update claims.yaml in the SAME PR. NO waiver needed: this
    pin asserts no direction (the directed one is the region-scoped pin) — ...

47 claims checked; 2 failure(s) incl. surface gates.
```

(The second failure is `artifacts/status.json` staleness — correct: the
derived numbers artifact must be regenerated too.)

## 1b. RED — the WILDCARD pin, fired on the real file

The lines pin and the wildcard pin are different derivations, and a passing
number proves nothing about the second. This probe moves only the wildcard
count. A `_ =>` arm added inside the code region:

```rust
I32Add => {
    match rd {
        _ => {}
    }
    ...unchanged...
}
```

```
$ python3 scripts/claim_check.py claims.yaml --metric                  (rc=1)

selector_wildcard_arms_code        63        62      +1  must FALL   0
selector_wildcard_arms_total      106         —       —  tracked     0

FAIL SYNTH-SUBTRACTION-SELECTOR
    ratchet 'selector_wildcard_arms_code' MOVED the WRONG way: derived 63 !=
    ledger value 62 (baseline 62, ceiling that must FALL) — ...
    tracked number 'selector_wildcard_arms_total' MOVED: derived 106 != ledger
    value 105 — update claims.yaml in the SAME PR. NO waiver needed: this pin
    asserts no direction (the directed one is the region-scoped pin) — ...
```

62 -> 63 on the region-scoped pin, 105 -> 106 tracked, with the two failure
messages correctly distinguished by direction. This is the pin RQ-58-WILDCARD
will drive, so it is demonstrated firing on the REAL selector rather than only
against a synthetic fixture in the unit tests.

This probe also FOUND A DEFECT in the gate, in the honest place — its own
output. `--metric` was printing `baseline None / delta ? / must RISE` for the
`track` pins, i.e. asserting a direction they do not have. Fixed to print
`— / — / tracked` before the pin count was frozen.

## 2. What NO existing oracle noticed — the reason this gate exists

With the probe still applied:

```
$ shasum -a 256 base.elf probe.elf
a866e44beef45679f0a2d3fbc23f94949b47a9b91eb64c6b83c10058b3531e76  base.elf
a866e44beef45679f0a2d3fbc23f94949b47a9b91eb64c6b83c10058b3531e76  probe.elf   <- IDENTICAL

$ cargo test -p synth-cli --test frozen_codegen_bytes
test result: ok. 10 passed; 0 failed; ...                              (rc=0)
```

The patch pile grew by a hand-written lowering decision and **the emitted bytes
did not move**. Byte-identity and frozen-anchor oracles are structurally blind
to this — they answer "did behaviour change", and the North Star's question is
"did the hand-written surface grow". That gap is what went unmeasured for
fifteen releases.

## 3. The escape hatch — a growth that is justified, not blocked

This is not a code-golf gate. With the probe still applied, adding the
documented waiver to the DIRECTED pin (the tracked one needs only its number
updated — no waiver, by design):

Re-run after the `track` change with a 3-line variant of the same probe, so the
numbers below are what the tree actually produced:

```yaml
- kind: ratchet
  name: selector_lines_code
  direction: down
  value: 18483          # ledger carries the LIVE number — no slack expressible
  baseline: 18480       # best ever; the waiver is measured against THIS
  waivers:
    - to: 18483         # bound to the value, so a 2nd growth needs a 2nd waiver
      reason: "ESCAPE-HATCH DEMO ONLY — reverted in this same PR."

- kind: ratchet
  name: selector_lines_total
  direction: track
  value: 29619          # tracked: number updated, NO waiver — by design
```

```
$ python3 scripts/claim_check.py claims.yaml --metric                  (rc=1)
selector_lines_code             18483     18480      +3  must FALL   1
selector_lines_total            29619         —       —  tracked     0
ok   SYNTH-SUBTRACTION-SELECTOR

47 claims checked; 1 failure(s) incl. surface gates.
```

The subtraction claim is GREEN — the growth was justified and accepted. The one
remaining failure is `artifacts/status.json` staleness, which is correct and
unrelated: the derived numbers artifact must be regenerated in the same PR too.

Two intermediate states observed while producing this, both worth keeping:

* A waiver whose `to:` did not equal the live value (18,489 against a derived
  18,485) did **not** silence the pin. Permission is bound to a number, never
  granted in general.
* Setting the tracked pin's value required NO waiver — one line, no ceremony.
  That is the asymmetry the `track` direction exists to create.

## 4. GREEN again after revert, byte-identical

```
$ git checkout -- crates/synth-synthesis/src/instruction_selector.rs claims.yaml
$ python3 scripts/claim_check.py claims.yaml --metric                  (rc=0)
selector_lines_code             18480     18480      +0  must FALL   0
47/47 claims hold.

$ shasum -a 256 base.elf after.elf
a866e44beef45679f0a2d3fbc23f94949b47a9b91eb64c6b83c10058b3531e76  base.elf
a866e44beef45679f0a2d3fbc23f94949b47a9b91eb64c6b83c10058b3531e76  after.elf
```

## 5. The gate's own gate

The metric adds a checker to a release whose thesis is that this repo's checkers
are where the defects are. Its predicate is unit-tested rather than trusted:

```
$ python3 scripts/test_claim_check.py
Ran 38 tests ... OK                                                    (rc=0)
```

Mutation-verified at authoring — stubbing `check_ratchet` to return no failures
kills 18 of the 38 (5 failures + 13 errors); a separate mutant of the
`track` branch kills 3 more. Anti-vacuity beyond the tests:
`--metric` fails outright on an EMPTY pin population, and
`SYNTH-SUBTRACTION-PINS-DECLARED` pins the population at 7 plus both CI step
commands, so deleting a single ceiling — or unwiring the step — is red rather
than a cheap way to go green.
