# RQ-57-MCDC (#912) — MC/DC structural coverage: surface, measurement, potency

Reproduce: `bash scripts/mcdc_run.sh target/mcdc && python3 scripts/mcdc_gate.py target/mcdc`
(needs `witness` v0.42.0 on `$PATH` or `WITNESS=…`, and the `wasm32-wasip1`
target). CI job: `mcdc-structural-coverage`.

## 1. The surface question, answered with evidence

#912 sat N/A for six releases on the argument that `witness` measures MC/DC on
a **Wasm** artifact while synth emits **ARM/RV32/A64 machine code**. That
argument is right about synth's *output* and irrelevant to the question: the
decisions that ship a miscompile are the ones in synth's own Rust, and those
compile to Wasm fine.

Three candidate surfaces were tried. Two were rejected on evidence, not taste.

### REJECTED — native LLVM MC/DC via `-Zcoverage-options=mcdc`

Not a preference: **the capability was removed from rustc.**
[rust-lang/rust#144999](https://github.com/rust-lang/rust/pull/144999) —
*"coverage: Remove all unstable support for MC/DC instrumentation"*, merged
2025-08-08, released in Rust 1.91 — on the stated rationale that the partial
implementation "has proven itself to be a major burden on overall maintenance
of coverage instrumentation."

Probed directly rather than taken on faith, across three nightlies
(1.93.0-nightly 2025-11-20, 1.95.0-nightly 2026-02-06, 1.97.0-nightly
2026-04-19):

```
[mcdc]      rc=1  error: incorrect value `mcdc` for unstable option
                  `coverage-options` - `block` | `branch` | `condition` was expected
[condition] rc=0
```

`condition` is the trap in this family: it compiles, and it is **not** MC/DC.
A toy `a && b || c` built with it yields per-condition *branch* entries, a
`report --show-mcdc-summary` reading `MC/DC Conditions 0`, `mcdc_records: 0`
in the JSON export, and **zero `llvm.instrprof.mcdc.*` intrinsics** in the
emitted IR. `cargo-llvm-cov` 0.6.21 and 0.8.7 both still pass `mcdc` and both
fail the build.

### REJECTED — `witness` over the Wasm fixtures synth COMPILES

This measures the fixture, not synth. The discriminating test is *whose source
do the gap rows name*. gale's run on a real dissolved isolation core (recorded
on #912) named:

| function | branches | reached |
|---|---|---|
| `core::fmt::Formatter::pad_integral` | 25 | 0 |
| `core::str::count::do_count_chars` | 20 | 0 |
| `<u64 as Display>::fmt` | 5 | 0 |
| `pad_integral::write_prefix` | 3 | 0 |
| `wit_bindgen::rt::cabi_realloc` ×2 | 3+3 | 0 |

Five stdlib/bindgen frames and **zero synth functions**. A surface whose gap
rows cannot name a synth decision cannot notice a missing condition in one.

### CHOSEN — `witness` over a `wasm32-wasip1` build of synth's OWN crates

`crates/synth-mcdc-harness` is a thin **row driver**: it links the real crates
and calls the real `pub fn`s with inputs arriving through Wasm parameters (so
nothing is constant-folded). It re-implements no predicate — a mirror would be
precisely the vacuous-gate class this is meant to catch. Gap rows then name
`synth_core::static_data_addr::resolve_owner`,
`synth_backend_riscv::alloc_validator::is_ret`, and so on.

Bonus, and the reason this surface is arguably *better* than the removed rustc
one: witness reconstructs decisions from the **lowered** `br_if` chains, so a
Rust `matches!` lowers to a real multi-condition decision. `is_ret`'s
`matches!(op, Jalr { rd: ZERO, rs1: RA, imm: 0 })` scores as a 4-condition
decision — source-level MC/DC would have seen nothing there.

## 2. "The right parts" — what is scored, and what is not

Scored (`SCORED_PREFIXES` in `scripts/mcdc_gate.py`) — the predicate classes
where a missed condition **has already shipped a soundness bug in this repo**:

| module | class | the bug |
|---|---|---|
| `synth_core::static_data_addr` | validator accept/reject | VCR-VER-003 #777; exists to hard-error the #757 wrong-segment miscompile; also the #798 served-image gate |
| `synth_backend_riscv::alloc_validator` | validator accept/reject | VCR-RA-003 #815; **#871** shipped an unsaved-`ra` miscompile and the fix *was* a condition added to the save-set predicate |
| `synth_backend_riscv::backend` | guard emission | #953/#959, three consecutive releases: `mem_size == 0` was EXEMPT from the power-of-two mask gate, so `(memory 0)` emitted an identity mask (`0-1 = 0xFFFF_FFFF`) and every access ran unmasked |

Excluded, named rather than hidden:

* `synth_synthesis::instruction_selector` — 225 boolean-operator lines. A lane
  of its own; already gated by ~30 execution differentials.
* the aarch64 `bounds_check` / `form_ea` closures (#865) — reachable only by
  driving a whole function body through the selector. **Named residual**: the
  guard-emission class is covered on RV32, not yet on aarch64.
* `synth_backend::wcet*` decline predicates — `scan_for_decline` has **1**
  boolean-operator line in 1061; it is match-dispatch, so most of that surface
  has no compound decision for MC/DC to speak about. Branch coverage is the
  applicable criterion there.

## 3. Measured baseline — and the platform is part of the measurement

witness 0.42.0, `wasm32-wasip1`, rustc **1.96.1**, the same 56 rows, two hosts:

| host | dec | full | cond | proved | gap | dead |
|---|---|---|---|---|---|---|
| **ubuntu-latest x86_64** (the CI platform — the floors) | **22** | **4** | **130** | **57** | 23 | 50 |
| macOS aarch64 (development) | 20 | 3 | 144 | 63 | 31 | 50 |

Same toolchain VERSION, same witness, same rows, different HOST. These are
counts of decisions reconstructed from *lowered Wasm*, so how `std` inlines
moves them: `validate_final_allocation_rv32` presents as **9 decisions / 44
conditions** on Linux and **4 / 43** on macOS, and `ensure_supported_target`
disappears entirely on Linux. Only `dead` is identical (50) — as you would
expect of "never reached".

That was not predicted; it was measured, by the first CI run, after the local
baseline had already been written down. Both numbers are recorded here and in
`scripts/mcdc_gate.py` so the delta is a stated fact: **a developer running
this locally on macOS will not meet the CI floors, and that is a platform
delta, not a regression.** Use `--report-only` locally and read the delta
against your own previous run. The absolute floors belong to the platform the
gate actually blocks on.

Witness-version invariance was checked separately — 0.28.0 and 0.42.0 give
identical numbers on the same host — so the tool is not what moves these.

### The CI table (the one the floors come from)

```
function                                                        dec  full  cond  prov  gap  dead
synth_backend_riscv::alloc_validator::is_ret                      1     1     4     4    0     0
synth_backend_riscv::alloc_validator::is_straight_line            1     0    52   12    0    40
synth_backend_riscv::alloc_validator::sp_slot_load                1     1     2     2    0     0
…alloc_validator::validate_final_allocation_rv32                  9     1    44   29   15     0
synth_backend_riscv::backend::build_options                       2     1     7     5    0     2
synth_backend_riscv::backend::compile_function_with_opts          1     0     4     1    0     3
synth_backend_riscv::backend::count_params                        1     0     4     1    0     3
…backend::count_params::{{closure}}                               1     0     2     0    0     2
synth_core::static_data_addr::resolve_owner                       1     0     2     0    2     0
synth_core::static_data_addr::runtime_image                       1     0     2     1    1     0
synth_core::static_data_addr::validate_reloc_resolutions          1     0     2     0    2     0
…static_data_addr::validate_reloc_resolutions_spanned             2     0     5     2    3     0
TOTAL                                                            22     4  130   57   23    50
```

### The macOS/aarch64 table (development; where the potency deltas were taken)

```
function                                                        dec  full  cond  prov  gap  dead
synth_backend_riscv::alloc_validator::is_ret                      1     1     4     4    0     0
synth_backend_riscv::alloc_validator::is_straight_line            1     0    52   12    0    40
synth_backend_riscv::alloc_validator::sp_slot_load                1     1     2     2    0     0
…alloc_validator::validate_final_allocation_rv32                  4     0    43   28   15     0
synth_backend_riscv::backend::build_options                       2     1     7     5    0     2
synth_backend_riscv::backend::compile_function_with_opts          1     0     4     1    0     3
synth_backend_riscv::backend::count_params                        1     0     4     1    0     3
…backend::count_params::{{closure}}                               1     0     2     0    0     2
synth_backend_riscv::backend::ensure_supported_target             1     0     4     0    4     0
synth_core::static_data_addr::resolve_owner                       1     0     2     0    2     0
synth_core::static_data_addr::runtime_image                       1     0     2     1    1     0
synth_core::static_data_addr::validate_reloc_resolutions          3     0     7     4    3     0
…static_data_addr::validate_reloc_resolutions_spanned             2     0    11     5    6     0
TOTAL                                                            20     3   144   63   31    50
```

**The gate reads gap rows, not a percentage.** The gap conditions are
printed in full by `scripts/mcdc_gate.py`, each with the vector witness says
would close it. Two examples of the residual, stated so it is named:

* `validate_final_allocation_rv32` carries decisions of 10 and 20 conditions
  (whole-function `br_if` chains after inlining). Closing those needs ≥21
  co-designed vectors and is **not** claimed.
* `ensure_supported_target`'s ISA conjunction (4 gap on macOS; the function
  does not survive inlining on Linux at all) cannot be flipped through public
  constructors: there is no `TargetSpec` with family RiscV and a non-RiscV32/64
  ISA.

`is_ret` went 1-proved/3-gap → **4-proved/0-gap** by adding exactly the three
vectors witness printed, which is the practical demonstration that the gap rows
are actionable rather than decorative.

## 4. Why the gate scores by FUNCTION and floors COUNTS

Three defects in the naive reading, each the "instrument measuring the wrong
surface" class:

1. **The module-wide percentage is meaningless here.** A wasip1 link drags in
   wasi-libc (`malloc.c`, `stpcpy.c`) and Rust `std`. Raw figure: `3/770 full
   MC/DC`, 3879 dead conditions. Says nothing about synth.
2. **witness's `source_file` / `source_line` cannot be used for scoping.** They
   are DWARF attributions of *inlined* code — `resolve_owner`'s decision reports
   as `static_data_addr.rs:355` (it is at :274), and
   `validate_reloc_resolutions`' decisions report as `backend.rs:480` and
   `num.rs:85`, files in other crates. `source_file` is also only a *basename*,
   so six crates' `backend.rs` collide. (Upstream: witness#179.) The manifest's
   per-branch **`function_name` is reliable**, so the gate scopes on the
   demangled symbol and prints the reported line as advisory only.
3. **A ratio cannot notice a deleted condition** — removing one removes its gap
   row and the percentage *improves*. So the floors are counts.

Declared floors = the **CI platform's** measured baseline, no slack:
`decisions ≥ 22`, `conditions ≥ 130`, `proved ≥ 57`, `fully-proved decisions ≥ 4`,
and `dead ≤ 50`.

**Dead is ceilinged, not ignored.** 50 scored conditions are never
evaluated — 40 of them in `is_straight_line`, whose match arms cover RV32
opcodes the row set does not construct. That is an honest residual, but an
UNFLOORED residual is how a number rots: a change that stopped reaching the
segment barriers would raise `dead`, lower nothing else, and pass. It is also a
third potency surface — mutation (a) moves dead 50 → 52.

## 5. Red-first potency — measured on both platforms, and one surprise

### On macOS/aarch64 (local; baseline 20 / 3 / 144 / 63 / 31 / 50)

Both mutations restored afterwards; `git diff` byte-identical.

**(a) Delete a condition** — remove the #871 fix `|| rs2 == Reg::RA` from the
RV32 allocation validator's save-set predicate:

```
mutated    TOTAL   dec 19  full 2  cond 142  proved 54  gap 36  dead 52
FAIL: scored decisions 19 < floor 20
FAIL: scored conditions 142 < floor 144
FAIL: proved conditions 54 < floor 63
FAIL: fully-proved decisions 2 < floor 3
FAIL: dead conditions 52 > ceiling 50
```

The **condition-count** drop is the signal a ratio-only floor cannot produce:
delete a condition and the *percentage improves*.

**(b) Weaken the vector set** — drop ONE truth-table row (`ra_validate:14`, the
non-`sp` `Lw` that gives `sp_slot_load` its unique-cause pair):

```
mutated    TOTAL   dec 20  full 2  cond 144  proved 62  gap 32  dead 50
FAIL: proved conditions 62 < floor 63
FAIL: fully-proved decisions 2 < floor 3
```

Conditions unchanged, coverage lost — a different failure path.

### On the CI platform, where the gate actually blocks

Both mutations were then pushed to the PR branch and run on CI, because a
potency result taken on one host does not obviously transfer to a host where
the same function presents as 9 decisions instead of 4. "It obviously still
works" is the reasoning this lane exists to distrust.

**Mutation (a) went red at the WRONG STEP, and that is worth recording.** The
job's own row-driver sanity gate (step 7) asserts `ra_validate(4) == 1` —
"#871: unsaved `ra` must be a violation" — so deleting the condition fails
*there* and the MC/DC measurement never runs. The commit is red, and the
`VCR-RA-003 RV32` job goes red independently, so the change cannot land. But
two other gates catching one mutation proves nothing about whether the **MC/DC
floors** bite.

**Mutation (b) isolates them,** because dropping a truth-table row changes no
compiler behaviour: the sanity gate passes, the witness run executes, and the
failure has to come from the scoring step or not at all. Measured, run
`31821746035`:

```
step 7  Row-driver sanity gate (host)                     success
step 8  Run the MC/DC rows under witness                  success
step 9  Score synth's own decisions against the floors    FAILURE

TOTAL                              22     3   130    56   24    50
FAIL: proved conditions 56 < floor 57
FAIL: fully-proved decisions 3 < floor 4
```

Against the CI baseline `22 / 4 / 130 / 57 / 23 / 50`: decisions unchanged,
**conditions unchanged at 130** — nothing was deleted — while `proved` fell
57 → 56 and one decision dropped out of full MC/DC. Exactly the predicted
signature of *coverage lost, structure intact*, produced by the MC/DC scoring
step itself, on the platform the gate blocks on.

Restored immediately afterwards (`scripts/mcdc_run.sh` byte-identical to the
pre-probe tree), and the source mutation from probe 1 likewise.

The lesson generalises past this lane: **a red gate is not evidence that the
gate you were testing works.** Read which step failed.

## 6. Two invocation traps, encoded in the scripts

Both are why this looked empty for six releases (upstream witness#177/#178):

1. `witness report` **without** `--format mcdc` prints branches *reached*, not
   MC/DC. `scripts/mcdc_run.sh` always requests `mcdc` / `mcdc-json`.
2. A build without full DWARF renders every gap row `(anon)` while still
   reporting `attribution_source: "dwarf"`. The script always builds with
   `-C debuginfo=2` and the dev profile (a `--release` build at `opt-level=z/s`
   dead-strips witness's counters).
