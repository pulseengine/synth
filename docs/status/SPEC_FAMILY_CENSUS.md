# Spec-suite census by WASM feature family — v0.65

**Measured 2026-09-09** on synth at the RQ-65-MVPCORE tree (main `580d53f9` +
#1225), over all **257 top-level `.wast` files** of the pinned spec test suite
(`tests/spec-testsuite`, submodule `345367358`).

Derived by grouping the existing `scripts/spec_compile_census.py` census by
feature family — **the census's own `classify()` and `family_of()` are
reused**, not reimplemented, so there is no second source of truth to drift.
The per-family `ok` counts are pinned in that script (`FAMILY_OK_PINS`), so a
count that moves reddens the census itself; this document is transcribed from
the census's per-family output and its row is pinned by `claims.yaml`
(`SYNTH-SPEC-FAMILY-MVP-CORE`).

## Why this document exists

The census publishes ONE derived figure per backend — `at-least-one-export`,
currently **47 / 43 / 47**. That number is correct and CI-gated, and it is the
wrong number to plan from, because it averages two populations that should
never be averaged: families synth **targets**, and families synth has **never
implemented**.

## The split — files fully `ok` / `partial`

| family | files | arm | riscv | aarch64 |
|--------|-------|-----|-------|---------|
| **MVP core** | 80 | **12** / 21 | **9** / 23 | **18** / 20 |
| SIMD | 59 | 0 / 0 | 0 / 0 | 0 / 0 |
| multi-memory | 39 | 1 / 3 | 0 / 3 | 1 / 1 |
| reference types | 23 | 0 / 3 | 0 / 3 | 0 / 0 |
| GC | 16 | 0 / 2 | 0 / 2 | 0 / 0 |
| memory64 | 14 | 2 / 1 | 0 / 1 | 2 / 3 |
| bulk memory | 11 | 1 / 1 | 0 / 2 | 0 / 2 |
| relaxed SIMD | 7 | 0 / 0 | 0 / 0 | 0 / 0 |
| exception handling | 4 | 0 / 0 | 0 / 0 | 0 / 0 |
| tail call | 3 | 0 / 0 | 0 / 0 | 0 / 0 |
| multi-value | 1 | 0 / 0 | 0 / 0 | 0 / 0 |

## What changed since v0.63, and why the MVP-core row went DOWN

v0.63 published **MVP core 14 / 114 arm, 11 riscv, 21 aarch64**. Both numbers
in that fraction were wrong, in ways that only became visible when
RQ-65-MVPCORE re-derived the row and ranked its blockers.

### 1. The denominator: 34 files were not MVP core

The census's family regexes were written against the suite's proposal-era
filenames. Two families had merged into the core suite at the pinned commit
(`4b24564`, 2025-09-22) under names the regexes did not match:

- **multi-memory** (Wasm 3.0, standardized 2025-09-17) arrived as
  digit-suffixed twins of core files — `address0.wast` beside `address.wast`,
  `load0..2`, `memory_size0..3`, `data0/1`, `linking0..3`, `imports0..4`,
  `start0`, `store0..2`, `traps0`, ... — plus `memory-multi.wast` and
  `data_drop0.wast`. Content-verified: every one declares 2..21 memories per
  module. The old `^multi.?memory|^memory_multi` pattern matched none of them
  (nor `memory-multi` — hyphen vs underscore), and `^data\b` cannot match
  `data0` (no word boundary between `a` and `0`). **31 of them sat in MVP
  core.** The family's top arm blocker in v0.63's ranking — "multi-memory: an
  op on memory N cannot be lowered into a self-contained image", 17 files as
  the SOLE blocker — was a multi-memory decline mis-filed as a scalar-core one.
- **relaxed SIMD** lane files — `i8x16_relaxed_swizzle`,
  `i16x8_relaxed_q15mulr_s`, `i32x4_relaxed_trunc` — are git-recorded renames
  from `proposals/relaxed-simd/` in the same commit and start with a lane
  type, not `relaxed_`. 3 more.

MVP core is **80** files. The two families are now matched before the
features they twin (`data0` is a multi-memory data test, `linking0` a
multi-memory linking test), so a decline there is attributed to the
capability actually missing.

### 2. The numerator: the census measured a path no oracle executes (#1225)

`synth compile file.wast` took a driver branch — the multi-module MERGE,
written for synth's own i32-only fixture suite — that handed the backends
**empty data segments, empty globals and initializers, i32-only signature
tables and a default aarch64 substrate**. Measured on the same one-module
input compiled as `probe.wast` and `probe.wat`: the `.wast` image carried no
data bytes and a `Reset_Handler` that never wrote R9, while `get_g` in both
was `ldr.w r4, [r9]`; `tests/wast/i64_arithmetic.wast`'s `i64.add` on two i64
parameters was lowered as `adds r3, r0, r1` — param 0's low half plus its own
high half. Exit 0 every time, counted `ok`.

The execution oracle over the suite (`selector_parity_197_differential.py`)
writes every `(module ...)` to a `.wat` and compiles THAT — the other path. So
v0.63's `14 / 114` was a property of objects nothing executes (the shape
issue #1217 asks to sweep for).

Since v0.65 a **single-module `.wast` compiles on the single-module path** —
gated byte-for-byte against its module compiled alone by
`scripts/repro/wast_single_module_path_identity_1225.py` in the `Spec Suite`
workflow (red on the pre-fix driver: arm 49 / riscv 33 / aarch64 56
mismatches of 140 compared; 140 / 140 / 140 identical after) — and the
**multi-module merge refuses** a module carrying active data segments,
accessed globals or an i64/f32/f64 parameter or result, naming the count.

### 3. The per-file movement, measured (old 114-file set, per backend)

| backend | before (v0.63 path) | after | lost `ok` | gained `ok` |
|---------|--------------------|-------|-----------|-------------|
| arm | 14 ok / 39 partial | 12 ok / 22 partial | `imports2` (multi-memory twin), `int_exprs` (i64 signatures), `stack` (accessed globals), `binary-leb128` (data) — refused instead of shipped wrong | `nop`, `load` (the merge's default `call_indirect` guards had declined every dispatch) |
| riscv | 11 / 38 | 9 / 23 | `imports2`, `binary-leb128` | — |
| aarch64 | 21 / 17 | 18 / 20 | `imports0/2/3` (multi-memory twins the merge had never handed a second memory), `address`, `memory`, `float_memory` (data — aarch64 REFUSES data-carrying modules on the real path, v0.53), `const` (402 f32/f64-result modules), `float_literals`, `int_exprs` | `f32`, `f32_bitwise`, `f32_cmp`, `f64_bitwise`, `f64_cmp`, `float_misc`, `conversions` — the backend's complete scalar float core, reachable for the first time; and 12 core files (`block`, `br`, `br_if`, `br_table`, `call`, `if`, `load`, `local_tee`, `loop`, `nop`, `return`, `left-to-right`) from whole-file refusal to `partial` |

On the corrected 80-file set the row is **arm 13 → 12, riscv 10 → 9,
aarch64 18 → 18**. Every loss is a refusal of an object that was wrong; every
gain is a compile of an object the merge had mis-typed.

### 4. The reach increment landed alongside moved ZERO files

The start-function invocation (#1046 follow-on: the self-contained Cortex-M
`Reset_Handler` BLs the `(start ...)` function after the data copy and the R9
table, before the entry call) was a SOLE blocker on all three backends — 4
files each. It moves **no file** in this table: `start.wast`,
`annotations.wast` and `binary.wast` are multi-module (the merge cannot run
five independent instantiations' start functions) and `start0.wast` is a
multi-memory twin. The gain is module-level and lives in the parity oracle's
own line — `start-function modules: 4 seen, 2 both-accepted and booted ...
10 assertion(s) ok` — which was `0 both-accepted` on the compiler before it.
That is the file-vs-module gap v0.63's caution predicted, measured rather than
assumed.

## The two facts the aggregate hides

### 1. MVP core is 12 of 80 fully-`ok` on arm

The scalar foundation every other family rests on is **15 %** complete by
this measure (9 riscv, 18 aarch64) — and this is the first release in which
that number is measured on objects nothing was silently dropped from. It is
the single most decision-relevant number in the project.

It is why **`VCR-SIMD-001` is gated on the scalar core, not on appetite**:
building a vector story on a 15 %-complete foundation widens the base faster
than it is closed.

### 2. 89 files — 35 % of the suite — are families with ZERO support anywhere

SIMD 59, GC 16, relaxed SIMD 7, exception handling 4, tail call 3.

Those files depress the aggregate while representing work that was **never
scoped**. A reader cannot tell `47/257` apart from a compiler that tries
everything and half-fails. The truth is a compiler that does one family
deliberately and declines the rest — which is the loud-decline stance the
compliance envelope already claims as a differentiator, and it should be
legible from the number.

**Declining a family synth does not target is not a failure.** It is the
boundary, and stating it as a boundary is more honest than letting it sit
inside an average.

## What blocks MVP core now — ranked, with the reason each was closed or declined

Ranked by the number of files where the cause is the SOLE recorded blocker
(the upper bound on files that could flip to `ok` if only that cause were
cleared — still an upper bound, because the census records only the FIRST
decline per function). Measured on the v0.65 path over the 80 MVP-core files;
the v0.63-path figure is given where the two differ, because the merge
refusal now sits IN FRONT of the lowering gaps it used to let through.

| blocker | sole (arm / riscv / aarch64) | decision |
|---------|------------------------------|----------|
| #1225 multi-module merge refusal: non-i32 signatures 9, accessed globals 7, active data 6 | 22 / 22 / 22 | **the next lever, declined here**: these 22 files are multi-module and the merge cannot represent them; compiling each `(module ...)` separately (a file is `ok` when every module is) is the honest successor to the merge — it is what the parity oracle already does — and it is a census-shape change, not a lowering change, so it is not this lane's reach increment |
| GI-FPU-002 scalar f32 / f64 on the census's fixed `--cortex-m` target (thumbv7m, no FPU) | 6 + 2 / – / – | **declined, measured**: a property of the census invocation, not a lowering gap — on `--target cortex-m7dp` (the STM32H743 profile) the same 80 files measure **17 ok / 22 partial** against 12 / 21 here; changing the invocation would move every pin to flatter one target |
| start function (#1046) | 3 / 3 / 3 (4 on the v0.63 set: `start0` was a multi-memory twin) | **closed, oracle first** (ARM self-contained): parity floor red on the pre-invocation compiler, green after; 0 files gained at file level (`start`, `annotations`, `binary` are multi-module), 2 modules and 10 assertions gained at module level. riscv and aarch64 emit no startup at all (ET_REL only), so they keep the refusal — measured decline |
| aarch64 `br_table` with value-carrying targets | – / – / 2 (13 files, 90 functions) | **declined for this lane**: a real aarch64 lowering gap, visible now that the #851 globals refusal no longer hides it |
| "stack underflow: malformed WASM or compiler bug" on VALID modules (`br`, `br_table`, `call`, `loop`, `return`, `unreachable`) | 0 (6 files, 74 functions; riscv's "invalid program — stack underflow" sibling 3 files) | **declined for this lane, filed as #1229**: the polymorphic stack after `unreachable`/`br`/`return`; 0 sole means clearing it alone flips no file — the exact v0.63 trap |
| `VCR-RA-003: JoinValueNotAvailable { reg: R4 }` (`br`, `br_if`, `br_table`, `labels`; an R5 instance in one more) | 1 / – / – | **filed as #1230**: the allocator validator refusing its own emitted stream — a caught would-be miscompile, not a lowering gap |
| aarch64 `expected GP operand, got FP` / `expected FP operand, got GP` (`local_set`, `align`, `float_exprs`, `endianness`, ...) | – / – / 1 (3 files after; 15 files, ~300 functions on the v0.63 set before the merge refusal hid most of them) | **filed as #1231**: an operand-class tracking defect in the aarch64 selector |
| `call_indirect` table not linked in a self-contained image (#717) | 2 on the v0.63 set; 0 now (`nop`/`load` flipped to `ok` once the single-module path handed the backend a real table) | **declined**: silicon-gated for the remaining multi-module shapes |
| multi-memory in a self-contained image (VCR-MEM-002) | 17 on the v0.63 set; 1 now | **moved out of the family**: a multi-memory decline; memory k cannot be bounds-checked on any profile (#1145) and no memory-k execution oracle exists for a self-contained image, so it is declined here, not closed |

## Relationship to the acceptance ladder

This document and `ACCEPTANCE_LADDER.md` measure **different things** and
should not be compared:

- **this** — the *spec suite* (257 conformance `.wast` files), one fixed
  invocation, "does the standard's own corpus compile".
- **the ladder** — the *reachable real-world corpus* (243 modules), flag-aware,
  "what can a consumer actually build".

A file here can be `partial` while the equivalent shape is a full accept there,
and vice versa. Quoting one as the other is the error this pair exists to
prevent.

## Caveats carried from #1168 and #1225

Before v0.63 these figures were measured on a path that **under-compiled**: the
`.wast` input path skipped the reachable-callgraph closure, so non-exported
callees were never built and three of four backends shipped objects with
dangling symbols at exit 0. `RQ-63-WASTCLOSURE` fixed it (`92 / 82 / 60` →
`84 / 74 / 57`). Before v0.65 they were measured on a path that **compiled the
wrong object** (#1225, above): `84 / 74 / 57` → `47 / 43 / 47`. Neither of the
earlier figures is comparable to these, and both drops are objects that were
not what the module says ceasing to count as successes — the same shape as
ARM's 81 % → 11 %.
