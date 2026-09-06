# Spec-suite census by WASM feature family — v0.63

**Measured 2026-09-06** on synth at `e3a09ac2`, over all **257 top-level
`.wast` files** of the pinned spec test suite (`tests/spec-testsuite`,
submodule `345367358`).

Derived by grouping the existing `scripts/spec_compile_census.py` census by
feature family — **the census's own `classify()` is reused**, not
reimplemented, so there is no second source of truth to drift.

## Why this document exists

The census publishes ONE derived figure per backend — `at-least-one-export`,
currently **84 / 74 / 57**. That number is correct and CI-gated, and it is the
wrong number to plan from, because it averages two populations that should
never be averaged: families synth **targets**, and families synth has **never
implemented**.

## The split — files fully `ok` / `partial`

| family | files | arm | riscv | aarch64 |
|--------|-------|-----|-------|---------|
| **MVP core** | 114 | **14** / 39 | **11** / 38 | **21** / 17 |
| SIMD | 59 | 0 / 0 | 0 / 0 | 0 / 0 |
| reference types | 27 | 2 / 8 | 1 / 8 | 1 / 1 |
| GC | 16 | 0 / 3 | 0 / 3 | 0 / 0 |
| bulk memory | 15 | 5 / 6 | 0 / 10 | 1 / 9 |
| memory64 | 14 | 1 / 6 | 0 / 3 | 4 / 3 |
| relaxed SIMD | 4 | 0 / 0 | 0 / 0 | 0 / 0 |
| exception handling | 4 | 0 / 0 | 0 / 0 | 0 / 0 |
| tail call | 3 | 0 / 0 | 0 / 0 | 0 / 0 |
| multi-value | 1 | 0 / 0 | 0 / 0 | 0 / 0 |

## The two facts the aggregate hides

### 1. MVP core is 14 of 114 fully-`ok` on arm

The scalar foundation every other family rests on is **12 %** complete by this
measure (11 riscv, 21 aarch64). It is the single most decision-relevant number
in the project and it appeared nowhere before this document — every "should we
add X" conversation was held without it.

It is why **`VCR-SIMD-001` is gated on the scalar core, not on appetite**:
building a vector story on a 12 %-complete foundation widens the base faster
than it is closed.

### 2. 86 files — 33 % of the suite — are families with ZERO support anywhere

SIMD 59, GC 16, relaxed SIMD 4, exception handling 4, tail call 3.

Those files depress the aggregate while representing work that was **never
scoped**. A reader cannot tell `84/257` apart from a compiler that tries
everything and half-fails. The truth is a compiler that does one family
deliberately and declines the rest — which is the loud-decline stance the
compliance envelope already claims as a differentiator, and it should be
legible from the number.

**Declining a family synth does not target is not a failure.** It is the
boundary, and stating it as a boundary is more honest than letting it sit
inside an average.

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

## Caveat carried from #1168

Before v0.63 these figures were measured on a path that **under-compiled**: the
`.wast` input path skipped the reachable-callgraph closure, so non-exported
callees were never built and three of four backends shipped objects with
dangling symbols at exit 0. `RQ-63-WASTCLOSURE` fixed it, and the numbers above
are post-fix. The pre-v0.63 figures (`92 / 82 / 60`) are **not comparable** to
these, and the drop to `84 / 74 / 57` is objects that could not link ceasing to
count as successes — the same shape as ARM's 81 % → 11 %.
