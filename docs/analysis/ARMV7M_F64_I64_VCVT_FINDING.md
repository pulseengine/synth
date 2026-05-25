# ARMv7-M FPv5 has no F64 ↔ I64 VCVT — v0.8.0 deferral finding

**Date:** 2026-05-25
**Branch:** `feat/v0.8.0-f64-i64-conversions`
**Status:** Deferred to v0.9.0 (or later)
**Related issues:** [#147](https://github.com/pulseengine/synth/issues/147)
(v0.8.0 umbrella), v0.7.0 CHANGELOG "Deferred to follow-up"

---

## TL;DR

The four WASM ops `F64ConvertI64S`, `F64ConvertI64U`, `I64TruncF64S`,
`I64TruncF64U` cannot be implemented as single-instruction VCVT
encodings on Cortex-M7DP, because the **ARMv7-M FPv5-D16
floating-point architecture does not include 64-bit integer ↔
floating-point VCVT instructions**. These encodings were first added
in **ARMv8-A FEAT_FP**, which is an A-profile feature; no M-profile
core (including Cortex-M55, M85) implements them.

Implementing these ops therefore requires either (a) a multi-instruction
software sequence in the codegen path, or (b) a software-helper call
into a libgcc-style soft-float routine. Both are non-trivial — the
WASM specification mandates **trapping** on NaN inputs and on
out-of-range conversions for the signed/unsigned trunc family
([WASM spec §4.3.2](https://webassembly.github.io/spec/core/exec/numerics.html#xref-exec-numerics-op-trunc-s-mathrm-trunc-s-m-n)),
which interacts with synth's existing trap-emission infrastructure.

Per the v0.8.0 task brief: **"If M7DP doesn't have them as single
instructions: ... defer this PR cleanly with a written architectural
finding."** This document is that finding.

---

## The hardware reality

### What ARMv7-M FPv5 (Cortex-M7DP) supports

From the ARMv7-M Architecture Reference Manual
([DDI 0403E.e](https://developer.arm.com/documentation/ddi0403/latest))
§A7.5 "Floating-point data-processing instructions" and §A8.8 "VCVT,
VCVTR (between floating-point and integer)":

| Variant | Operands | Supported on M7DP |
|---------|----------|-------------------|
| `VCVT.F32.S32` / `VCVT.F32.U32` | Sd, Sm | yes |
| `VCVT.S32.F32` / `VCVT.U32.F32` | Sd, Sm | yes |
| `VCVT.F64.S32` / `VCVT.F64.U32` | Dd, Sm | yes |
| `VCVT.S32.F64` / `VCVT.U32.F64` | Sd, Dm | yes |
| `VCVT.F32.F64` (demote) | Sd, Dm | yes |
| `VCVT.F64.F32` (promote) | Dd, Sm | yes |
| **`VCVT.F32.S64` / `VCVT.F32.U64`** | **Sd, (Rlo,Rhi)** | **no** |
| **`VCVT.F64.S64` / `VCVT.F64.U64`** | **Dd, (Rlo,Rhi)** | **no** |
| **`VCVT.S64.F32` / `VCVT.U64.F32`** | **(Rlo,Rhi), Sm** | **no** |
| **`VCVT.S64.F64` / `VCVT.U64.F64`** | **(Rlo,Rhi), Dm** | **no** |

The "no" rows are the missing instructions. They are listed in
**A-profile** references (ARMv8 ARM, DDI 0487, C7.2.337 onward) and
are gated on **FEAT_FP** — explicitly an ARMv8-A floating-point
feature. They are not part of:

- VFPv2 (ARMv6)
- VFPv3 / VFPv3-D16
- VFPv4 / VFPv4-D16
- **FPv5 / FPv5-D16** (the M-profile flavor used by Cortex-M7DP, M33-DP, M55, M85)

The pattern is consistent with the existing situation in synth's
codebase for `F32ConvertI64S/U` and `F32DemoteF64`-via-S64-route, which
are already deferred with the same root cause — see
`crates/synth-synthesis/src/instruction_selector.rs` lines 1956–1960.

### Why this is not just an encoding-table gap

This is a real architectural absence, not a missing encoding in our
encoder. The ARM Architecture Reference Manuals for ARMv6-M, ARMv7-M,
and ARMv8-M all omit these opcodes. The encoding space they would
occupy under VFP's `op2` field is reserved/undefined on M-profile.
Emitting an A-profile-only 64-bit VCVT bit pattern on a Cortex-M7DP
would either decode to a different instruction (worst case, a silent
miscompile) or fault with `UNDEFINSTR` — exactly the kind of bluff
the task brief and PulseEngine's "rigor and honesty" principle
forbid.

---

## Why not just implement a multi-instruction software sequence?

This is the obvious follow-up. The reason we don't do it inline in
this PR is **scope and correctness obligations**:

1. **WASM trap semantics for `I64TruncF64S/U`.** The WASM spec
   ([§4.3.2 trunc_s/trunc_u](https://webassembly.github.io/spec/core/exec/numerics.html#xref-exec-numerics-op-trunc-s-mathrm-trunc-s-m-n))
   requires *trapping* if the input is NaN or out of i64 range. This
   means the sequence must include:
   - NaN detection (VCMP.F64 + VMRS APSR_nzcv)
   - Range comparison against `±2^63` (signed) or `[0, 2^64)` (unsigned)
   - A trap-emission branch using synth's existing trap infrastructure
     (see `synth-synthesis::trap_emitter` and the established WASM-trap
     conventions in i32-div-trap-zero / i32-trunc-out-of-range)

2. **Algorithmic implementation of F64↔I64.** A correct, fast
   software conversion is ~30 instructions per op (split-by-sign,
   exponent extraction, mantissa shift, sign-bit reassembly, round-mode
   handling for F64ConvertI64*). The signed and unsigned variants share
   most of the work but diverge at the sign-handling boundary. This
   is the level of complexity normally pushed into a libgcc-style
   helper (e.g., `__aeabi_l2d`, `__aeabi_d2lz`).

3. **Verifiability obligation.** synth has a Rocq proof suite
   (`coq/Synth/`) that establishes T1 result-correspondence for ARM
   sequences against WASM semantics. Adding a 30-instruction software
   conversion without a matching mechanized correctness argument would
   regress the verification posture v0.8.0 is *raising*. The v0.8.0
   umbrella issue #147 promotes i64 *arithmetic* from T2 to T1 — adding
   an unproven i64-conversion sequence on top of that would be
   directionally wrong.

4. **Issue #147 explicitly marks this PR "optional additive".** It is
   not required for v0.8.0's stated theme (i64 T1 result-correspondence
   parity). The right answer when an optional additive turns out
   harder-than-budgeted is to record the finding and move it to a
   later milestone.

5. **No `gale` / libgcc-equivalent yet.** Synth does not currently link
   against a soft-float runtime. The `meld` platform crate has
   established conventions for cross-component dispatch but no
   floating-point helper layer; introducing one is a separate
   infrastructure decision.

---

## What gets deferred

The four WASM ops below remain in the v0.7.0 "Deferred to follow-up"
state. Synth's selector continues to emit the existing typed error
(`Error::Synthesis`) with a message naming "i64 register pairs on
32-bit ARM" — surfaced cleanly to the user, never miscompiled.

- `F64ConvertI64S` (signed i64 → f64)
- `F64ConvertI64U` (unsigned i64 → f64)
- `I64TruncF64S` (f64 → signed i64, trapping on NaN/range)
- `I64TruncF64U` (f64 → unsigned i64, trapping on NaN/range)

The existing F32 counterparts remain deferred for the same reason
(see lines 1956–1960 of `instruction_selector.rs`):

- `F32ConvertI64S`, `F32ConvertI64U`, `I64TruncF32S`, `I64TruncF32U`
- `F32DemoteF64` (separate but related — needs a VCVT.F32.F64
  encoder, *that one is actually a single-instruction op* on M7DP
  and is tracked as the other "optional additive" PR in #147 item 7)

---

## What this PR ships

Nothing executable. This PR documents the finding and updates:

- `CHANGELOG.md` — adds a note under `[Unreleased]` pointing at this
  finding and explaining why the four v0.7.0 "Deferred to follow-up"
  ops remain deferred. The v0.7.0 history section is frozen and
  unchanged.
- `docs/analysis/ARMV7M_F64_I64_VCVT_FINDING.md` — this document.

No code changes. No new encoder variants (those would be bogus). No
new tests (would test bogus encodings).

---

## Path to closing this in a future milestone

The right shape of the eventual closing PR:

1. **Decide the helper-vs-inline question.** Either:
   - Inline software sequence emitted by the selector (4 ops × ~30
     instructions, ~120 lines of ArmOp emission)
   - **Or** add a `synth-runtime` / `gale-softfloat`-style helper crate
     and emit a BL into it (cleaner separation, matches the gale
     pattern for primitives synth doesn't compile itself)
2. **Add WASM-trap integration.** Reuse the existing `trap_emitter`
   conventions used by `I32DivS`-zero and `I32TruncF32S`-out-of-range.
3. **Add Rocq proofs.** At minimum T2 existence-only with a path to
   T1 result-correspondence; the WASM reference operator semantics
   are already encoded in `coq/Synth/WASM/WasmSemantics.v`.
4. **Add WAST conformance tests.** The `tests/spec-testsuite` harness
   already runs the upstream WASM conversion tests — they're currently
   skipped on M7DP for these four ops; un-skip on closure.

Out-of-scope for this v0.8.0 deferral PR but tracked for the next
floating-point milestone.

---

## References

- ARMv7-M Architecture Reference Manual, DDI 0403E.e, §A7.5 and §A8.8
  (VCVT variants).
- ARMv8-A Architecture Reference Manual, DDI 0487, §C7.2 (VCVT
  encodings with 64-bit operands gated on FEAT_FP).
- WebAssembly Core Specification, [§4.3.2 Numerics — `itrunc_sat` /
  `itrunc`](https://webassembly.github.io/spec/core/exec/numerics.html#xref-exec-numerics-op-trunc-s-mathrm-trunc-s-m-n).
- synth v0.7.0 CHANGELOG entry "Deferred to follow-up" (lines 62–67).
- synth umbrella issue
  [#147](https://github.com/pulseengine/synth/issues/147),
  "Optional additive PRs" item 6.
- synth `crates/synth-synthesis/src/instruction_selector.rs` lines
  1956–1960 (existing F32 deferral with identical root cause).
