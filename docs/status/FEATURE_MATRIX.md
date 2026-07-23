# Feature Matrix — Current State

> **GENERATED — do not hand-edit.** Rendered from
> `scripts/templates/feature_matrix.md.tmpl` with machine-derived counts by
> `python3 scripts/claim_check.py claims.yaml --emit-status`.
> The `claim-check` CI job regenerates it and fails if this committed copy is
> stale. All numbers come from [`artifacts/status.json`](../../artifacts/status.json),
> which is re-derived from source on every run — never hand-edited.

**Workspace version:** 0.50.1

---

## Legend

| Symbol | Meaning |
|--------|---------|
| Y | Working — implemented and oracle/CI-gated |
| P | Partial — implemented with named, tracked gaps |
| D | Declined loudly — compile fails with a machine reason, never silent wrong code |
| R | Research/experimental |

The project-wide honesty rule: an unsupported construct must **loud-decline**
(the #369/#554/#615 class of silent drops is gated against in CI), so "D" is a
soundness feature, not an absence.

---

## Backends

| Backend | Crate | Targets | Coverage |
|---------|-------|---------|----------|
| ARM Thumb-2 (primary) | `synth-backend` | `cortex-m3`, `cortex-m4`, `cortex-m4f`, `cortex-m7`, `cortex-m7dp` (+ `cortex-m55` experimental MVE) | i32 + i64 (register pairs) complete; scalar f32/f64 via VFP on FPU targets; control flow (block/loop/if/br/br_table); memory incl. sub-word; direct calls; `call_indirect` in both relocatable and self-contained `--cortex-m` images (v0.47, #275) |
| ARM A32 | `synth-backend` | `cortex-r5` | i32 + i64 integer family (221-variant no-wildcard tripwire, #615); self-contained `call_indirect` declines loudly (no flash-table builder) |
| RISC-V RV32IMAC | `synth-backend-riscv` | `rv32imac`, `rv32imc`, `rv32im`, `rv32i`, `rv32gc`, `esp32c3` | i32 + i64 integer ops, control flow, calls incl. `call_indirect`, memory loads/stores; relocatable ELF; floats decline loudly |
| AArch64 (A64, host-native) | `synth-backend-aarch64` | `cortex-a53` (host-linkable ET_REL, `-b aarch64`) | 111 distinct WASM ops handled by the selector: i32 + i64 integer core (no div/rem/popcnt yet), scalar f32/f64 incl. domain-guarded trapping float→int truncations, IEEE 754-2019 min/max, copysign (#538 milestone 4); forward VOID-result `block` with `br`/`br_if` (#538 cf increment) — `loop`/`if`/`br_table`, value-carrying blocks, memory, and everything else decline loudly |

---

## WebAssembly Operation Coverage (ARM Thumb-2 primary path)

| Category | Status | Notes |
|----------|--------|-------|
| i32 arithmetic / bitwise / comparison / shift / rotate | Y | Full Rocq T1 proofs; Renode + silicon (gale) execution evidence |
| i64 (register pairs) — arithmetic, shifts, rotates, div/rem, compare | Y | Pair lowering complete (#599, #610, #615); execution differentials vs wasmtime |
| f32 scalar via VFP | Y (FPU targets) | Complete op set incl. all six comparisons, NaN-aware (v0.41); requires an FPU target (e.g. `cortex-m4f`) |
| f64 scalar via VFP | Y (FPU targets) | Complete (v0.43, #369 closed); marshalling + AAPCS-VFP mixed params |
| Trapping float→int truncations | Y | Domain-guarded (trap, not saturate) — the #709 soundness class |
| Non-trapping `trunc_sat` (0xFC prefix) | Y (FPU targets) | Decoded and lowered as bare saturating VCVT (§4.3.2: NaN→0, out-of-range saturates, never traps). i32-target forms on any FPU target; i64-target forms on a double-FPU target (`cortex-m7dp`) via a branch-free FP word-decompose (v0.49, #782); aarch64 lowers all eight. Residuals: i64-from-f32 declines on single-precision (needs the f64 promote); a pressure-dependent f32 class on `--relocatable cortex-m7dp` still tracked in #782 |
| Control flow (block, loop, if/else, br, br_if, br_table) | Y | Renode execution tests |
| Function calls (direct + `call_indirect`) | Y | `call_indirect` traps per WASM §4.4.8 (OOB index, type mismatch, null slot); self-contained dispatch is PC-relative via a flash funcref table (v0.47) |
| Memory (load/store incl. sub-word, size/grow) | Y | `memory.grow` returns -1 on fixed-memory embedded targets; grow(0) ≡ size |
| Multi-memory | D | Module-level loud decline with machine reason (#406 phase 1); fused components need single-memory mode |
| Globals, select, locals | Y | R9-based globals; cmp→select fusion default-on |
| SIMD (ARM Helium MVE) | R | Cortex-M55 encoding exists; untested on silicon/emulator; SIMD functions loud-skip on all other targets (category-level gate, #680) |
| Component Model | P | Parses + ABI lift/lower; execution needs kiln-builtins; `cabi-arena-realloc` binds natively on self-contained dissolves (#418 partially open) |

---

## Mechanized Proofs & Verification

Counts below are machine-derived into `artifacts/status.json` and CI-gated —
see [coq/STATUS.md](../../coq/STATUS.md) for the per-file matrix.

| Track | Derived count(s) | What it covers |
|-------|------------------|----------------|
| Rocq proof suite | 591 Qed / 3 Admitted (+2 `admit.` tactics) | T1 result-correspondence for all i32 and i64 selection; T2 existence-only for float/SIMD; trusted base: 93 Axiom/Parameter declarations |
| Verified selector DSL (VCR-SEL-001) | 50 rules / 50 Qed (1:1, + 7 pilot Qed) | The Rocq-proved rules ARE the shipped lowering path for their covered ops; model generated from the shipped rule table (#667), so selector drift breaks the matching proof |
| Sail/ASL ISA bridge (VCR-ISA-001) | 92 Qed | `coq/Synth/ARM/SailArmBridge.v` |
| WasmCert-Coq source anchor (VCR-WASM-001) | 104 Qed | `coq/Synth/WASM/WasmCertBridge.v` — i32 integer fragment refined against pinned WasmCert-Coq rules |
| Kani (bounded model checking) | 18 harnesses | ARM encoder properties |
| Verus (SMT contracts) | 8 spec functions | `synth-synthesis/src/contracts.rs` |

### Per-compilation validators (run at compile time, not proof time)

| Validator | Status | What it catches |
|-----------|--------|-----------------|
| SMT translation validation | Y | ordeal (pure-Rust QF_BV) default since v0.27.0; Z3 demoted to a feature-gated differential oracle |
| Trap-preservation VC (VCR-VER-002) | Y (live classes) | Dropped WASM traps: i32 + i64 div/rem, memory OOB (all widths), `call_indirect`, `unreachable`, float→int trunc |
| Static-data addressing VC (VCR-VER-003) | Y | Byte-equality of served vs runtime-image static data (the #757 wrong-segment class); spanned accesses, self-contained ROM image; RV32 warns loudly on dropped initializer bytes |
| Proof-carrying specialization (`SYNTH_FACT_SPEC`) | Y (opt-in) | ordeal-certified elisions from loom `wsc.facts` invariants (#494) |

### WCET (Track D, #778)

| Feature | Status | Notes |
|---------|--------|-------|
| `--emit-wcet` sound per-function cycle bounds | Y | `synth-wcet-v1` sidecar; documented Cortex-M3/M4 worst-case per-op cycles (max over {M3, M4}); sound-critical model constants pinned in `claims.yaml` |
| Statically-proven const-bound loop bounds | Y | Conservative symbolic walk over the final encoded stream (v0.47); nested-multiplicative |
| `--wcet-hints` (untrusted hint seam) | Y | Every hint verified against synth's own derived trip count or rejected with a machine reason — never trusted into a bound |
| Data-dependent loops, calls, i64 software div/rem, non-M3/M4 cores | D | Loud decline with machine reason |

---

## CLI

| Command | Notes |
|---------|-------|
| `synth compile <in> -o <out>` | WAT/WASM → ELF; `--cortex-m`, `--target <profile>`, `-b <backend>`, `--all-exports`, `--relocatable`, `--verify`, `--emit-wcet`, `--wcet-hints` |
| `synth verify <wat> <elf>` | Standalone translation validation (feature-gated build) |
| `synth disasm <elf>` | Disassemble generated ELF |
| `synth parse <wasm>` | Parse and analyze WASM components |
| `synth synthesize` | Synthesis pipeline entry (WIT-driven) |
| `synth target-info <target>` | Show a target profile |
| `synth backends` | List registered backends and capabilities |

---

## Testing

| Type | Notes |
|------|-------|
| Rust unit + integration tests | `cargo test --workspace`; count is whatever CI runs today — deliberately not hand-pinned here |
| Rocq proofs | `bazel test //coq:verify_proofs` (hermetic via Nix) |
| Renode emulation | ARM Cortex-M4 robot tests via `rules_renode` |
| Execution differentials | unicorn/wasmtime differential scripts in `scripts/repro/`, CI-gated (symtab-based, host-independent) |
| Silicon (gale loop) | Fixture-scoped cycle + correctness gates on NUCLEO-G474RE / STM32F100; no broad board matrix |
| WASM spec test suite | Compile-rate tracked by CI (`tests/spec-testsuite`); not executed on emulator |

---

## Honest Summary

- The primary ARM Thumb-2 path is a complete i32/i64/f32/f64 compiler with
  mechanized proofs on the integer selection and per-compilation validators
  (translation, trap-preservation, static-data addressing) on every build.
- The other three backends are honest subsets: their gaps decline loudly and
  their coverage is listed above, not implied.
- Broad hardware validation is still missing: silicon evidence is
  fixture-scoped (gale), emulation is Renode/QEMU/unicorn.
- Known open soundness/coverage residuals are tracked as issues (e.g. #782:
  `trunc_sat` + a pressure-dependent f32 class on `--relocatable cortex-m7dp`;
  #418: real dissolved-component fixture).
