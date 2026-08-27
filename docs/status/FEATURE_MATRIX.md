# Feature Matrix — Current State

> **GENERATED — do not hand-edit.** Rendered from
> `scripts/templates/feature_matrix.md.tmpl` with machine-derived counts by
> `python3 scripts/claim_check.py claims.yaml --emit-status`.
> The `claim-check` CI job regenerates it and fails if this committed copy is
> stale. All numbers come from [`artifacts/status.json`](../../artifacts/status.json),
> which is re-derived from source on every run — never hand-edited.

**Workspace version:** 0.60.0

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
| ARM A32 | `synth-backend` | `cortex-r5` | i32 + i64 integer family (222-variant no-wildcard tripwire, #615); self-contained `call_indirect` declines loudly (no flash-table builder) |
| RISC-V RV32IMAC | `synth-backend-riscv` | `rv32imac`, `rv32imc`, `rv32im`, `rv32i`, `rv32gc`, `esp32c3` | i32 + i64 integer ops, control flow, calls incl. `call_indirect`, memory loads/stores; relocatable ELF; import/external calls emit `R_RISCV_CALL_PLT` relocations (`.rela.text`, undefined import symbols — #871) with exact-arity marshalling from the module signature tables; >8-arg / i64-arg / multi-value calls decline loudly; floats decline loudly |
| AArch64 (A64, host-native) | `synth-backend-aarch64` | `cortex-a53` (host-linkable ET_REL, `-b aarch64`) | 185 of 197 probed WASM op shapes lower (the op-level surface is DERIVED by running the real selector — `artifacts/aarch64-op-surface.json`, not a hand list): i32 + i64 integer core incl. `div_s/div_u/rem_s/rem_u` (with the ÷0 + INT_MIN/−1 WASM trap guards), `popcnt`, `select` (branchless `CSEL`/`FCSEL`, all four value types), `drop`/`nop`, `i32.wrap_i64`, `i64.extend_i32_{s,u}`, and the five `extend8/16/32_s` sign extensions (#851 v0.53); scalar f32/f64 incl. domain-guarded trapping float→int truncations, IEEE 754-2019 min/max, copysign, and f64↔i64 reinterpret (#538 milestone 4, #851); full control flow — `block`/`loop`/`if`/`else`/`br`/`br_if`/`return` (#538 cf + #851), plus **`br_table`** as a compare-and-branch chain (`cbz` / `cmp`+`b.eq` per arm, then the default `b`; the index is compared in the W view, so an out-of-range index — including the "negative" i32s that denote huge unsigned values — reaches the DEFAULT exactly as WASM requires, and one table may MIX a backward loop header with forward block ends) and **VALUE-CARRYING `block`/`loop`/`if`** (a reserved reconciliation register per frame that every incoming edge deposits into — `br`/`br_if` at the branch, the then-arm at `else`, the fall-through at `end` — so the frame's result is in ONE register on every path; i32/i64 through `mov x`, f32/f64 through `fmov d`. A `br` to a LOOP label carries the loop's PARAMETERS, not its results, so a `loop (result T)` back-edge reconciles nothing) (VCR-A64-CF-001, #851 — execution-verified against wasmtime over the index lattice and both join edges); non-param locals — zero-init stack slots with copy-semantics get/set/tee (#856); linear-memory `i32`/`i64` load/store incl. all sub-word sign/zero forms, **BOUNDS-CHECKED by default** — an out-of-bounds access traps (`brk`) exactly where wasmtime traps, and `--safety-bounds` selects the strategy (`software` = the enforcing default, `none` = explicit opt-out; `mask`/`mpu` hard-error rather than silently degrading) (#851, #865 — execution-verified against the OOB table); fixed-memory `memory.size`/`memory.grow` (declared-min page count; `grow(0)` ≡ size, `grow(n>0)` → −1 — growth failure is spec-permitted and keeps the static bounds limit sound); direct calls (AAPCS64 + `R_AARCH64_CALL26`, #851); **WASM globals** — `global.get`/`global.set` for i32/i64, i.e. every defined global gets an 8-byte slot in a synth-EMITTED `.data` region (`__synth_globals`) carrying its decoded constant initializer (#851 lane L3); **`call_indirect`** — a synth-EMITTED `.text`-resident funcref table (`__synth_func_table`, one `[u32 structural-class-id][b func_N]` record per slot across all tables, null slots `[0][brk #0]`) with all THREE WASM §4.4.8 trap guards emitted inline: out-of-range index (UNSIGNED bounds compare), null slot, and signature mismatch — compared on STRUCTURAL type class, so duplicate-but-identical types stay interchangeable (#851 lane L3, execution-verified against wasmtime incl. every trap); param HOMING (incoming argument registers are stored to stack slots at the prologue, so a param survives a call) — for non-leaf functions that READ a param, and since #971 for ANY function that WRITES one, so `local.set`/`local.tee` on a parameter lowers in leaf functions too. **PRECONDITIONS — exactly ONE, and it is not new:** memory-using functions expect `x28` = linear-memory base on entry, and synth emits NO startup or prologue that establishes it (no linker script, no data section); the embedder/harness must set it, and a module carrying **active data segments is REFUSED loudly** (v0.53 — previously the segments were silently dropped and initialized regions read zeros). The globals region and the funcref table are explicitly **NOT** preconditions: synth EMITS both into the object with their contents, and code reaches them via an `adrp` + `add :lo12:` pair that the linker resolves — there is no globals base register and no table base register, so no second ambient input and nothing that can collide with the linear-memory base (the #275/#717 class). Loud declines, OP-LEVEL — 12 of the 197 probed shapes, SUBSTITUTED from the derived artifact so this list cannot go stale: `memory.copy`, `memory.fill`, `multi-memory wrapper`, `simd (grouped)`, `v128.and`, `v128.andnot`, `v128.const`, `v128.load`, `v128.not`, `v128.or`, `v128.store`, `v128.xor`. Loud declines, MODULE- and SHAPE-LEVEL — **hand-written prose, and explicitly UNCHECKED** (RQ-58-MIRRORS): these are not a function of the op alone, so no derivation covers them; they were verified by compiling one probe module each at v0.58 (18/18 declined) but nothing re-checks them per commit: import calls, `>8` args, float-result callees; the three NAMED residuals of the v0.55 control-flow increment — a `br_table` past 16 targets (the chain is O(n); PC-relative jump-table dispatch is a follow-up), a `br_table` whose targets are VALUE-CARRYING (the flat chain has no per-path edge to deposit a result on), and a block type with PARAMETERS or MULTI-VALUE results (the reconciliation slot is one register); and — rather than guess — an imported global, a global with no decoded constant initializer (float/v128/non-const init expr), a FLOAT param in any function that homes (the slot model is single-register-file), a growable imported table, an element segment that is not statically verifiable, and a table slot holding an imported function |

---

## WebAssembly Operation Coverage (ARM Thumb-2 primary path)

| Category | Status | Notes |
|----------|--------|-------|
| i32 arithmetic / bitwise / comparison / shift / rotate | Y | Full Rocq T1 proofs; Renode + silicon (gale) execution evidence |
| i64 (register pairs) — arithmetic, shifts, rotates, div/rem, compare | Y | Pair lowering complete (#599, #610, #615); execution differentials vs wasmtime |
| f32 scalar via VFP | P (FPU targets) | Arithmetic, all six comparisons, min/max/abs/neg/copysign, load/store and conversions — NaN-aware (v0.41); requires an FPU target (e.g. `cortex-m4f`). **Residual: `f32.{ceil,floor,trunc,nearest}` LOUD-DECLINE on every ARM target** (v0.54): the legacy pseudo-op round-tripped through a saturating `VCVT`, so `ceil(1e30)`, `ceil(±inf)` and `ceil(NaN)` were all wrong — the #709 more-total-than-WASM class. Declining keeps it latent rather than shipping it; a real `VRINT.F32` lowering (the f32 twin of the shipping f64 path) is the follow-up. The f64 rounding ops lower on a double-FPU target (`cortex-m7dp`). |
| f64 scalar via VFP | Y (FPU targets) | Complete (v0.43, #369 closed); marshalling + AAPCS-VFP mixed params |
| Trapping float→int truncations | Y | Domain-guarded (trap, not saturate) — the #709 soundness class |
| Non-trapping `trunc_sat` (0xFC prefix) | Y (FPU targets) | Decoded and lowered as bare saturating VCVT (§4.3.2: NaN→0, out-of-range saturates, never traps). i32-target forms on any FPU target; i64-target forms on a double-FPU target (`cortex-m7dp`) via a branch-free FP word-decompose (v0.49, #782); aarch64 lowers all eight. Residual: i64-from-f32 declines on single-precision FPUs (needs the f64 promote). The falcon `--relocatable cortex-m7dp` D-register-pressure + RA tail closed in v0.53 via VFP register-file spilling (#881); #782 closed v0.49 |
| Control flow (block, loop, if/else, br, br_if, br_table) | Y | Renode execution tests |
| Function calls (direct + `call_indirect`) | Y | `call_indirect` traps per WASM §4.4.8 (OOB index, type mismatch, null slot); self-contained dispatch is PC-relative via a flash funcref table (v0.47) |
| Memory (load/store incl. sub-word, size/grow) | Y | `memory.grow` returns -1 on fixed-memory embedded targets; grow(0) ≡ size |
| Multi-memory | P | N memories lower to N distinct native base regions on ARM `--relocatable` (memory 0 keeps the runtime R11 base; memory k>0 via its own `__synth_wasm_data_<k>` symbol, #406) with an execution differential; everything outside that lane declines loudly — self-contained, native-pointer-abi, shadow-stack, riscv/aarch64, cross-memory copy/fill, i64/f32 access on memory k>0 |
| Globals, select, locals | Y | R9-based globals; cmp→select fusion default-on |
| SIMD (ARM Helium MVE) | R | Cortex-M55 encoding exists; untested on silicon/emulator; SIMD functions loud-skip on all other targets (category-level gate, #680) |
| Component Model | P | Parses + ABI lift/lower; execution needs kiln-builtins; `cabi-arena-realloc` binds natively on self-contained dissolves since v0.47 (#418 closed) |

---

## Mechanized Proofs & Verification

Counts below are machine-derived into `artifacts/status.json` and CI-gated —
see [coq/STATUS.md](../../coq/STATUS.md) for the per-file matrix.

| Track | Derived count(s) | What it covers |
|-------|------------------|----------------|
| Rocq proof suite | 630 Qed / 2 Admitted (+2 `admit.` tactics) | T1 result-correspondence for all i32 and i64 selection; T2 existence-only for float/SIMD; trusted base: 93 Axiom/Parameter declarations |
| Verified selector DSL (VCR-SEL-001) | 80 rules / 80 Qed (1:1, + 7 pilot Qed) | The Rocq-proved rules ARE the shipped lowering path for their covered ops; model generated from the shipped rule table (#667), so selector drift breaks the matching proof |
| Sail/ASL ISA bridge (VCR-ISA-001) | 92 Qed | `coq/Synth/ARM/SailArmBridge.v` |
| ISA-model basis (#867) | 80/80 rule theorems stated against the SIMPLIFIED `ArmSemantics.v` model (0 against the Sail-derived one) · 5 assumed simplified→Sail obligations (`ArmRefinement.v`) · 72 simplified-model axioms | The counted #682-class trusted base — "covered" ≠ "faithful": a Qed against a simplified model is only as good as that model; see `coq/STATUS.md` |
| Model coverage (#867 phase 2) | 26 bridge-validated / 73 simplified-only / 4 UNCOVERED modelled `arm_instr` behaviours | The uncovered complement = candidate list for the next silent miscompile (`artifacts/model-coverage.json`, static heuristic labelled as one; complement is an under-approximation) |
| WasmCert-Coq source anchor (VCR-WASM-001) | 104 Qed | `coq/Synth/WASM/WasmCertBridge.v` — i32 (19 ops) + i64 (22 ops) integer fragments refined against pinned WasmCert-Coq rules |
| Kani (bounded model checking) | 18 harnesses | ARM encoder properties |
| Verus (SMT contracts) | 8 spec functions | `synth-synthesis/src/contracts.rs` |

### Per-compilation validators (run at compile time, not proof time)

| Validator | Status | What it catches |
|-----------|--------|-----------------|
| SMT translation validation | Y | ordeal (pure-Rust QF_BV) default since v0.27.0; Z3 demoted to a feature-gated differential oracle |
| Trap-preservation VC (VCR-VER-002) | Y (live classes) | Dropped WASM traps: i32 + i64 div/rem, memory OOB (all widths), `call_indirect`, `unreachable`, float→int trunc |
| Static-data addressing VC (VCR-VER-003) | Y | Byte-equality of served vs runtime-image static data (the #757 wrong-segment class); spanned accesses, self-contained ROM image; RV32 ships active data segments as `.wasm_data` records — the emitted blob is read back and any served/runtime disagreement hard-errors the compile (#798, v0.48) |
| Proof-carrying specialization (`SYNTH_FACT_SPEC`) | Y (opt-in) | ordeal-certified elisions from loom `wsc.facts` invariants (#494) |
| Proven-safe bounds elision (`--proven-safe`, VCR-MEM-004) | Y (opt-in) | Consumes scry's `safe-accesses.json` (`scry/safe-accesses/v1`, scry#114) and elides the `--safety-bounds software` inline guard at the access sites scry PROVED in-bounds against the memory's guaranteed minimum. FAIL CLOSED on a `module_sha256` mismatch (verified against the exact bytes handed to the decoder, so a pre-compile rewrite that shifts operator indices refuses too), on a `memory_min_bytes` disagreement, and on a malformed/missing/wrong-schema file — each elides NOTHING, warns, and exits 0. Absence from the list means "not proven", NEVER "unsafe": an unlisted site keeps its guard. Each `(func, pc)` key is re-validated against the decoded operator (existence + access kind + width), so a wrong key space elides nothing LOUDLY instead of stripping the wrong guard. Writes a `synth-proven-safe-elisions-v1` attestation for sigil — on refusal too. MEASURED on `proven_safe_bounds_901.wat` (Cortex-M4): 5 of 8 sites proven ⇒ 232 → 152 B (80 B, 58 % of the guard tax) and 70 → 45 executed instructions (#901) |

### WCET (Track D, #778)

| Feature | Status | Notes |
|---------|--------|-------|
| `--emit-wcet` sound per-function cycle bounds | Y | `synth-wcet-v1` sidecar; documented Cortex-M3/M4 worst-case per-op cycles (max over {M3, M4}); sound-critical model constants pinned in `claims.yaml` |
| Statically-proven const-bound loop bounds | Y | Conservative symbolic walk over the final encoded stream (v0.47); nested-multiplicative |
| `--wcet-hints` (untrusted hint seam) | Y | Every hint verified against synth's own derived trip count or rejected with a machine reason — never trusted into a bound |
| Inter-procedural composition (direct call graph) | Y | `total = own + Σ site-multiplier × callee-total` over direct `BL` calls to local bounded callees (v0.48, phase 3); a declined callee propagates its decline UP |
| Bounded single-self-recursion + masked-ceiling data-dependent loops | Y (hint-gated) | Depth/trip are always synth-DERIVED (mask-bounded, entry-independent), never the raw hint; too-low or unverifiable hints rejected with machine reasons (phases 4–5) |
| Unhinted data-dependent loops, indirect/external calls, tree/mutual recursion, i64 software div/rem, non-M3/M4 cores | D | Loud decline with machine reason |

---

## CLI

| Command | Notes |
|---------|-------|
| `synth compile <in> -o <out>` | WAT/WASM → ELF; `--cortex-m`, `--target <profile>`, `-b <backend>`, `--all-exports`, `--relocatable`, `--verify`, `--emit-wcet`, `--wcet-hints`, `--proven-safe` |
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

- The primary ARM Thumb-2 path is a complete i32/i64/f64 compiler — and f32
  complete except the four rounding ops, which loud-decline (see the f32 row) — with
  mechanized proofs on the integer selection and per-compilation validators
  (translation, trap-preservation, static-data addressing) on every build.
- The other three backends are honest subsets: their gaps decline loudly and
  their coverage is listed above, not implied.
- Broad hardware validation is still missing: silicon evidence is
  fixture-scoped (gale), emulation is Renode/QEMU/unicorn.
- Known open soundness/coverage residuals are tracked as issues (e.g. #890: the
  oracle-wiring gate now leaves 0 undeclared and 0 unwired scripts, so a
  forgotten gate is no longer indistinguishable from a deliberately manual one
  — what remains open is the 7 `manual` scripts (external fixture, measurement
  and scratch categories); #851: the aarch64
  op-surface gaps the VCR-SEL-005 third-backend oracle now enumerates
  mechanically; #846: the two `gpio-thin` CRL/CRH sites are now PROVEN by a
  bounded masked-seed evaluation (502 -> 494 B, 3 -> 1 masks); the ONE
  remaining mask is genuinely required, not a residual — its amount is a
  frame-reloaded raw param, so eliding it would be the #682 miscompile).
- **What the oracle steps ATTEST is now stated (#910).** The exit-status-only
  residual noted above was measured and was larger than described: **152 of the
  160** workflow steps that run a `scripts/repro/` oracle asserted nothing
  beyond the process exit code — the pre-#890 hand-wired steps too, not only
  the newly wired ones; exactly 8 asserted a printed verdict or count. Every
  `wired` oracle now declares a `# ci-checks:` floor that
  `scripts/oracle_run.py` enforces per run by counting real emulator entries,
  wasmtime executions and compilations: **147 oracles assert 322,754 emulator
  entries**, 7 assert a printed count, 9 assert compilations, and 1
  (`aarch64_matrix.sh`, a POSIX shell oracle the in-process driver cannot
  instrument) is itemized as unbindable in `scripts/repro/ORACLE_WIRING.md`
  alongside the five other weak floors.
- **The `Code Coverage` percentage was renamed for what it measures (#910).**
  It is `Rust-test Line Coverage (unit + integration only)`: `cargo llvm-cov
  --workspace`, the Rust test suite, in process. It is structurally blind to
  the execution differentials, which spawn the compiler as a separate
  UNINSTRUMENTED process from other jobs — which is why
  `synth-backend-*/src/backend.rs` reads ~42 % while being exercised
  end-to-end by nearly every differential. The number understates the testing
  that exists and is not a completeness measure. The two populations are
  reported separately, in their own units, and are never added together.
- Two residuals live in code comments rather than issues, and are restated here
  so they are not implied away: `validate_segment_rewrite` does NOT catch a
  recoloured `Pop {…, PC}` in the MIDDLE of a segment (pinned at the pass via
  `arch_pinned`, with whole-function `validate_final_allocation` as the
  independent backstop — #872); and a wrong-return-register rewrite is accepted
  by `validate_cfg_rewrite` AND VCR-RA-003 *both*, caught only by execution
  (VCR-DEC-001, flag-off). Two validators sharing a blind spot agree without
  adding evidence.
- **That second residual is now closed STATICALLY** (VCR-VER-004, v0.54):
  `abi_contract::validate_abi_contract` is a FORWARD, value-level check whose
  obligation is the AAPCS result registers hard-named in its own source and whose
  CFG is re-derived from both instruction streams — it takes nothing from the
  pass, so emptying the shared exit contract cannot empty it. Re-running v0.53's
  exact mutation, the two dataflow validators stay green (`validate_cfg_rewrite`
  → Ok, VCR-RA-003 → Consistent) while this one rejects with a concrete violation
  naming `R0`, and the miscompile is not emitted. That is a CI job, not a claim.
- What VCR-VER-004 does **not** close, stated plainly:
  - It is a **gate only on the flag-off** graph-colouring allocator. On the
    DEFAULT path it is a report-only audit held to a CI floor — measured
    `Holds 431 / NotAttempted 202 / Violated 0` over 633 corpus functions (the corpus is `scripts/repro/*.{wat,wasm}`, so it GROWS as lanes add fixtures — the invariant is `Violated 0`, not the absolute counts), so it
    proves the observable return contract on ~68 % of the shipping path —
    `bl`/`blx` calls included, via the shared AAPCS `liveness::call_effect` — and
    declines (never guesses) on the rest. Making it gate the default path means
    hard-erroring a user's compile on a checker whose false-positive rate is
    measured, not proven; that flip is deliberately not taken here.
  - **Memory is not in its obligation.** A mis-renamed store address that a later
    load reads back is a false negative for this instrument (it is covered by
    `validate_cfg_rewrite`'s use-equations when that seed is intact — the two are
    complementary, which is what independence looks like, not redundancy).
  - **The op model is still shared.** Def/use extraction runs through
    `liveness::reg_effect`, so a *mismodeled op* remains a blind spot common to
    all three instruments. VCR-VER-004 closes the shared-*contract* hole, not the
    shared-*op-model* hole. `synth-verify`'s `ArmSemantics::encode_op` is a
    genuinely second model of the same operations; pinning the two against each
    other is the next rung, and until it is done "three independent validators"
    would be an overclaim.
  - **How second that second model is, measured (#923).** "A genuinely second
    model of the same operations" held for fewer operations than it sounds like:
    `encode_op`'s default arm was a SILENT NO-OP, so 87 of `ArmOp`'s 222
    variants — every register-amount shift the selector emits among them — were
    modeled as doing NOTHING, and a lowering that destroyed its own result
    (`ADD r0,r0,r1 ; UXTB r0,r0`, which returns `(x+y) & 0xFF` on silicon) came
    back `Verified` from the value VC. Modeling the shipped ops and making the
    default arm RECORD-and-DECLINE brings the unmodeled set to **73** (41 MVE
    vector ops; 32 others — flag-setting/carry forms, subword and symbol memory,
    branch and stack ops). Those 73 now DECLINE loudly instead of passing. So the
    second model is genuinely second for the i32/i64/VFP core it covers, and
    explicit about the rest; the faithfulness pin between the two op models
    remains the follow-up above.
