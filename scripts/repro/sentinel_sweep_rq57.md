# RQ-57-SENTINEL — numeric-sentinel audit (Refs #953, #932)

Sweep of every size/count/address path where a NUMERIC SENTINEL stands in for
absence, across `synth-core`, `synth-backend`, `synth-backend-riscv`,
`synth-backend-aarch64`, `synth-cli`, `synth-verify` (plus `synth-synthesis`
where it carries a bounds value). Non-test code only; line numbers as of the
sweep commit.

**Denominator: 54 sites examined. 4 converted (with 2 latent defects found and
fixed), 41 classified (a) with an argument each, 9 classified (c) residuals
(listed, named, not silently dropped).**

Classification key (from the release artifact):

- **(a)** the sentinel CANNOT collide with a legitimate value — argued below.
- **(b)** it CAN collide — converted.
- **(c)** it CAN collide and is safe only because ANOTHER pass's rule prevents
  it (the #946 "true for the wrong reason" class) — convert, or list loudly.

## Converted in this PR

| # | Site | Was | Class | Finding |
|---|------|-----|-------|---------|
| C1 | `synth-backend/src/arm_backend.rs` mask gate | `bytes != 0 && !is_power_of_two` — 0 exempt as "unknown" | (b) | **LATENT SECURITY DEFECT (third instance of the #932/#953 disease).** A `(memory 0)` module under `--safety-bounds mask` compiled with startup `R10 = 0`; the emitted guard `SUB R12, R10, #1; AND addr, R12` computes `0 − 1 = 0xFFFFFFFF` — an IDENTITY mask. Every access executed unmasked at `[R11 + addr]` for any 32-bit addr: unbounded OOB read AND write in the mode whose purpose is bounding. Verified pre-fix on the v0.56.1 tree (exit 0, `movw r10, #0x0` in the reset handler). Now: zero-byte memory REFUSES loudly. Test: `arm_safety_bounds_mask_zero_size_refused_rq57` + CLI `arm_mask_zero_memory_refused`. |
| C2 | `synth-cli/src/main.rs` single-function config (`linear_memory_bytes: if aarch64 {..} else { 0 }`) | forced 0 for ARM/RV32 on a comment claiming the field was "never consumed" there | (c) | **LATENT DEFECT — the comment's claim was false for RV32** (its `compile_function` has always read the field), and after #953 deleted the rv32 fallback, `--func-index` + `--safety-bounds software` on a `(memory 1)` module compiled EVERY access to the zero-size `ebreak` fold (verified pre-fix: `00050293 00100073` at entry; a live availability miscompile in v0.56.1). Now: the module's declared size threads to ALL backends. Byte-invisible where unconsumed (ARM reads it only for the mask gate + native-ABI statics gate, both off here; frozen anchors are `--all-exports`). Tests: `rv32_single_func_software_uses_declared_bound` + fail-closed control `rv32_single_func_zero_memory_stays_fail_closed`. |
| C3 | `synth-cli/src/main.rs` elision attestation `memory_min_bytes: proven_safe_module_min_bytes.unwrap_or(0)` | "unreachable by construction" comment | (c) | Safe only because the ingest closure's acceptance rule refuses a floorless module — a rule in a different code region. If it drifts, the flattened 0 is the exact #932 lie written into a signed attestation. Converted to `.expect(...)` — an invariant break now panics loudly instead of attesting an invented 0 B floor. |
| C4 | `synth-cli/src/main.rs` `NativeGlobalsLayout.sp_init: i32` (0 = "no SP global") | `stack_pointer_global_opt.map(..).unwrap_or(0)` | (c) | 0-for-absent was indistinguishable from a real SP init of 0. Extent consumers happened to treat 0 as the max-fold identity (safe by coincidence of consumer shape), and `--shadow-stack-size 0` on a module with NO SP global fell through into the re-base machinery against a phantom reservation. Converted to `Option<i32>`: extent folds map `None → 0` explicitly as the identity; the shrink REFUSES `None` with a machine reason. Byte-identical otherwise. |

## Class (a) — sentinel cannot collide (argument per site)

| # | Site | Pattern | Why 0 (or MAX) cannot lie |
|---|------|---------|--------------------------|
| A1 | `synth-backend-riscv/src/backend.rs:75` | `memories.first().map(initial_bytes).unwrap_or(0)` | Post-#953 contract: no defined memory = zero bytes = every access traps (fail-closed). Imported-memory caveat is R1 below. |
| A2 | `synth-backend-riscv/src/backend.rs:240` | mask `mem_size - 1` after `is_power_of_two` | `0.is_power_of_two() == false` → size 0 REFUSES loudly (generic message, but loud). rv32 never had the ARM C1 exemption. |
| A3 | `synth-backend-riscv/src/backend.rs:400` | `count_params` `.max().unwrap_or(0)` | 0 is the true count of an empty set — the value IS the count, not a stand-in. |
| A4 | `synth-backend/src/arm_backend.rs:236` | same | same |
| A5 | `synth-backend-aarch64/src/backend.rs:198` | same | same |
| A6 | `synth-backend-aarch64/src/backend.rs:74` | `limit_bytes: linear_memory_bytes as u64` raw | 0 = zero pages folds to unconditional `brk` — statically-correct always-trap (the model #953 adopted). |
| A7 | `synth-backend-aarch64/src/encoder.rs:577` | `position(|h| h != 0).unwrap_or(0)` | value 0 has no non-zero halfword; emitting `movz w, #0` from position 0 is exactly correct. |
| A8 | `synth-backend-aarch64/src/selector.rs:1400/1420/1444/1463` | `imm.unwrap_or(0)` | `form_ea` returns `None` = offset fully folded into the EA register, so the residual immediate IS 0; a real residual of 0 encodes identically. Same value, same bytes. |
| A9 | `synth-backend-aarch64/src/selector.rs:2588` | `type_class_ids.get(ti).unwrap_or(0)` | 0 is a RESERVED id (assignment starts at 1, `wasm_decoder::structural_type_class_ids`) and is checked two lines later: `expected == 0` → loud decline. |
| A10 | `synth-core/src/wasm_decoder.rs:473` | funcref slot class id `unwrap_or(0)` | id 0 never matches an expected class (≥ 1) → runtime TRAP, not a wrong branch. Documented at the site. |
| A11 | `synth-core/src/wasm_decoder.rs:562` | `vec![0; size.unwrap_or(0)]` sidecar | zero-filled sidecar words are id 0 = trap-on-dispatch — fail-closed for a statically-unknown table image. |
| A12 | `synth-core/src/wasm_decoder.rs:1235` | `table_index.unwrap_or(0)` | wasm spec: an elem segment with omitted table index targets table 0. Spec semantics, not a sentinel. |
| A13 | `synth-core/src/wasm_stack_check.rs:108` | `try_from(max).unwrap_or(u32::MAX)` | saturation UP on overflow = larger claimed stack depth = strictly more conservative. |
| A14 | `synth-core/src/arena_bind.rs:434` | `unwrap_or(u32::MAX).min(0xFFFF_0000)` | saturating cap immediately clamped; overflow can only shrink the arena, never grow it. |
| A15 | `synth-core/src/arena_bind.rs:446` | `global_top .max().unwrap_or(0)` | empty set claims nothing; `.max(16)` floor applies regardless. A real global init of 0 also claims nothing — identical meaning. |
| A16 | `synth-core/src/static_data_addr.rs:493` | `image_extent .max().unwrap_or(0)` | the true extent of zero segments is 0; downstream loops over `[0, 0)` are correct no-ops. |
| A17 | `synth-core/src/static_data_addr.rs:537` | `runtime.get(addr).unwrap_or(0)` | uncovered address OWES 0 — wasm zero-init semantics; documented at the site. This is the value, not its absence. |
| A18 | `synth-core/src/static_data_addr.rs:649` | extent, as A16 | same |
| A19 | `synth-core/src/static_data_addr.rs:375` | `served: served.unwrap_or(0)` | the mismatch DECISION compares `Option`s (`served != Some(runtime_byte)`); only the already-failed report's display flattens. Cannot change a verdict. |
| A20 | `synth-core/src/dwarf_line.rs:190/193` | line/file 0 | DWARF's own convention: line 0 = "no source line". The consumer speaks DWARF. |
| A21 | `synth-core/src/dwarf_line.rs:298` | `high_pc = max().unwrap_or(0) + 1` | synthetic end-of-range for an empty table; range stays empty. |
| A22 | `synth-core/src/dwarf_line.rs:144/223` | `unwrap_or_default()` | collection defaults (no rows/no files), not numeric stand-ins. |
| A23 | `synth-core/src/sbom.rs:412` | epoch secs `unwrap_or(0)` | pre-1970 clock → 1970 timestamp in SBOM metadata; diagnostic field, collision physically impossible on a sane host, and a wrong date cannot alter any verdict. |
| A24 | `synth-core/src/provenance.rs` + decoder | `wsc_facts.unwrap_or_default()` | empty facts = "no facts forwarded" = every elision declines (fail-safe rule documented in #494). |
| A25 | `synth-verify/src/solver.rs:243` | model completion `unwrap_or(0)` | a variable the SAT core never saw is unconstrained; ANY value witnesses (z3 completes with 0 identically). |
| A26 | `synth-verify/src/solver.rs:348` | timeout `unwrap_or(u32::MAX)` | saturating a deadline UP = weaker timeout, never a wrong verdict (verdicts are Sat/Unsat/Unknown). |
| A27 | `synth-verify/src/expansion_validator.rs:888` | `last().map(off+len).unwrap_or(0)` | an empty instruction stream has length 0 — the value, not a sentinel. |
| A28 | `synth-verify/src/fact_spec.rs:194` | `linear_memory_bytes`, `0` documented "= unknown" | the two meanings (unknown / zero-byte memory) COINCIDE in effect: the only consumer action is elision, which requires discharging `addr + len ≤ bound` — impossible at 0 either way → guards stay. Fail-closed under both readings. |
| A29 | `synth-backend/src/elf_builder.rs:790/912` | `if ph_count > 0 {..} else { 0 }` | zero program headers genuinely have offset/entry-size 0 (ELF spec for empty PH table). |
| A30 | `synth-cli/src/main.rs:1690` | `func_index.unwrap_or(0)` | documented CLI default: no `--func-index`/`--func-name` = compile function 0. A stated default, not absence-as-value. |
| A31 | `synth-cli/src/main.rs:1812` | `single_func_linear_memory_bytes` `unwrap_or(0)` | post-#953 contract: no DEFINED memory = zero bytes (software traps, mask refuses per C1). Imported-memory caveat = R1. |
| A32 | `synth-cli/src/main.rs:2921` | merged-memory `max` seed 0 | max-accumulator seed: any real memory beats "none". |
| A33 | `synth-cli/src/main.rs:3085` | `linmem_bytes` → SP heuristic | with 0 no candidate passes `0 < v ≤ linmem` → promotion disabled — fail-safe (an optimization declines). |
| A34 | `synth-cli/src/main.rs:3454` | all-exports `linear_memory_bytes` `unwrap_or(0)` | as A31; the value feeds backends that now uniformly read 0 as zero bytes. |
| A35 | `synth-cli/src/main.rs:3464` | `memory_pages` slots `max().unwrap_or(0)` | 0 slots is the true count for no memories. |
| A36 | `synth-cli/src/main.rs:4072` | `rv_mem_size` `unwrap_or(0)` | instantiation-trap guard: with 0, ANY active segment bails loudly (correct: a segment cannot instantiate into a zero-byte memory). |
| A37 | `synth-cli/src/main.rs:4748–4878` | extent `max().unwrap_or(0)` folds | max-fold identities: each accumulator's 0 means "this source claims no extent", exactly its contribution. |
| A38 | `synth-cli/src/main.rs:7880` | metadata len `unwrap_or(0)` | println diagnostic on the link summary line. |
| A39 | `synth-cli/src/main.rs:8362–8576` | section data `unwrap_or_default()` | inspect/disasm path; unparseable section renders empty — diagnostic output only. |
| A40 | `synth-synthesis/src/instruction_selector.rs:5754` | `addr < linear_memory_bytes` statics gate | native-ABI only; at 0 NOTHING classifies as a static → base-relative path — correct for a zero-byte memory. |
| A41 | `synth-backend-riscv/src/selector.rs:3055` | `pages = bytes / 65536` | `(memory 0)` → `memory.size` = 0 pages — the spec answer. |

WCET note: `wcet.rs` / `wcet_loops.rs` / `wcet_compose.rs` / `wcet_recursion.rs`
carry NO numeric absence-sentinels — absence is modeled with enums
(`Bounded`/`LoopedExpansion`/decline reasons) and `Option` throughout; the two
`unwrap_or_default()` hits are empty hint-rejection collections. That design is
the target state this sweep converges the rest of the tree toward.

## Class (c) residuals — listed loudly, named follow-ups, NOT converted here

Ordered by blast radius. Each is safe today only because of another pass's
rule; none is silent — this table is the telling.

| # | Site | Collision | Today's guardian (the "wrong reason") | Follow-up |
|---|------|-----------|----------------------------------------|-----------|
| R1 | `main.rs:1812/3454`, `riscv backend.rs:75` | IMPORTED memory: `all_memories` holds only DEFINED memories, so `(import "env" "memory" (memory 1))` yields `linear_memory_bytes = 0` — and post-#953 every access compiles to a trap on rv32/aarch64 (software mode) for a module whose memory is REAL at runtime. Fail-closed, but a silent always-trap miscompile of a legitimate module — the "tell the caller" class. | wasm validation ("no memory ⇒ no memory ops") makes 0 honest for truly memoryless modules; imported memory breaks that argument. The decoder discards the imported min (`TypeRef::Memory(_) → ImportKind::Memory`), already named on #932. | Carry the imported minimum through the decoder (#932 follow-up), or refuse imported-memory modules loudly on self-contained paths. |
| R2 | `main.rs:5990` (cortex-m image) | `initial_pages.unwrap_or(1)` "backwards compat": a NO-memory module gets R10 = 65536 baked. | For defined-memory-less modules wasm validation forbids memory ops, so the invented page is unobservable — EXCEPT via an imported memory (R1), where R10 then lies about the size. | Fold into R1's resolution; delete the `unwrap_or(1)` once callers state sizes (the #953 contract applied to the image builder). |
| R3 | `main.rs:4712` | `emit_wasm_data = needs_wasm_data && linear_memory_bytes > 0`: a `(memory 0)` (or imported-memory) module whose code carries `__synth_wasm_data`/`__synth_globals` relocs gets NO region emitted → dangling symbol. | The final link fails loudly downstream (undefined symbol) — the right failure by the wrong actor, with the wrong message. | Emit the globals region independent of linmem size, or refuse at compile with a named reason. |
| R4 | `wasm_decoder.rs:941/1031/1399` | type-table `.get(ti).unwrap_or(0)` — an out-of-range type index yields arg/result count 0. | wasmparser validation rejects out-of-range type indices before these lines run. | Convert to a decode error (defense in depth against a validation-skipping caller). |
| R5 | `validator_pattern.rs:776` | `arity(op).unwrap_or(0)` — an op outside the supported surface seeds no inputs. | the caller dispatches only supported ops here; and a wrong arity under-constrains the EQUIVALENCE check, which can only FAIL spuriously (loud), never pass vacuously. | Return the `Option` and decline the op loudly. |
| R6 | `arm_backend.rs:127–129` | `params.cloned().unwrap_or_default()` — a driver that supplies no param tables gets "no i64/f32/f64 params", the #518 miscompile mechanism. | the CLI always populates the tables (post-#518/#599); only hand-built `Backend` API callers can omit them. | Make the tables non-optional in `CompileConfig` or decline i64/float-param functions when absent. |
| R7 | `provenance.rs:199`, `main.rs:3794` | `op_offsets.get(i).unwrap_or(0)` — a missing offset renders as offset 0 (= first op) in the provenance sidecar. | decoder emits `op_offsets` parallel to `ops`, so the index is always in range. | `Option` through the sidecar schema; diagnostic-only blast radius. |
| R8 | `elf_builder.rs:723` | `name_offsets.get(i).unwrap_or(0)` — a missing name renders as the null strtab entry (empty section name). | the two vectors are built in the same loop, same length. | zip the vectors so the invariant is structural. |
| R9 | `solver.rs` deadline / `translation_validator.rs:552` | not sentinels (exact-arithmetic guards); listed here only because the grep surfaced them — no absence encoding present. | — | none needed. |

## Red-first evidence (pre-fix probes, v0.56.1 tree, 2026-08-13)

```
$ synth compile mem0.wat --all-exports --safety-bounds mask ; echo $?
0                                   # accepted — C1 hole open
$ synth disasm mem0_mask.elf | grep r10
movw r10, #0x0                      # zero size baked; SUB R12,R10,#1 = identity mask

$ synth compile mem1.wat -b riscv --func-index 0 --safety-bounds software
$ synth disasm mem1_rv.o            # first words:
00050293 00100073                   # addi t0,a0,0 ; ebreak — every access traps (C2)

# post-fix: 00010337 ffc30313 ...   # lui t1,0x10 ; addi t1,t1,-4 = the real 65532 bound
# control: (memory 0) keeps 00100073 and gains no bound — #953 fail-closed preserved
```
