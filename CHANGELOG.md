# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.11.14] - 2026-05-31

**Three control-flow miscompiles in the direct selector — fixes the binary
semaphore's WAKE path (#204 follow-up).** After v0.11.13 fixed the no-waiter
*increment* path on hardware (gale confirmed `sem->count` now oscillates
0→1→0), the *waiter* (WAKE) path still couldn't be exercised on silicon — the
debugger perturbs the give/take race (a true heisenbug). A wasmtime-oracle vs
unicorn differential harness (`scripts/repro/wake_path_differential.py`) drove
`z_impl_k_sem_give` with a non-empty wait_q and pinned three independent bugs,
all in the `--relocatable` direct-selector path, that combined to make the give
always increment and never wake:

1. **The decoder silently dropped `br_table`.** `convert_operator` had no arm
   for it, so the multi-way dispatch vanished and control fell straight into
   table arm 0 — `has_waiter` never selected the WAKE branch. Now decoded with
   its target list + default preserved.
2. **`select` clobbered its own condition flags.** The lowering emitted
   `CMP cond,#0; MOV dst,val1; cond-move` — the middle `MOV` is a 16-bit Thumb
   `MOVS` (flag-setting) for low registers, destroying the `CMP` result before
   the conditional move read it (so the select returned the wrong arm under
   register pressure). Reordered to `CMP` immediately followed by two
   flag-preserving `IT;MOV` conditional moves; correct under any register
   aliasing.
3. **`SetCond` corrupted a high-register result.** It materialized 0/1 with the
   16-bit `MOVS Rd,#imm` (T1), whose Rd field is 3 bits (R0–R7); for a high Rd
   (R8–R12) the register bits overflowed the opcode, turning `MOVS` into `CMP`,
   so the comparison result was never written. `has_waiter` (allocated to R12)
   stayed stale. High Rd now uses the 32-bit `MOV.W` (T2).

End-to-end: synth's `z_impl_k_sem_give` now matches the WASM semantics on **both**
paths (no-waiter → `count=1`, no wake; waiter → `count=0`, `z_ready_thread`
called with the unpended thread) under unicorn emulation of gale's gist on the
cortex-m4 (Thumb-2) build. Regression tests: `test_decode_br_table` (synth-core),
`test_encode_setcond_high_reg_uses_mov_w_204` (synth-backend, verify-bytes).

_Falsification:_ this release is wrong if, for a Cortex-M (Thumb-2) target, a
`br_table` fails to dispatch on its index, or a `select`/comparison whose result
lands in R8–R12 reads back a value other than the materialized 0/1.

## [0.11.13] - 2026-05-31

**i64 width-conversion decode + i32/i64-aware spilling + param frame-backing —
fixes the binary-semaphore give (#204).** gale's loom-inlined
`z_impl_k_sem_give` ran on real Cortex-M4 hardware (NUCLEO-G474RE) without
faulting (after #202) but `sem->count` stayed 0 on a no-waiter give — a hardware
watchpoint on `&sem->count` showed the give's store **never fired it**. Three
compounding root causes, all now fixed:

1. **The decoder silently dropped `i64.extend_i32_u`, `i64.extend_i32_s` and
   `i32.wrap_i64`** — `convert_operator` had no arm for them, so they vanished
   from the op stream. gale's `(new_count << 32)` pack is
   `local.get N; i64.extend_i32_u; i64.const 32; i64.shl`; with the extend gone,
   an i32 value was left as a 64-bit operand with a garbage high half. Now
   mapped to `WasmOp::I64ExtendI32U/S` and `I32WrapI64`.
2. **`select_with_stack` spilled every register-resident stack value as an
   8-byte i64 pair (latent #171).** `StackVal::Reg` carried no width, so
   `spill_deepest_reg`/`stack_live_regs` called `i64_pair_hi` on i32 temps —
   failing for an i32 in R12 (no consecutive hi), exhausting the allocator on
   gale's pack ("no high register available for R12"). `StackVal` now tracks
   i32-vs-i64 width and spills 4 vs 8 bytes accordingly.
3. **A param used as a store address and live across a call was clobbered
   (#193 class).** `local.get 0` (the semaphore pointer) lives in R0; the
   intervening `k_spin_lock(1024)` reclaims R0 for its AAPCS argument before the
   store reads it. Call-containing functions now **frame-back every in-register
   param** (spill at entry, reload through a stack slot), so the store's address
   index survives the call. The give now lowers to
   `str.w r_val, [r11, r_semptr]` (Thumb-2), writing `new_count` to the real
   `&sem->count`. Call-free functions keep params register-backed (no behaviour
   change; call-free temp clobbers remain the separate, non-blocking #193 fuzz
   class).

End-to-end verified by unicorn emulation of gale's gist on the **cortex-m4
(Thumb-2)** build — the no-waiter give now sets `sem->count = 1` — plus decoder
and selector regression tests.

_Falsification:_ this release is wrong if, for a Cortex-M (Thumb-2) target, a
WASM `iN.store*` whose address operand is a parameter held live across a call
emits a base-only `[r11, #off]` store (dropping the register index) instead of
the indexed `[r11, r_addr, #off]` — i.e. if the store can no longer reach a
runtime-computed linear-memory address after an intervening call.

## [0.11.12] - 2026-05-31

**Byte-accurate local branch resolution — fixes mid-instruction branch targets
(#202).** gale's `z_impl` faulted on real Cortex-M4 hardware (NUCLEO-G474RE): a
`bne.n` conditional branch landed in the *middle* of the following 32-bit
Thumb-2 instruction, so taking the branch executed from mid-instruction →
UsageFault (stacked fault PC == the bad target). Root cause: `select_with_stack`
emits `if`/`else`/`block`/`loop` branches as label placeholders (`Bcc`/`B`/`Bhs`/
`Blo` + `Label`) but nothing ever resolved them — the encoder emitted `bne.n #0`
placeholders. The only resolver (`control_flow::resolve_branches`) was dead *and*
counted instruction indices rather than bytes. Before #197 this path only ran for
`--no-optimize`/declined functions, so the bug stayed latent; routing relocatable
code through `select_with_stack` surfaced branches that skip a 32-bit instruction
(an `ldr.w` spill-reload, a `movw`/`movt` constant, …). New `resolve_label_branches`
pass in the backend encodes each instruction to learn its real byte length (16-
vs 32-bit and multi-instruction expansions are exact), maps each `Label` to its
byte position, and rewrites every local label branch to the displacement the
encoder consumes — `(target − branch − 4) / 2` halfwords — with a bounded
fixed-point for the case where an offset grows a branch 16→32-bit. External
labels (`Trap_Handler`, resolved by relocation) and the optimized path's inline
`BCondOffset` are left untouched. An `if` over a 32-bit `movw`/`movt` now emits
`beq 0x12` (else boundary) instead of `beq 0x0a` (mid-`movw`).

_Falsification:_ this release is wrong if any conditional or unconditional Thumb
branch in synth `.text` targets an address that is not an instruction boundary —
i.e. if hand-decoding the halfword stream shows a `B<cond>`/`B.N` whose
`(addr + 4 + 2·imm)` lands on the second halfword of a 32-bit instruction.

## [0.11.11] - 2026-05-30

**Relocatable host-link correctness — fp-relative memory + caller-saved
preservation across imports (#197).** gale's `z_impl_k_sem_give` miscompiled on
the optimized path: a pointer param live across an import call (`k_spin_lock`)
was read from a fixed absolute base (`0x20000100 + clobbered-r0`) instead of
`[fp, sem]`. Two root causes, both specific to the optimized path and both only
wrong for relocatable output: (1) the optimized `Call` lowering does not
preserve caller-saved registers across a `BL`, and (2) `MemLoad`/`MemStore`
materialize an absolute SRAM base (`0x20000100`) — valid for a bare-metal
`ET_EXEC` at a known address, but wrong for a host-linked `ET_REL` where the host
supplies the linear-memory base in `fp` (R11) at runtime. Fix: `--relocatable`
now routes to the direct selector (`select_with_stack`), which preserves
caller-saved registers (#188), marshals AAPCS args (#195), spills i64 pairs under
pressure (#171), and addresses memory fp-relative. Imports in relocatable mode
emit a direct `BL func_N` (rewritten to the wasm field name, e.g. `k_spin_lock`,
by `build_relocatable_elf`) instead of `__meld_dispatch_import`. The optimized
path and its Meld-dispatch import ABI are unchanged for non-relocatable output.
gale's shape now lowers to `str.w r0,[sp]; bl k_spin_lock; ldr.w r0,[sp]; ldr.w
r0,[fp,r0]` with an `R_ARM_THM_CALL k_spin_lock` relocation. Follow-up tracked
separately: an fp-aware optimized path so relocatable builds can be optimized too.

_Falsification:_ this release is wrong if a `--relocatable` object with a pointer
param live across an import call still reads that param from an absolute base or a
call-clobbered register — i.e. if `arm-*-objdump -dr` on the `.text` shows a
`MOVT ip,#0x2000` feeding the dereference, or the param's home register is neither
spilled across the `BL` nor callee-saved.

## [0.11.10] - 2026-05-30

**i64 register-pair spill (#171).** i64-heavy functions that kept more i64 values
live than the five consecutive register pairs hold hit "no consecutive pair"
exhaustion and were dropped by the #168 skip-and-continue net — and #188's
caller-saved preservation added pressure that regressed `z_impl_k_sem_give` from
compiling (v0.11.6) to skipped (v0.11.8). The selector now spills: the operand
stack carries `Reg | Spilled` entries, `alloc_consecutive_pair` spills the
deepest register-resident value to a reserved frame slot when no pair is free
(reloading it on pop), the call-result park spills when no callee-saved register
is free, and the arg-move cycle scratch is acquired lazily. i64-heavy functions
and the i64+calls `z_impl` shape now compile instead of being skipped.

**Falsification statement.** v0.11.10 is wrong if a function with six or more
simultaneously-live i64 values fails to compile with a register-exhaustion error
instead of spilling.


## [0.11.9] - 2026-05-30

**Call argument marshalling (#195).** `select_with_stack`'s `Call` lowering
emitted `BL` + `push(R0)` but never moved the call's stack arguments into r0–r3,
so a call with arguments ran the callee with garbage (gale: "lock addr in r5,
not passed in r0" — the last blocker for `z_impl_k_sem_give`). Callee argument
counts are now plumbed frontend→backend→selector (from the Type/Function
sections); `Call`/`CallIndirect` pop the top-N operand-stack values as arguments
*before* the #188 caller-saved preservation (so they're excluded from the spill
set) and emit a cycle-safe parallel move into r0..r(N-1) as the last writes
before the `BL`. Verified end-to-end with #188: `(call $use (i32.const 42))` now
emits `mov r0, #42` before the `bl`, with the live param preserved across the
call. Together with v0.11.8 (#188) this makes a value-live-across-a-call-with-args
pattern — gale's `z_impl_k_sem_give` shape — compile correctly.

Scoped out: i64/f64 arguments counted as one slot (gale uses i32/pointer args),
`>4` arguments (5th+ stack-passed) not yet emitted, and import-call marshalling
(the Meld dispatch ABI uses r0 for the import index — separate). The broader
no-call param-register clobber class remains #193.

**Falsification statement.** v0.11.9 is wrong if a call with i32 arguments
(≤4) invokes the callee without those arguments in r0–r3, or if marshalling
clobbers a caller-saved value the #188 preservation was meant to save.


## [0.11.8] - 2026-05-30

**Caller-saved register preservation across calls (#188).** gale-confirmed
miscompile: a value (param or temp) live across a `call` was corrupted. The
selector maps params to r0–r3 and allocates r0–r3/r12 (AAPCS caller-saved) as
temps, but the `Call` lowering modeled nothing about the `BL` clobbering them —
so `g`: `drop(call $clob); i32.load(local.get 0)` read param0 from r0 *after*
`clob` overwrote it (blocking gale's `z_impl_k_sem_give`, whose `sem` pointer is
live across `k_spin_lock`). Now the direct selector spills live caller-saved
registers to a reserved frame scratch area before each `BL` and reloads them
after; the optimized path declines functions containing a local call so the
backend re-lowers them with the corrected direct selector (import calls stay on
the optimized path to preserve the #173 field-name relocations). Verified: `g`
now emits `str r0,[sp]; bl; ldr r0,[sp]; ldr r0,[fp,r0]` — the load derives from
the original param0.

Scoped out (tracked in #193): the broader no-call subset of the param-register
clobber class (i64 results / constants / return values landing in r0–r3 before a
live param read), and general argument marshalling for calls with register args.

**Falsification statement.** v0.11.8 is wrong if a value live across a `call`
(e.g. a pointer param dereferenced after a call) is read from a caller-saved
register the call clobbered rather than from its preserved home.

## [0.11.7] - 2026-05-30

**Standalone `--cortex-m` internal call resolution (#170).** A standalone
(non-`--relocatable`) `--cortex-m` build of a module with an internal `call` was
silently routed to the relocatable-object builder (every internal BL records a
relocation since #167), producing an `ET_REL` object with an unresolved
`R_ARM_THM_CALL` and a `bl #0` placeholder — which, with no linker, stayed
garbage. Now internal-only modules build a standalone `ET_EXEC` and each internal
`BL func_N` is patched in place to the callee entry after layout. The Thumb BL
encoding (`target − (P+4)`, J1/J2 from the sign bit) is verified byte-for-byte
against `arm-none-eabi-as`. The `$t`/`$a`/`$d` mapping-symbol half of #170 is
deferred (needs an ElfBuilder symtab-ordering rework).

**Falsification statement.** v0.11.7 is wrong if a standalone `--cortex-m`
internal `BL func_N` resolves to anything other than the callee's entry address
(e.g. callee+4, or an unpatched `f7ff fffe` placeholder).

## [0.11.6] - 2026-05-30

**Patch: encoder is now total under fuzzing (#186).** The `encoder_no_panic`
fuzz target (which runs with an empty corpus) intermittently found pre-existing
panics, making the Fuzz Smoke gate flaky. The remaining root — after the
PC/R15-operand fix in v0.11.4 (#185) — was arithmetic overflow in the ARM32
branch encoders: `*offset - 2` overflow-panics at `i32::MIN` under
`-Cdebug-assertions`. Now uses `wrapping_sub` (total; identical for any real
branch offset). A 180s sweep then ran **8.8M executions with zero panics**.
Also adds a committed `fuzz/seed_corpus/encoder_no_panic/` (61 inputs) so CI's
60s run starts with coverage rather than exploring cold. The separate
`i64_lowering` fuzz finding (real clobber vs harness false-positive) is tracked
in #188.

**Falsification statement.** v0.11.6 is wrong if `encoder_no_panic` panics on
any input (the encoder must return Ok or Err, never abort).

## [0.11.5] - 2026-05-30

**Patch: high-register Thumb CMN (#184).** Closes the last sibling of the #180
16-bit-truncation class. The 16-bit `CMN` (T1) reg-form encodes only R0–R7;
high-register operands overflowed the 3-bit fields. CMN has no high-register
16-bit form, so high registers now use 32-bit `CMN.W` (`EB10 Rn | 0F00 Rm`),
byte-verified against `gas`. Latent (the optimized divide-guard uses the CMN
*immediate* form; the reg-form is only emitted by the non-optimized selector
with low registers) — closed as defense-in-depth.

**Falsification statement.** v0.11.5 is wrong if `encode(Cmn { rn, op2: Reg(rm) })`
emits a 16-bit instruction when `rn` or `rm` is ≥ R8 (truncating the operand).

## [0.11.4] - 2026-05-30

**Patch: root-cause + re-enable the optimized memory path (#180).** The
optimizer memory miscompilation mitigated in v0.11.3 (by declining linear-memory
ops to `select_with_stack`) is now fixed at its true source — the Thumb
*encoder*, not the optimizer. `ArmOp::Add`/`Adds`/`Subs` register-forms
unconditionally emitted the 16-bit encoding, whose 3-bit register fields
overflow for high registers; since `MemLoad`/`MemStore` use R12 as the base
scratch, `add ip, ip, r0` was emitted as the corrupt `adds r4, r5, r1`
(`0x186C`), dropping the address operand. (i64 low-word `Adds`/`Subs` hit the
same class via R8–R11 pairs.) High registers now use the 32-bit
`ADD.W`/`ADDS.W`/`SUBS.W` forms. The v0.11.3 decline is removed; the optimized
linear-memory path is re-enabled and the four `issue_104` memory CSE tests are
un-ignored. Byte-verified against `--no-optimize` (clean-room confirmed).

**Falsification statement.** v0.11.4 is wrong if any optimized Thumb output
contains a 16-bit `add`/`adds`/`subs` register encoding with an operand ≥ R8
(which truncates the operand), or if an optimized pointer-param
`i32.load`/`i32.store` produces an effective address that does not depend on the
pointer operand register.

## [0.11.3] - 2026-05-30

**Patch: optimizer memory-address miscompilation.** Fixes a correctness bug
where the optimized (default) path dereferenced the wrong memory location.

**Falsification statement.** v0.11.3 is wrong if the optimized path still
emits a fixed-address load/store for a pointer-param (or constant) memory
access, or if optimized and `--no-optimize` output differ for a
pointer-deref function.

### Fixed
- **Optimized path no longer miscompiles linear-memory addresses** (#178,
  PR #179). The optimized `wasm_to_ir → ir_to_arm` lowering dropped the
  `i32.load`/`i32.store` address operand (the `ADD base, base, Raddr` came out
  with garbage registers), so the access hit a fixed address
  (`linmem_base + 0x100`) regardless of the operand — for both a dynamic
  pointer-param address and a constant one. `optimize_full` now declines
  modules using linear-memory load/store and falls back to the correct
  `select_with_stack` path (`ldr [fp, Raddr]`). Verified: optimized
  pointer-deref output now byte-matches `--no-optimize`. Guarded by
  `pointer_deref_optimized_matches_no_optimize_178`.

  Trade-off: memory-using modules compile correctly but unoptimized until the
  optimized memory path is repaired (#180). The host-ABI / `__linear_memory_base`
  contract raised alongside this is tracked in #181.

## [0.11.2] - 2026-05-30

**Patch: gale-wasm ARM linkability, round 2.** Completes the cross-language-LTO
route (gale-ffi → wasm → synth → ARM `ET_REL` → linked against a real host).
Backend bugfix + regression tests; no proof-suite changes.

**Falsification statement.** v0.11.2 is wrong if an imported wasm call still
produces a generic `func_N` undefined symbol instead of the import's field
name, if a linked call lands at `symbol+4` instead of `symbol`, or if any of
the new regression tests pass against the pre-fix code.

### Fixed
- **Calls land on the callee entry, not `symbol+4`** (#174, PR #177). After
  the #167 fix the Thumb BL placeholder was `0xF800` (addend 0), which under
  `R_ARM_THM_CALL` nets to `S+4` — every call branched one instruction-pair
  *past* the callee entry (links cleanly, runs wrong). The correct relocatable
  placeholder is what `gas` emits for `bl <extern>`: `f7ff fffe`
  (`hw1=0xF7FF, hw2=0xFFFE`), carrying a `-4` addend that nets to exactly `S`.
  Verified: `mini.o` links and `caller`'s `bl` lands on `callee` (0x8000), not
  0x8004. Guarded by `test_encode_thumb_bl_placeholder_addend_167_174` and an
  end-to-end `.text` placeholder check.
- **Import-call relocations now use the wasm field name** (#173, PR #175).
  The selector emits `BL func_{wasm_index}` for imported calls too (an import's
  wasm index < num_imports), so `build_relocatable_elf` named the undefined
  symbol `func_0`/`func_1`/… A real host (e.g. the Zephyr kernel) defines
  `k_spin_lock`, not `func_0`, so the object could not resolve — the final
  blocker for the cross-language-LTO route. `build_relocatable_elf` now maps
  `func_{import_index}` relocation labels to the import's field name (from the
  imports table it already receives). Internal defined calls keep their
  `func_N`/export-name symbol; `__meld_*` dispatch stubs unchanged. Verified:
  a module importing `env::host_fn` now emits `R_ARM_THM_CALL host_fn` and
  `U host_fn` (was `U func_0`).

### Added
- **Regression tests for the #167/#168/#173 gale linkability fixes.** The
  v0.3.0→v0.11.0 non-linkable-ELF regression slipped through because nothing
  tested internal-call linkability. Now guarded:
  - `test_encode_thumb_bl_zero_offset_167` — the Thumb BL placeholder must
    encode `0xF800` (true zero offset), never `0xD000` (the ~`+0x600000`
    garbage addend).
  - `test_compile_internal_call_produces_relocation_167` — an internal call
    records a relocation against `func_{index}`.
  - `compile_internal_call_is_linkable_167` (integration) — a relocatable
    object carries `R_ARM_THM_CALL` against a defined `func_0`, end-to-end.
  - `compile_import_call_uses_field_name_173` (integration) — an import call
    produces `U host_fn`, not `U func_0`.

  Adds the `object` crate as a synth-cli dev-dependency for ELF inspection.

## [0.11.1] - 2026-05-30

**Patch: gale-wasm ARM linkability.** Unblocks the cross-language-LTO route
(gale-ffi → wasm → synth → ARM `ET_REL` → linked into a Zephyr build). No
proof-suite changes; the v0.12 control-flow-model verification work is
separate and unaffected.

**Falsification statement.** v0.11.1 is wrong if a WASM module containing an
internal function call still compiles to an ARM object that fails to link
(no `R_ARM_THM_CALL` for the call, or a non-zero built-in BL addend), or if
`--all-exports` still aborts the whole module on a single un-compilable
function.

### Fixed
- **Internal calls are now linkable** (#167, PR #169). Every synth ARM object
  containing a function call was non-linkable (a regression from v0.3.0).
  Three chained defects:
  1. `arm_backend.rs` recorded a relocation only for `BL __meld_*` (import
     dispatch); internal `BL func_N` got none, so they were emitted as bare
     `bl #0` with nothing to patch. Now records a relocation for every `BL`.
  2. `build_relocatable_elf` defined only export-name symbols and used
     `R_ARM_CALL` (ARM mode). Now defines a `func_{index}` symbol per function
     and emits `R_ARM_THM_CALL` (Thumb).
  3. The Thumb BL placeholder encoded second halfword `0xD000`, which
     (`J1=J2=0, S=0` ⟹ `I1=I2=1`) bakes in a bogus ~`+0x600000` addend — the
     source of the garbage `bl c0000c` target *and* the linker
     "relocation truncated to fit". A true zero-offset Thumb BL is `0xF800`.

     Verified on a minimal 2-internal-call module: the `.o` now carries
     `R_ARM_THM_CALL → func_0`, links with `arm-none-eabi-ld` with zero
     errors, and the call resolves to the callee.
- **`--all-exports` no longer aborts on one un-compilable function** (#168,
  PR #169). A function the backend cannot compile (e.g.
  `compiler_builtins::float::div`, which exhausts the i64 register-pair
  allocator) is now skipped with a diagnostic and an end-of-run report; a
  caller that references it gets a clean `undefined symbol func_N` link error.
  Erroring only if every function fails.

### Known follow-ups (not blocking the gale `--relocatable` route)
- Standalone `--cortex-m` (no linker) internal-call direct resolution + `$t`
  mapping symbols (#170).
- i64 consecutive-pair allocator spill / coalescing — the root of #168 (#171).

## [0.11.0] - 2026-05-29

**Theme: true i64 T1 result-correspondence parity.**

v0.11.0 closes the final three i64 bitwise admits (`i64_and_correct`,
`i64_or_correct`, `i64_xor_correct`), completing i64 T1 parity with i32:
**40 i64 T1 Qed, 0 i64 admits.** Tree-wide admits drop 12 → 9. All proofs
authored and verified against the local Nix/Bazel Rocq checker before
push (`bazel build //coq:verify_proofs` green); clean-room verified
(5/5 claims: genuinely Qed, no statement weakening, zero new axioms,
Qed-backed helpers, admit accounting matches).

**Falsification statement.** v0.11.0 is wrong if (a) any of
`i64_and/or/xor_correct` is not `Qed` (Admitted/Abort/admit), (b) any of
the three theorem statements was weakened from its v0.10.0 `Admitted`
form (each must still assert `exec_program … = Some astate'` plus BOTH
`get_reg astate' R0 = lo_of_i64 (…)` and `get_reg astate' R1 = hi_of_i64 (…)`),
(c) a new `Axiom` was introduced anywhere under `coq/` (grep: zero), or
(d) `bazel test //coq:verify_proofs` goes red on a clean v0.11.0 checkout.

### Added
- **i64 bitwise T1 result-correspondence** (PR #164, closes #163).
  `i64_and_correct` / `i64_or_correct` / `i64_xor_correct` discharged.
  AND/ORR/EOR compile to two flag-free register ops
  (`[_ R0 R0 R2; _ R1 R1 R3]`); the proof is the `i64_add_correct`
  template minus flag-peeling — step `exec_program` over the pair, route
  R0/R1 via `get_set_reg_{eq,neq}`, apply the combine lemmas.
- **Bitwise combine + slice helpers** (PR #164, all Qed, no axioms):
  `div32_mod64` (`(a mod 2^64)/2^32 = (a/2^32) mod 2^32`, bit
  extensionality via `Z.div_pow2_bits` + `Z.mod_pow2_bits_{low,high}`),
  `and_hi_combine`, and the `or_lo/or_hi/xor_lo/xor_hi_combine`
  analogues. Complete the infrastructure begun in v0.10.0
  (`{land,lor,lxor}_{low,high}32`, `combine_lo32/hi32`, `and_lo_combine`).

## [0.10.0] - 2026-05-29

**Theme: i64 add/sub T1 + Rocq 9 Z.mod_mod wrap closed + bitwise lift infrastructure.**

v0.10.0 closes the two carry/borrow i64 admits and the long-standing
`Z.mod_mod` blocker, and lands the infrastructure for the remaining
bitwise T1 lifts. All proofs verified against the local Nix/Bazel Rocq
toolchain (`bazel build //coq:verify_proofs` green) before each push —
this session established that synth's Rocq proofs can be checked locally,
ending the blind-CI-round-trip pattern.

**Falsification statement.** v0.10.0 is wrong if (a) any newly-Qed lemma
is actually `Admitted`/`Abort` (grep confirms the claimed Qeds compile),
(b) `bazel test //coq:verify_proofs` goes red on a clean v0.10.0 checkout,
(c) a new `Axiom` was introduced (grep confirms zero), or (d) the stated
admit count (12) does not match the tree.

### Added
- **i64 add/sub T1 result-correspondence** (PR #160). `i64_add_correct`
  and `i64_sub_correct` (Admitted in v0.9.0) are now Qed, via new
  ADDS/ADC carry-propagation and SUBS/SBC borrow-propagation lemmas in
  `coq/Synth/ARM/ArmFlagLemmas.v` (`i64_add_via_adds_adc`,
  `i64_sub_via_subs_sbc`, `carry_split_add`, `borrow_split_sub`). The
  discharge steps `exec_program` over the real `[ADDS; ADC]` / `[SUBS; SBC]`
  pairs, reading the C flag set by the low-half instruction. No new axioms.
- **Bitwise halves-distribute infrastructure** (PR #161). Six pure-Z
  distribution lemmas (`{land,lor,lxor}_low32` via `Z.land_ones` + bit
  extensionality; `{land,lor,lxor}_high32` via `Z.shiftr_{land,lor,lxor}`),
  plus `combine_i32_raw`, `mod64_mod32`, `combine_lo32`, `combine_hi32`,
  and `and_lo_combine` — all in `coq/Synth/Synth/CorrectnessI64.v`, all
  Qed, no axioms.

### Fixed
- **`i64_to_i32_to_i64_wrap` closed** (PR #161). The long-standing Rocq 9
  `Z.mod_mod` Admit in `coq/Synth/Common/Integers.v` is now Qed via a
  canonical symbolic-atom modular proof (keeps moduli as atoms so `lia`
  avoids 2^64-scale literal certificates; `rewrite !Z.mod_small` clears the
  double `mod 2^64` introduced by `I64.repr` + `I64.unsigned`).

### Deferred to v0.11.0
- `i64_and_correct` / `i64_or_correct` / `i64_xor_correct` remain Admitted
  (3 of the 12 total admits). The remaining work is the high-half combine
  helper (`(Z.land X Y mod 2^64) / 2^32 mod 2^32`, via `ZDivEucl.mod_mul_r`),
  the or/xor analogues of `and_lo_combine`, and the three theorem
  exec-proofs (template: `i64_add_correct` minus flag handling). The
  infrastructure to close them shipped in this release.

## [0.9.0] - 2026-05-27

**Theme: i64 T1 result-correspondence lifts against the aligned model.**

v0.9.0 picks up what v0.8.0 set up. v0.8.0 (the "honest foundation") aligned
`Compilation.v` with the real Rust codegen and shipped 26 type-only pseudo-op
axioms + tactics + flag-correspondence lemmas. v0.9.0 layers the value-correspondence
on top: 26 new `_spec` axioms equate every i64 pseudo-op's result to the WASM-spec
function, then 30 existence-only (T2) i64 proofs are lifted to result-correspondence
(T1), and the 5 strategically-`Admitted` theorems #150 carried over are discharged.

**Net delta:** previously had 36 i64 theorems Qed at T2 plus 5 admits.
Now has **30 new T1 Qeds + 5 discharged T1 Qeds = 35 i64 T1 Qeds**, with 5 honest
admit carry-overs (Add/Sub/And/Or/Xor) whose proofs depend on missing helper
lemmas (ADDS/ADC carry-propagation; SUBS/SBC borrow-propagation; halves-distribute
over bitwise, blocked by Rocq 9 `Z.mod_mod`).

**Falsification statement.** v0.9.0 is wrong if (a) any of the 35 newly-T1 i64
theorems is shown to disagree with the WASM reference for a value pair the
theorem covers (the `_spec` axioms are inconsistent with `Compilation.v`),
(b) any of the 5 honest-Admitted carry-overs is claimed `Qed.` anywhere in the
release artifacts, (c) `bazel test //coq:verify_proofs` goes red on a clean
v0.9.0 checkout, or (d) any newly-added `_spec` axiom claims a result the Rust
codegen does not actually produce (cross-checked against `docs/analysis/I64_CODEGEN_SURVEY.md`).

### Added

- **i64 pseudo-op result-correspondence axioms (v0.9.0 PR 1 precursor).**
  `coq/Synth/ARM/ArmSemantics.v` gains 26 new `_spec` axioms that pin the
  axiomatic i64 pseudo-op result functions (`i64_const_lo`, `i64_divs_pair`,
  `i64_mul_lo_bits`, etc., introduced as opaque types by v0.8.0 #150) to the
  WASM-spec operation on the combined 64-bit operand pair via the new
  `combine_i32 / lo_of_i64 / hi_of_i64` helpers in `Common/Integers.v`. Each
  axiom is cross-referenced to `docs/analysis/I64_CODEGEN_SURVEY.md` and to
  the `instruction_selector.rs` line numbers that emit the pseudo-op. This
  layer was the missing precursor blocking PRs 2-5 of umbrella #152.
- **5 i64 T1 admit discharges (v0.9.0 PR 1).** `i64_const_correct` in
  `CorrectnessSimple.v` and `i64_{divs,divu,rems,remu}_correct` in
  `CorrectnessI64.v` are now `Qed` via the new spec axioms. Each theorem is
  restated with dual-register hypotheses and dual-register post-conditions
  (R0 = lo_of_i64 result, R1 = hi_of_i64 result), reflecting that an i64
  result spans both halves of the (R0, R1) register pair.
- `I64.rems` and `I64.remu` definitions in `Common/Integers.v` to provide a
  WASM-spec target for the new `i64_rems_pair_spec` / `i64_remu_pair_spec`
  axioms (previously only `I64.divs` and `I64.divu` were defined).

## [0.8.0] - 2026-05-26

**Theme: honest i64 verification foundation.**

v0.8.0 was originally scoped as "i64 T1 result-correspondence parity"
(umbrella issue #147). A clean-room check of the first foundation PR
(#149) surfaced that `coq/Synth/Synth/Compilation.v` modeled i64 ops
as single 32-bit ARM instructions (e.g., `I64Add → [ADD R0 R0 R1]`,
inline comment: *"Simplified: just add low 32 bits"*) while the real
Rust compiler at `crates/synth-synthesis/src/instruction_selector.rs:1450`
emits proper register-pair sequences (`ADDS R0,R0,R2; ADC R1,R1,R3`).
The umbrella's own falsification clause forbade shipping T1 proofs
that "prove a different operation than the compiler emits."

Rather than overclaim or paper over the gap, v0.8.0 ships the
**aligned model + proof tooling** layer, and the actual T2→T1
promotions become v0.9.0's theme. This is a smaller user-visible
delta but a much bigger verification-soundness delta: the existing
i64 proofs now reason about the operation the compiler actually
emits, instead of a degenerate 32-bit slice of it.

**Falsification statement.** v0.8.0 is wrong if (a) the aligned
`Compilation.v` clauses do not match what the Rust compiler emits
(cross-checked against the per-op survey in
[`docs/analysis/I64_CODEGEN_SURVEY.md`](docs/analysis/I64_CODEGEN_SURVEY.md)),
(b) `bazel test //coq:verify_proofs` goes red on a clean v0.8.0
checkout, or (c) any of the 5 strategically-`Admitted` i64 theorems
(4 div/rem + 1 i64_const) are claimed to be Qed anywhere in the
release artifacts.

### Changed
- **`coq/Synth/Synth/Compilation.v` aligned with real Rust i64 codegen** (PR #150).
  28 i64 op clauses updated: I64Add/Sub now emit `ADDS R0,R0,R2; ADC R1,R1,R3`
  (and SUBS/SBC); I64And/Or/Xor emit parallel lo/hi binops; i64 comparison ops
  emit a single `I64SetCond[Z]` pseudo-op; div/rem/mul/shifts/rotates/bit-manip
  emit ArmOp::I64* pseudo-ops mirroring the Rust ArmOp variants. ArmSemantics.v
  gains the real ADDS/ADC/SUBS/SBC instructions plus ~25 axiomatized result
  functions for the pseudo-ops (parallel to how VFP is axiomatized).
  Per-op cross-check against the Rust source is documented in
  [`docs/analysis/I64_CODEGEN_SURVEY.md`](docs/analysis/I64_CODEGEN_SURVEY.md).
- ~36 existence-only (T2) i64 proofs re-proved against the aligned model
  using the existing `solve_single_arm` / `solve_cmp_mov` / `solve_mem_single`
  tactics. **Net: previously had 29 i64 theorems Qed against a model that
  proved the wrong operation; now has 36 i64 theorems Qed against the
  correct model, plus 5 strategically-Admitted theorems pending the
  v0.9.0 lift queue.**

### Added
- **Proof tooling for i64 T1 lifts** (PR #149). Three new tactics in
  `coq/Synth/Synth/Tactics.v`: `synth_binop_proof_i64`,
  `synth_cmp_binop_proof_i64`, and `synth_cmp_unop_proof_i64`. Eleven
  new i64 flag-correspondence lemmas in `coq/Synth/ARM/ArmFlagLemmas.v`
  (`z_flag_sub_eq_i64`, `flags_ne_i64`, `nv_flag_sub_lts_i64`,
  `flags_ltu_i64`, `flags_ges_i64`, `flags_geu_i64`, `flags_gts_i64`,
  `flags_gtu_i64`, `flags_les_i64`, `flags_leu_i64`,
  `z_flag_sub_eqz_i64`), plus 14 supporting boundedness helpers. All
  proofs Qed; 0 Admitted in #149's diff. These are the infrastructure
  the v0.9.0 lift PRs will consume.

### Documentation
- **Architectural finding: ARMv7-M FPv5 has no F64↔I64 VCVT** (PR #148).
  The four WASM ops `F64ConvertI64S/U` and `I64TruncF64S/U` listed under
  v0.7.0's "Deferred to follow-up" cannot be implemented as
  single-instruction VCVTs on Cortex-M7DP — the 64-bit integer ↔
  floating-point VCVT encodings are ARMv8-A FEAT_FP only, not present
  in M-profile FPv5-D16. Closing these requires a multi-instruction
  software sequence plus WASM-trap integration plus matching Rocq
  proofs — deferred to a later floating-point milestone. Full analysis
  in [`docs/analysis/ARMV7M_F64_I64_VCVT_FINDING.md`](docs/analysis/ARMV7M_F64_I64_VCVT_FINDING.md).
  Selector continues to surface a typed `Error::Synthesis`; no
  behavior change vs. v0.7.0.
- **I64 codegen survey** at [`docs/analysis/I64_CODEGEN_SURVEY.md`](docs/analysis/I64_CODEGEN_SURVEY.md):
  per-op extraction of what the Rust compiler emits for every i64 WASM
  op, with line citations into `instruction_selector.rs`. Reviewers
  audit Compilation.v against the Rust source mechanically using this
  file.

### Fixed
- **Bazel rocq_library dep wiring**. `rules_rocq_rust` requires every
  `Require Import Synth.X.Y.` in a `.v` file to be matched by a
  corresponding `:y` target in the library's `deps` list — transitive
  deps through intermediate targets do **not** propagate the `-Q`
  flags to `coqc`. Synth's `:arm_instructions`, `:arm_semantics`,
  `:compilation`, `:tactics`, and `:correctness_*` rocq_libraries were
  relying on transitive resolution that happened to work on main only
  because cached `.vo` files masked the missing flags. PR #150's
  alignment changes broke the happy accident; the deps are now
  explicit (matches the pattern in
  `pulseengine/loom/proofs/BUILD.bazel`).

### Deferred to v0.9.0
- **i64 T1 result-correspondence promotions.** The original umbrella's
  scope: 30 T2 → T1 lifts (arithmetic, bitwise, shifts/rotates,
  comparisons, bit-manip) plus discharging the 5 admits #150 introduced
  (4 div/rem T1 + 1 i64_const T1). These now ride into v0.9.0 as the
  primary theme, against the now-aligned model. Tracked in #147.
- F64↔I64 conversion implementations (see Documentation section).
- F32DemoteF64 (deferred from v0.7.0).

## [0.7.0] - 2026-05-25

Floating-point breadth + verifiable signing CI — synth now compiles
WASM modules with double-precision FP on Cortex-M7DP targets (i.MX RT1062
class), and the sigil keyless-signing path is now exercised end-to-end
in CI against a sha256-pinned wsc v0.9.0. PRs #140 (Phase 5 e2e),
#141 (f64 codegen).

**Falsification statement.** v0.7.0 would be wrong if (a) a WASM module
using only the f64 ops listed below produces an ELF that fails to link,
returns a synthesis error on a Cortex-M7DP target, or computes a result
that disagrees with the WASM reference on a covered op; or (b) the new
`signing-e2e.yml` workflow goes red on a clean `v0.7.0` checkout (cases
1 and 2 must remain hard checks; case 3 is xfail against
[sigil#135](https://github.com/pulseengine/sigil/issues/135)).

### Added

#### f64 codegen — ARM VFP-D end-to-end
- **WASM f64 modules now compile on Cortex-M7DP targets**
  (double-precision FPU, `FPUPrecision::Double`). The non-optimized
  selector (`InstructionSelector::select_with_stack`) lowers every
  f64 op for which the backend has a direct VFP-D encoding:
  arithmetic (`F64Add/Sub/Mul/Div`), comparison
  (`F64Eq/Ne/Lt/Le/Gt/Ge`), unary math
  (`F64Abs/Neg/Sqrt/Ceil/Floor/Trunc/Nearest`), binary math
  (`F64Min/Max/Copysign`), constants (`F64Const`), memory
  (`F64Load/Store`), and the i32/f32 conversion / bitcast family
  (`F64ConvertI32S/U`, `F64PromoteF32`, `F64ReinterpretI64`,
  `I64ReinterpretF64`, `I32TruncF64S/U`). Values live in VFP
  D-registers (D0..D15), allocated via a wrap-around counter
  mirroring the f32 S-register allocator.
- **Targets without double-precision FPU fail cleanly.** F64 ops
  on Cortex-M3 (no FPU) or Cortex-M4F (single-precision only) now
  surface a typed `Error::Synthesis` whose message names the
  missing capability ("target {} has no FPU" or "target {} lacks
  double-precision FPU"). Replaces the previous blanket "F64 not
  supported" path, and matches the existing validate_instructions
  feature-gate behavior. Silent miscompilation or panic is
  impossible — every f64 op is matched explicitly.
- **VFP-D encoding test coverage.** 24 new byte-level encoder
  tests cross-checked against the ARMv7-M Architecture Reference
  Manual (Section A7.5) cover VADD/VSUB/VMUL/VDIV.F64,
  VABS/VNEG/VSQRT.F64, VLDR/VSTR.64, VCVT.F64.F32, and
  VMOV core ↔ D-register. The coprocessor-11 (cp11 / 0xB)
  selection bit is verified independently from each arithmetic
  op's bit pattern.
- The optimized path (`optimize_full` in `synth-synthesis`) still
  declines modules containing f64 ops and falls back to the
  non-optimized selector (PR #126 behavior, unchanged); the
  fallback path is what now compiles f64 modules end-to-end.

#### Deferred to follow-up
- f64 ↔ i64 conversions (`F64ConvertI64S/U`, `I64TruncF64S/U`)
  remain unimplemented — they require i64 register-pair handling
  in the VFP-D backend. The selector emits a typed error
  mentioning "i64 register pairs on 32-bit ARM" when these ops
  are encountered, consistent with the existing f32 behavior.
- `F32DemoteF64` (round f64 to f32) is not yet handled — needs a
  `VCVT.F32.F64 Sd, Dm` ArmOp variant in the encoder.
- Extending the optimized IR path (`wasm_to_ir` → `ir_to_arm`) to
  model f64 is a separate, larger feature.

### Internal
- CI: `signing-e2e.yml` workflow added (Phase 5 end-to-end). Runs three
  wsc keyless cases against a sha256-pinned wsc v0.9.0. Case 3
  (tamper-negative) is `xfail` against current wsc — see
  [pulseengine/sigil#135](https://github.com/pulseengine/sigil/issues/135):
  `wsc verify --keyless` accepts WASM modules whose signed payload has
  been byte-modified after signing. Documented in
  `docs/sigil-integration.md`.

## [0.6.0] - 2026-05-24

Supply-chain close-out — synth produces all six evidence layers from
rivet#107's table (SLSA + cosign + SBOM + build-attest + signed-output
+ sbom-record). PRs #135 (Phase 5) and #136 (Phases 4 + 6).

### Added

#### CLI — sign synth's output ELF binaries (release roadmap Phase 5)
- **`synth compile --sign-output`** invokes sigil's
  `wsc sign --keyless --format elf` after writing the ELF, attaching a
  Sigstore keyless signature in place. Off by default — opt in per
  invocation; the unsigned compile path is unchanged for consumers
  without `wsc` installed. Composes with `--all-exports` (one signing
  call covers the multi-function ELF) and with `--sbom` (the SBOM
  records the unsigned synth output; the on-disk ELF after this
  command is the signed version). When `wsc` is missing, synth exits
  non-zero with an actionable error pointing at sigil's install
  instructions. See [`docs/sigil-integration.md`](docs/sigil-integration.md)
  for the trust model, verification command, and the wsc-version
  contract assumption.

#### Release pipeline — Phases 4 + 6
- **Phase 4 — crates.io trusted publishing.** New workflow
  `.github/workflows/publish-to-crates-io.yml` publishes the
  workspace's public crates (`synth-cli`, `synth-core`, `synth-frontend`,
  `synth-synthesis`, `synth-backend`, `synth-backend-{awsm,wasker,riscv}`,
  `synth-cfg`, `synth-opt`, `synth-verify`) on every `v*` tag via
  crates.io OIDC trusted publishing — no stored `CRATES_IO_TOKEN`.
  Internal-only crates (`synth-analysis`, `synth-abi`, `synth-memory`,
  `synth-qemu`, `synth-test`, `synth-wit`) carry `publish = false`.
  Dependency-order walk lives in `scripts/publish.rs` (compiled by
  `rustc` at workflow start). User-side step still required:
  per-crate trusted-publisher registration on crates.io.
- **Phase 6 — toolchain SBOM auto-emit.** `release.yml` now installs
  `cargo-cyclonedx` and writes `synth-v<VERSION>.cdx.json` (CycloneDX
  1.5 JSON) into the release assets before the SHA256SUMS step, so the
  existing cosign signature over `SHA256SUMS.txt` transitively covers
  the SBOM. Complements (does not replace) the per-compilation SBOM
  from `synth compile --sbom`.

### Changed
- Workspace `version` bumped from `0.1.0` to `0.6.0` to support
  crates.io trusted publishing (real semvers required) and to align
  the in-tree version with the next release tag. Going forward the
  workspace version is bumped pre-tag in lockstep with the release
  tag. Every published crate's internal `path` deps now also carry
  an explicit `version = "0.6.0"` so `cargo publish` can resolve
  them on crates.io.

## [0.5.0] - 2026-05-23

Verification & robustness release. Three workstreams: prototype-to-
production validator pattern, panic-free optimized lowering with the
gating fuzz harness restored, and the RV32 i64 integer surface
completed.

### Added

#### Verification — validator pattern reaches production (#76)
- **`Z3ArmValidator` now covers the full i32 + i64 op surface** —
  arithmetic, logic, shifts/rotates, comparisons, unary ops, div/rem
  for i32; the same arithmetic/logic/shift/comparison surface for
  i64, modeled as 64-bit bitvectors and decomposed into the (lo, hi)
  register pair the ARM lowering uses. Per-op Z3 SMT validation
  replaces hand-written Rocq lemmas for the i64 surface (the layer
  where Rocq is most painful). Negative tests confirm the validator
  rejects deliberately wrong lowerings. **133 synth-verify tests.**
  Closes #76 (CompCert-style untrusted-solver + trusted-validator
  strategy); sidesteps #73 (Rocq divergence). (#133)

#### RISC-V — i64 div/rem (Phase 3 completes the i64 integer surface)
- **`I64DivS` / `I64DivU` / `I64RemS` / `I64RemU`** lower to inline
  software long division (one shared 64-iteration restoring-binary-
  division core; signed wrappers compute magnitudes via branchless
  abs and fix the result sign). Wasm trap semantics honored:
  divide-by-zero traps via 64-bit-or-of-halves; `INT64_MIN / -1`
  overflow trap is emitted only for `div_s` — `rem_s` correctly does
  not trap there. **+11 tests, 158 RV32 selector tests.** (#131)

### Fixed

#### Optimized path — panic-free, fuzz re-gated
- **`ir_to_arm` returns `Result` instead of panicking** on an
  unmapped vreg. The `get_arm_reg` defensive panic (PR #101) was the
  last remaining panic site in the optimized lowering pipeline;
  166 call sites threaded through `?`. The backend falls back to
  the direct selector on `Err` (same shape as the issue-#120 float
  fallback). The diagnostic content of the original panic is
  preserved in the `Err` message — the bug-finder role still holds.
- **`pop_i32_unary!` macro converted to `?`** — sibling fix. The
  earlier slot_stack Result conversion missed this macro because
  its `.expect(...)` ended with `,` (macro-arg) not `;`
  (statement); the re-gated fuzz harness caught it on the first
  run.
- **`wasm_ops_lower_or_error` fuzz harness re-promoted to gating**
  (`gating: true`) — closes debt open since v0.3.1 / PR #117. The
  gating harness now serves as a permanent clean-room verifier of
  the panic-free invariant. (#132)

## [0.4.0] - 2026-05-22

### Added

#### RISC-V backend — i64 Phase 2
- **16 new i64 ops** in the RV32IMAC selector, building on the Phase 1
  typed register-pair model (v0.3.1):
  - `I64Mul` — low-64 product via `mul` + `mulhu`.
  - `I64Shl` / `I64ShrS` / `I64ShrU` — runtime-amount shifts with the
    cross-word (`shamt >= 32`) case handled.
  - `I64Rotl` / `I64Rotr` — composed from cross-word shifts.
  - `I64Clz` / `I64Ctz` / `I64Popcnt` — base-ISA software sequences
    (no Zbb dependency).
  - `I64{Lt,Le,Gt,Ge}{S,U}` — the hi-then-lo 64-bit comparison ladder.
  - `I64Extend8S` / `I64Extend16S` / `I64Extend32S`.
- i64 `div`/`rem` remain deferred to Phase 3 (need a `__divdi3`-style
  runtime); they fail loudly with `Unsupported`, not silently. (#128)

#### Supply chain — CycloneDX SBOM
- **`synth compile --sbom`** writes a CycloneDX 1.5 JSON SBOM
  (`<output>.cdx.json`, or an explicit path) documenting the synth
  compiler, the input WASM module (SHA-256 + size), the output ELF
  (SHA-256, size, target triple, backend), and the WASM module's
  imports as a dependency graph. This is the artifact consumed by
  `rivet import --format cyclonedx` for rivet #107's `sbom-record`.
  See `docs/sbom.md`. (#129)

### Changed
- Closed #72 (explicit WASM value-stack tracking): the production
  lowering path (`select_with_stack`) already tracks the value stack
  deterministically, and the `Replacement::Var`/`Inline` silent-`Nop`
  variants now error. The round-robin `select_default` flagged by the
  issue is test-only and never reaches a compiled binary.

## [0.3.1] - 2026-05-21

First release built and published by the automated release pipeline:
cross-platform binaries, SHA256 checksums, SLSA build provenance, and
cosign keyless signatures (see `docs/release-process.md`).

### Added

#### RISC-V backend — toward ARM parity
- **`WasmOp::Call` leaf-call lowering** — arguments marshalled into
  `a0..a7` per the RV psABI, label-based `RiscVOp::Call` resolved by the
  ELF builder. i64 call args and back-to-back calls with surviving
  results are deferred to v0.4 (need function-signature plumbing). (#116)
- **i64 Phase 1** — the selector's value stack is now a typed
  `Vec<VstackVal>` (`I32` / `I64 { lo, hi }`). i64 const, add, sub,
  and/or/xor, eq/ne/eqz, extend_i32_s/u, wrap_i64, and load/store. (#119)

#### Binary safety — Phase 1
- **`--safety-bounds` umbrella flag** (`mpu` / `software` / `mask` /
  `none`) with `--bounds-check` kept as a deprecated alias. RV32
  software bounds checks (`bgeu` + `ebreak` trap block), RV32 signed
  division overflow trap, and `safety-manifest.json` emission. (#115)

#### Verification
- **Validator-pattern prototype** — `CertifiedSelection` + `Validator`
  trait + `Z3ArmValidator` for `I32Add`. First step of the CompCert-
  style certifying-validator strategy toward retiring divergent Rocq
  proofs. (#113, issues #73 / #76)

#### Release engineering
- **Automated release pipeline** (`release.yml`) — tag-triggered
  cross-platform binary matrix, `SHA256SUMS.txt`, SLSA provenance via
  `actions/attest-build-provenance`, cosign keyless signing, GitHub
  release automation. `docs/release-process.md` documents the process
  and a 5-phase rollout plan. (#123)

### Fixed

#### Silicon-blocking codegen
- **`wasm_to_ir` slot-model rewrite** — `inst_id` was overloaded as both
  the unique IR id and the vreg-slot index, so any op that consumed a
  stack slot without producing one (`Drop`, `LocalSet`, stores, …)
  corrupted downstream back-references — a silent miscompilation Gale
  caught on real silicon. Decoupled via an explicit `slot_stack`. (#122,
  issue #121)
- **f32/f64 in the optimized path** — float ops fell through to
  `Opcode::Nop`, leaving downstream consumers with unmapped vregs and
  tripping the defensive panic. `optimize_full` now declines float
  modules with a typed error and the backend falls back to the
  non-optimized selector, which lowers f32 via VFP/FPU. (#126, issue
  #120)

#### Robustness
- **Pre-flight wasm stack-underflow check** (`wasm_stack_check`) — the
  lowering pipeline returns a typed `Err` on malformed input instead of
  panicking. `wasm_to_ir` now returns `Result` and propagates
  slot-stack underflow rather than `.expect()`-panicking. (#117)
- **`synth verify` exits non-zero** when the binary was built without
  `--features verify`, instead of printing a hint and exiting
  success-shaped — a no-op verify step silently passing CI is a
  correctness-of-process bug. (#125, issue #124)

### Changed
- CHANGELOG backfilled with per-version sections for v0.1.1–v0.3.0. (#114)

### Internal
- cargo-fuzz harness `i64_lowering_doesnt_clobber_params` gained a
  carve-out for return-value-placement dead stores. (#118, closes #112)
- `fuzz/seed_corpus/` directory layout for committed regression seeds;
  the fuzz-smoke workflow replays them on every run.

## [0.3.0] - 2026-05-15

### Added

#### Optimizations
- **`(i32.const C)(i32.load offset=O)`** folds to a single 4-byte
  `LDR rd, [base, #(C+O)]` when `C+O ≤ 4095`. Drops from ≥10 bytes
  (MOVW+MOVT+LDR triplet). Applies to load/store + sub-word variants. (#96)
- **u64-packed FFI return extraction**: `(i64.shr_u 32; i32.wrap_i64)`
  and friends lower to a direct hi/lo register rename. **83% size
  reduction** on the canonical pattern (48 bytes → 8 bytes). (#98)

#### Test + verification infrastructure
- 59 new semantic-correctness tests covering every i64 wasm op. Closes
  the gap that allowed #93 to ship. (#99)
- 37 tests of coverage uplift for the v0.1.1 diff. (#92)
- 4 cargo-fuzz harnesses + CI smoke gate (#100):
  - `wasm_ops_lower_or_error` (gating) — arbitrary `Vec<WasmOp>` through
    both lowering paths, asserts no panic / no unencodable instruction
  - `wasm_to_ir_roundtrip_op_coverage` (gating) — value-producing ops
    must emit live IR (catches the #93-class silent-drop bug)
  - `i64_lowering_doesnt_clobber_params` (exploration) — random
    i64/i32-param mixes, asserts AAPCS preservation
  - `encoder_no_panic` (exploration) — random ArmOp values, encoder
    panic-freedom
- Spectre/csdb policy doc + aarch64 CVE audit (CVE-2026-34971 /
  CVE-2026-34944) + arXiv 2604.17391 citation. (#105)
- 842-line binary-safety design covering MPU/PMP/CFI/PAC/BTI/MSPLIM with
  per-target applicability matrix and 5-phase roadmap. (#110)

### Fixed

#### AAPCS bug class — systematic closure
- 24 i64 ops (Eq/Ne/Lt/Le/Gt/Ge × Signed/Unsigned, Mul/Div/Rem,
  Rotl/Rotr, Clz/Ctz/Popcnt, Extend8/16/32 Signed, I32WrapI64)
  re-routed through `alloc_consecutive_pair`. (#106, #103)
- CSE missing arms for `MemLoad`/`MemStore`/`Extend` consumers added —
  fixes silent miscompile when CSE killed a duplicate load. (#107, #104)
- **Systematic audit**: 47 hardcoded R0..R3 sites swept, 6 new `Opcode`
  variants, 27 regression tests. (#108)
- `WasmOp::Call` had no `wasm_to_ir` handler — fell through to `Nop`,
  causing recursive `fib` to silently miscompile. (#109)
- **Defensive panic** on unmapped vreg replaces the silent `R0` fallback.
  Future wasm_to_ir gaps now crash the compiler with a diagnostic instead
  of producing miscompiled firmware. (#101)
- `I32WrapI64` no longer preassigns R0 — defers to function-return
  epilogue. (#111)

### CI / infrastructure
- Test + Clippy moved back to ubuntu-latest (smithy runners couldn't
  hold the z3-sys C++ build's intermediate files). (#102)
- Fuzz workflow split into gating (2 harnesses) + exploration (2 harnesses,
  `continue-on-error: true`). Promotion criterion documented.

## [0.2.1] - 2026-05-10

### Fixed
- **Silicon-blocking memset i64-codegen non-terminating loop** on
  Cortex-M. `optimizer_bridge::wasm_to_ir` had no handler for
  `I64ExtendI32U` / `I64ExtendI32S` / `I32WrapI64` — their result vregs
  were never mapped to ARM registers, and `get_arm_reg`'s silent R0
  fallback caused subsequent i64 shifts to read R0 as `rm_lo`/`rm_hi`,
  destroying memset's destination pointer. Discovered on real
  STM32G474RE silicon at `memset+0x4c` during Zephyr's `z_bss_zero`.
  Synth-emitted memset was 454 bytes vs picolibc's ~80 and looped
  forever. (#93 / #97)

## [0.2.0] - 2026-05-10

### Added — RISC-V RV32IMAC GA

- New `synth-backend-riscv` crate: RV32IMAC encoder, ELF builder
  (EM_RISCV=0xF3), PMP allocator, instruction selector, bare-metal
  startup + linker script generators.
- CLI: `--backend riscv`, `--target riscv32imac/rv32imac/rv32i/rv32gc/rv64imac/rv64gc`.
- New `synth riscv-runtime` command emits `startup.c` + `linker.ld` for
  cross-compilation with `riscv64-unknown-elf-gcc`.
- Selector covers the i32 surface (arithmetic, logic, shifts,
  comparisons, division with trap-on-zero), `i32.load/store` +
  sub-word load8/16 + store8/16, and control flow (block, loop,
  if/else, br, br_if). Locals for params 0..7.
- 98 RISC-V backend tests passing; encoder cross-validated against
  canonical RV32 hex encodings.
- Renode RV32IMAC platform (`tests/renode/synth_riscv.repl`) wired into
  Bazel CI.
- Offline integration smoke + end-to-end calculator demo.

### Known gaps (deferred to v0.3.x)
- i64 lowering for RV32 (register pairs)
- RV32F/D floating point
- br_table jump-table emission
- Cross-function calls + relocations
- RISC-V Rocq proofs

## [0.1.1] - 2026-05-10

### Fixed — AAPCS regalloc bugs (real-hardware-found via gale silicon tests)
- **Optimized path** — `optimizer_bridge::ir_to_arm` no longer hardcodes
  i64 ops to R0:R1 / R2:R3. New `alloc_i64_pair` picks free callee-saved
  pairs (R4..R11) skipping live param registers. Fixes silent corruption
  of i32 params when an i64 op ran before all params were read.
- **No-optimize path** — `select_with_stack` now allocates a stack frame
  for non-param locals and uses 8-byte STR/LDR for i64 locals so the
  upper half doesn't get dropped. Fixes corruption of the callee-saved
  spill area when a function has any non-param local.

### Added
- `HardwareCapabilities::imxrt1062()` — Cortex-M7 single-precision FPU,
  16 MPU regions, 8 MB QSPI flash, 1 MB OCRAM.
- `HardwareCapabilities::stm32h743()` — Cortex-M7 double-precision FPU,
  16 MPU regions, 2 MB Flash, 1 MB RAM.
- CLI `--hardware {imxrt1062,stm32h743}` and target-info wired up.
- Renode `synth_cortex_m7.repl` profile + `cortex_m7_test.robot`.
- MPU allocator tests proving 16-region operation on M7-class parts.
- CLI `--relocatable` flag — forces ET_REL output even when the wasm
  has no imports, for linking into a host build system (e.g. Zephyr).

### Toolchain hygiene
- 8 clippy errors fixed (Rust 1.95 lint refresh): `unnecessary_sort_by`,
  `collapsible_match`, `collapsible_if`, `manual_checked_division`.

## [0.1.0] - 2026-03-21

### Added

#### Compiler
- WebAssembly-to-ARM Cortex-M AOT compiler
- ~93 WASM opcodes compile to ARM (i32, i64, f32); SIMD/Helium encoding experimental; f64 decoded but not compiled
- Full control flow (block, loop, if/else, br, br_if, br_table, call)
- Sub-word memory operations (load8/16, store8/16)
- memory.size / memory.grow
- Globals, select, i64 register pairs
- ARM Thumb-2 instruction encoding
- VFP/FPU support (f32; f64 not yet supported in instruction selector)
- WASM SIMD to ARM Helium MVE (Cortex-M55) — encoding and instruction selection implemented, unit-tested only

#### Output
- ELF binary output with vector table and startup code
- Linker script generation (STM32, nRF52840, generic)
- MPU region configuration
- `synth compile --link` cross-compilation pipeline via arm-none-eabi-gcc

#### CLI
- `synth compile` -- compile WASM/WAT to ARM ELF
- `synth disasm` -- disassemble ARM ELF binaries
- `synth verify` -- Z3 SMT translation validation
- `synth backends` -- list available compilation backends
- Target profiles: cortex-m3, cortex-m4, cortex-m4f, cortex-m7, cortex-m7dp, cortex-m55

#### Verification
- Rocq mechanized proofs (233 Qed / 10 Admitted)
- All i32 operations (arithmetic, division, comparison, bit-manip, shift/rotate) have T1 result-correspondence proofs
- Z3 SMT translation validation (53 verification tests)
- STPA safety analysis (losses, hazards, UCAs, constraints)
- Rivet SDLC artifact traceability (250+ artifacts)

#### Testing
- 895 tests, all passing
- 227/257 WebAssembly spec test files compile
- Renode ARM Cortex-M4 emulation tests via Bazel

#### Examples & Integrations
- Zephyr RTOS integration examples
- Anti-pinch window controller (automotive safety demo)
- OSxCAR WASM compilation test

---

## Pre-release Development

### 2025-11-21
- Completed Phase 3a: 100% WASM Core 1.0 coverage (151 operations)
- Added Loom ASIL evaluation and integration analysis
- Added Bazel build system infrastructure

### 2025-11-17
- Initial codebase with 14 Rust crates
- Z3 verification framework
- ARM instruction encoding
- ELF generation
