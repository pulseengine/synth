# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.11.44] - 2026-06-14

**ENCODER ROBUSTNESS — gale #350: out-of-range `ADD #imm` now lowers instead of
failing the whole function (and the lowering is panic-free under fuzz).**

- **#350 — lower out-of-range `ADD #imm` to `MOVW(/MOVT)+ADD-reg`** (#351):
  `encode_thumb32_add_imm` returned `Err("ADD immediate too large for single
  instruction")` for any `imm > 0xFFF`, so a function using the indexed-address
  path `ADD ip, base, #off` with `off > 0xFFF` (e.g. `i32.store offset=70000`,
  as in gale's struct-return `gale_k_stack_push_decide`) failed to compile —
  emitting an empty object. The encoder now materializes the immediate into a
  scratch register (`MOVW ip,#lo16; MOVT ip,#hi16; ADD.W rd, rn, ip`, MOVT
  skipped when `imm ≤ 0xFFFF`), picking the scratch so it never aliases `Rn`
  (`rd` when `rd != rn`, else `R12`). Size-probe-consistent: the byte length
  depends only on `imm` and `rd==rn`, so the twice-encoded function agrees. The
  `#180`/`#185` "encoder produces a legal sequence, never asserts" class.
- **#350 follow-up — `rd==rn==R12` returns `Err`, not a panic** (#352): the
  lowering's in-place scratch is `R12`, which the `encoder_no_panic` fuzz harness
  can alias by feeding `Add{rd=R12, rn=R12, imm>0xFFF}` (arbitrary registers).
  An interim `debug_assert!` documenting "scratch ≠ Rn" therefore *panicked* under
  the fuzz's debug-assertions profile, breaking the Ok-or-Err contract. Replaced
  with a real `return Err` — the only register configuration the lowering cannot
  serve (no free scratch). Real codegen never emits `rd==rn==R12` (R12 is
  non-allocatable), so this is a **no-op for emitted code**: the #350 repro
  compiles to the same SHA256 with and without the guard. Fuzz: 2.46M execs,
  no panic.

  **Falsification:** wrong if `synth compile` of a wasm function with a
  `≥0x1000`-byte static offset (`scripts/repro/add_imm_large.wat`) emits an empty
  object or an address-truncated store (`add_imm_large_differential.py` would
  drop below 8/8 vs wasmtime); or if `cargo +nightly fuzz run encoder_no_panic`
  panics on any input. The four frozen behavior differentials (control_step
  0x00210A55, flight_seam 0x07FDF307, div_const 338/338, mutex_pressure) stay
  **byte-identical** — the change only adds a previously-erroring lowering path
  and an adversarial-only `Err` guard.

## [0.11.43] - 2026-06-14

**ON-TARGET SHIPPABILITY — gale #345: dissolved `--relocatable` objects are now
MCU-shippable and link-survivable (both fix steps bundled).**

- **#345 step 1 — zero-init wasm linmem → `.bss`** (#347): a dissolved
  `--relocatable --native-pointer-abi` object emitted the entire wasm
  linear-memory reservation as a SHT_PROGBITS `.data` section — ~64 KB of
  mostly-zero bytes, a non-starter on a 128 KB-RAM MCU. Now the zero-init
  reservation rides a SHT_NOBITS `.bss` (zero file bytes; the host loader zeroes
  it, preserving wasm zero-init semantics), with only the materialized
  `__synth_globals` slots in a tiny PROGBITS `.data`. Initialized `(data)`
  segments stay PROGBITS. Measured on the dissolved `k_mutex_unlock`: `.data`
  **65548 → 4 bytes**.
- **#345 step 2 — link-survivable linmem addressing** (#348): the
  `__synth_wasm_data`/`__synth_globals` addresses were loaded with inline-immediate
  `MOVW`/`MOVT-ABS` (`R_ARM_MOVW_ABS_NC`/`MOVT_ABS`), whose instruction-immediate
  form gets mangled into an undefined instruction when linked into a large Zephyr
  image (G474RE USAGE FAULT). Replaced with a **literal-pool load** — `LDR rX,
  [pc, #off]` from a `.text` word carrying `R_ARM_ABS32` (which `ld`/bfd patches
  in a data word and survives a large multi-object link). Mutex object: **22
  inline `MOVW/MOVT-ABS` → 0; 11 link-survivable `R_ARM_ABS32`**. (A new
  `LdrSym` literal-pool op, wired through the encoder + reg_effect; a defensive
  `func_base % 4 == 0` assert makes the imm12 alignment coupling explicit.)
  Together these unblock the 51 struct-return decide drop-ins + jess PR #60.
  The four frozen differentials (control_step 0x00210A55, flight_seam
  0x07FDF307, div_const 338/338, mutex_pressure) stay **byte-identical** (the
  whole change is gated on `--native-pointer-abi`).

  **Falsification:** wrong if a dissolved `--native-pointer-abi --relocatable`
  object still carries a 64 KB PROGBITS `.data` or any inline
  `R_ARM_MOVW_ABS_NC`/`MOVT_ABS` against `__synth_wasm_data`; or if gale's
  G474RE `mutex_api` (`CONFIG_GALE_WASM_LTO_MUTEX=y`) still links to a USAGE
  FAULT. (Reloc-shape + value-differential verified in-tree; gale's silicon
  link-test is the final gate.)

## [0.11.42] - 2026-06-14

**IF/ELSE-WITH-RESULT RECONCILIATION BUG-FIX — gale #313: asymmetric arms
silently miscompiled (then-path returned garbage); now fixed.**

- **if/else-with-result register reconciliation** (#313): `select_with_stack`'s
  `If`/`Else`/`End` lowering tracked the operand stack textually through both
  arms with no checkpoint at `If`, no restore at `Else`, and no reconciliation at
  `End`. For an `if (result …)` with asymmetric arms the two arms' results piled
  onto the vstack and `End` read the top (the else-arm's register)
  **unconditionally**, so the then-path — which branches over the else-arm —
  returned a register it never wrote (silent wrong-code, the #311/#331 class).
  Fix: checkpoint the vstack depth at `If`; at `Else` capture the then-arm's
  result registers and reserve them across the else-arm (reproducing the buggy
  code's incidental on-vstack protection, which is what keeps register-symmetric
  if/else byte-identical); at `End` reconcile the else-arm's result into the
  then-arm's register with a `MOV R_then, R_else` on the else path, emitting
  **nothing** when the arms already agree. No decoder/enum change — the result
  arity is observable from the vstack depth. A spilled or width-mismatched arm
  returns the ladder-recoverable exhaustion `Err` (retried/skipped, never
  miscompiled). Regression fixture `scripts/repro/u64_unpack_if.wat` +
  differential (`check_call(3,4) = 8`, was 0); the four frozen differentials
  (control_step 0x00210A55, flight_seam 0x07FDF307, div_const 338/338,
  mutex_pressure) stay **byte-identical** (none contains an `if`-with-result).

  **Falsification:** this fix is wrong if a re-decode of any `if (result …)` with
  asymmetric arms still shows `End`/return reading the else-arm's register on the
  then path, or if `check_call(3,4)` on `u64_unpack_if.wat` returns anything but
  8 on silicon. (The RISC-V selector has the same gap — tracked as #343, not
  fixed here.)

- **CI: `std::hint::black_box`** (#344): criterion (bumped to 0.8.2 in #339)
  deprecated `criterion::black_box`; stable-clippy's `-D warnings` then failed
  the synth-opt bench on every PR. Imported `black_box` from `std::hint`.

## [0.11.41] - 2026-06-13

**SPILL-SLOT COLLISION BUG-FIX — gale #331: dissolved `k_mutex_unlock`
silently miscompiled into a silicon deadlock; now fixed.**

- **Spill-slot / param-home collision** (#331): on a function with no i64
  (`has_i64 == false`), `compute_local_layout` set `i64_spill_base` to the same
  offset where the `#204 param_slots` are appended, so the i64 spill pool
  **aliased** the param home slots. `restore_caller_saved`'s call-result park
  called `spill.alloc()` without the `area_reserved` guard the arg-move-cycle
  resolver already used, parking `z_unpend_first_thread`'s result onto the live
  mutex-ptr arg's home slot — the no-waiter `lock_count = 0` store then reloaded
  the clobbered slot and wrote `linmem[0+12]` instead of `mutex+12`, deadlocking
  the G474RE (`owner=0, lock_count=1`). Fix: mirror the resolver's
  `area_reserved` guard at the result-park, so the first pass returns the
  ladder-recoverable exhaustion `Err` and the backend retry reserves the i64
  pool — relocating the param home slots above it so the park is non-aliasing
  and the function compiles **correctly** (not skipped). Verified on gale's exact
  committed module (`scripts/repro/synth-331/`): kill-criterion satisfied
  (no-waiter `lock_count` base = mutex pointer), all frozen differentials
  bit-identical. Regression test `synth_331_call_result_not_parked_on_live_param_home_slot`.
- **Multi-value-call × select regression lock** (#329/#330): the minimal
  reproducer + 3 discriminating controls committed as
  `tests/fixtures/multivalue_call_select/`; the multi-value-return ABI itself is
  tracked as VCR-SEL-003 (the selector still cleanly *skips* that shape).
- **VCR-RA-003 validator completeness gate broadened** (#332): the real-codegen
  zero-validator-rejects gate now spans the full ARM frozen suite (32 functions
  / 57 segments across 10 fixtures, was 3); the ≤5% decline kill-criterion is
  now asserted explicitly. Records the v-next "validate slot non-aliasing"
  extension (the layer #331 lived in).

## [0.11.40] - 2026-06-11

**THE ALLOCATOR ACCEPTANCE RELEASE — VCR-RA-001's five criteria are all met,
and gale's k_mutex_unlock lane unblocks (#242, #326).**

- **i64 pair-spill via param frame-backing** (#325): the last acceptance
  criterion closes. The true pair-exhaustion blocker was pinned param home
  registers (no stack spill can free them); a third retry-ladder rung forces
  the proven #204 param frame-backing onto call-free functions, after which
  a consecutive pair always exists (pigeonhole over the freed pool). Ladder:
  default -> spill-only (#320) -> spill+param-backing, each rung triggered
  only by its predecessor's exact error — bit-identity stays structural.
  NEW high-pressure-i64 lane: hard Err on v0.11.39 -> 6/6 vs wasmtime.
- **Arg-move cycles via the parallel-move resolver** (#327, gale #326): the
  call-marshal cycle-breaker no longer demands a callee-saved register —
  VCR-RA-004's resolver (v0.11.38) breaks cycles via a stack-scratch cell
  when registers are saturated. This unblocks the dissolved k_mutex_unlock
  (gale's exact error reproduced on main by the committed mutex_pressure
  lane; 7/7 vs wasmtime on the fix) AND killed a latent wrong-code bug: the
  old cycle-breaker miscompiled genuine 2-swaps (duplicated a value).
- **VCR-RA-001 status: implemented.** All five criteria verified: no
  hard-fail on high-pressure i32 AND i64 modules; fixtures bit-identical
  through six releases; cycles equal-or-better on the G474RE (gale); the
  v0.11.20 cost-gate revert EXECUTED (#322); the backward-dataflow validator
  guarding every re-allocated segment (#323). Honest bounds: the 8-slot
  spill pool, stack-passed params, the R8-pair/i64-param class (tracked).

Falsification: wrong if gale's mutex lane fails on silicon (native ref 124),
any previously-compiling module's bytes change, or any pressure lane
disagrees with wasmtime.


## [0.11.39] - 2026-06-11

**The assurance carrier: a backward-dataflow translation validator now guards
every re-allocated segment (#242, VCR-RA-003 v1) — and the v0.11.20 cost-gate
is deleted (VCR-VER-001 executed).**

- **Allocation validator** (`validate_segment_rewrite`, Rideau/Leroy CC'10
  style): every segment rewrite by the default-ON re-allocation pass must
  PROVE dataflow preservation — backward lockstep walk, equation sets
  (defs discharge, uses impose, entry must be identity vs the pass's input
  pinning) — or the segment falls back to original bytes. On first contact
  with production output it caught a real latent hazard (live-out pinning
  pins the last RANGE, not the register's exit VALUE) — benign at function
  returns (principled AAPCS scratch exemption), mechanically rejected with
  safe fallback mid-function until cross-segment liveness lands. Evidence:
  98.0% seeded-mutant kill (196/200; survivors are the documented dead-def
  equivalence class), 0 validator rejects on real fixtures, fixtures
  cmp-bit-identical.
- **The v0.11.20 reciprocal-mult cost-gate is DELETED** (#322): reverting
  proved byte-identical on every frozen fixture (the pressure vanished under
  accumulated improvements) and the guarded case is covered by v0.11.38's
  spill-on-exhaustion retry. The first greedy patch removed under the VCR
  program's exit criterion — allocation failures at the reciprocal-multiply
  now propagate to the retry instead of degrading to UDIV.

Falsification: wrong if the validator accepts a rewrite that changes observable
behavior (watched by the differential lanes + 98% mutant kill), or if any
previously-compiling module's bytes change (all fixtures sha-verified).


## [0.11.38] - 2026-06-11

**The first register-exhaustion hard-fail becomes recoverable
(#242, VCR-RA-001 steps 3b-lite + 4 substrate).**

- **Spill-on-exhaustion retry**: when `alloc_temp_safe` would hard-fail
  ("register exhaustion: all allocatable registers are live on the stack"),
  the function is re-selected with spilling enabled — the deepest
  stack-resident value moves to a frame slot (existing #171 `Spilled`
  reload-on-pop machinery) and selection continues. Bit-identity for every
  currently-compiling function is STRUCTURAL: the unmodified first pass runs
  for everyone; only the exact exhaustion error triggers the fresh-selector
  retry (which also forces the spill-area reservation that i32-only frames
  lacked). Honest bound: 8 spill slots cap simultaneous spills; the i64
  consecutive-pair and call-result hard-fail sites remain (next increments).
- **Cycle-safe parallel-move resolver** (`synth_synthesis::parallel_move`,
  VCR-RA-004): chains leaf-first, cycles broken via move-set-filtered scratch
  or a self-bracketing stack-scratch pair; property-tested across 6000
  deterministic sequentializations + directed swap/cycle cases with a
  structural size bound. Pure substrate for upcoming spill/reload insertion.
- NEW committed oracle: `scripts/repro/high_pressure_i32.wat` +
  unicorn-vs-wasmtime differential — hard `Err` on v0.11.37, compiles and
  passes 6/6 on this release.

All fixtures sha256-identical to v0.11.37; differentials PASS (13/13,
338/338, 0x07FDF307). gale's v0.11.36/37 scorecard verified everything
shipped (filter −8 cyc, #311 closed on silicon, #237 sizing confirmed).

Falsification: wrong if any previously-compiling module's bytes change, or
the high-pressure lane disagrees with wasmtime. The reciprocal-mult
cost-gate revert experiment (VCR-VER-001 evidence) is now runnable.


## [0.11.37] - 2026-06-11

**RV32 i64 locals + the per-op register-aliasing fix the behavioral oracle
caught (#312) — the packed-u64 verified-decide pattern is now correct on BOTH
lanes.**

- **RV32 i64 locals**: 8-byte (8-aligned) frame slots; `local.get/set/tee`
  emit two `lw`/`sw` (lo at off, hi at off+4) using the existing pair
  convention; call results from i64-returning callees are tagged as the
  `a0:a1` pair via the shared decoder result tables (#311); width inference
  reused from `synth_synthesis::infer_i64_locals` (now `pub`). i64 params
  stay fail-loud `Unsupported` (the psABI pair-register convention is its own
  increment).
- **Per-op alloc pin scope** (the real find): under the lowest-free allocator
  (#231), back-to-back `alloc_temp` calls within ONE wasm op's expansion
  returned the SAME register — every i64 pair collapsed to a single reg
  (`sw t0,0(sp); sw t0,4(sp)`), and popped operands lost clobber protection
  (the #232 class, generalized). `pop_any` now pins its operands and
  `alloc_temp` pins its grants for the duration of the op; targeted unpins
  keep worst-case pressure ≤ 11 of 13 pool registers.
- NEW committed oracle: `scripts/repro/u64_unpack_riscv_differential.py`
  (unicorn vs wasmtime) — 4/4 FAIL before the pin-scope fix, 4/4 PASS after;
  compile-only gating would have shipped the wrong code.

All four existing RV32 differentials PASS (controller_step, filter_axis,
signed-div-const, control_step); ARM fixtures cmp-bit-identical to v0.11.36;
175/175 backend-riscv tests.

Falsification: wrong if gale's RV32 funccheck lane disagrees with wasmtime on
the u64 family or any RV32 baseline regresses. Known + filed separately:
pre-existing `i64.div_s/rem_s` sign clobber (#317, probe staged).


## [0.11.36] - 2026-06-11

**Four silicon blockers in one tag: the allocator goes default-ON, the mutex
shadow-stack works, and the entire packed-u64 verified-decide pattern is
correct (#209/#237/#311, VCR-RA-001 step 3a).**

- **Range re-allocation DEFAULT-ON** (#309): the value-range re-colouring pass
  (wiring step 3a) is on for every compile after gale's on-target gate cleared
  it (byte-identical on flat_flight/controller/control_step, cycle-neutral +
  smaller where it fires). Opt out with `SYNTH_RANGE_REALLOC=0`; stats via
  `SYNTH_REALLOC_STATS=1`.
- **Dead callee-saved-save elimination** (#309): prologue/epilogue save lists
  shrink to the callee-saved registers the re-allocated body still touches
  (leaf-only, SP-untouched, even-count-padded) — `push {r4-r8,lr}` overhead
  (~12 cyc on a 37-cyc leaf) removed where the body packs into low registers.
- **Native-pointer ABI: materialized global slots + used-extent sizing**
  (#310, gale #237): every defined global lives at `__synth_globals + idx*4`
  in `.data`, initialized from the wasm global section — `global.set` is a
  real store (the old promotion DROPPED stores to the shadow-stack pointer),
  and the SP global starts at the wasm-ld stack top instead of 0 (the
  0xFFFFFFF4 bus fault). The region is sized to the USED extent (data end /
  stack top / layout globals / static addends) instead of declared 64 KiB
  pages: 131072 B -> ~4 KiB for gale's 830-byte module.
- **i64 pair correctness, all three legs** (#310, gale #311): (1) call results
  are pair-tagged (decoder result-type tables -> liveness sees r1, constants
  can no longer materialize into the live u64 pair; i64-local inference models
  call widths so both halves spill); (2) the encoder's I64SetCond/I64SetCondZ
  high-rd MOVS->CMP transmutation is fixed with 32-bit MOV.W/CMP.W — closing
  STPA hazard H-CODE-9; (3) the return epilogue moves BOTH halves of an i64
  result into r0:r1 (lo-first, safe for every consecutive pair).

Falsification: this release is wrong if gale's staged lanes disagree — the sem
unicorn check (count 0->1) and gmutex oracle on the G474RE are the decisive
gates, plus cycle-neutrality on the rebaselined suite (241/150/151/37). New
committed oracles: u64_unpack(+inlined).wat differentials,
native_pointer_shadow_stack differential, test_311_* + shrink_saves_* tests.


## [0.11.35] - 2026-06-09

**In-place select + spill-cost ranking — the first VCR codegen-quality release
(#209/#242, VCR-SEL-002).**

- **In-place select (#283):** the stack selector's `Select` lowering reuses
  `val2`'s register as the destination when `val2` is a consumed temp (not a
  live param, distinct from cond/val1), eliding the `EQ` "keep val2"
  conditional move — one `IT;MOV` per qualifying select instead of two, which
  is what native emits for a clamp `(x>k)?k:x`. Falls back to the fresh-dst
  two-move form when the guards don't hold (#193 param-clobber class).
  Measured `.text`: control_step 378→354 B (−6.3 %), flight_seam inlined
  1058→1020 B (−3.6 %), flat 1294→1244 B (−3.9 %). All four differential
  fixtures RESULT-identical (control_step 13/13 `0x00210A55`, flight_seam
  inlined+flat `0x07FDF307`, div_const 338/338).
- **Spill-cost ranking (#285, VCR-RA-001 wiring step 2):** the Chaitin/Briggs
  colourer picks optimistic spill candidates by cost/degree (cost = def+use
  occurrence count) instead of degree-only; the uncosted API reproduces the
  historic choice exactly. Pure and unwired — fixture ELFs bit-identical.
- **Allocator substrate (#279–#281, unwired/flag-gated):** SelectMove/Select
  modeled in `reg_effect`; allocator driver + `SYNTH_SHADOW_ALLOC` shadow
  pass; const-CSE rematerialization-avoidance behind `SYNTH_CONST_CSE`.
- **VCR traceability (#282, #284):** VCR-SEL-002/VCR-RA-002 filed;
  tool-qualification top-of-V (VCR-TQ-001/002: DO-178C/ISO 26262/IEC 61508/
  EN 50128 classification + evidence pillars); release-plan tags
  (`release-vX.Y`, queryable via `rivet list --filter`).

Falsification: this release is wrong if any module produces a different
*result* than wasmtime where `val2`'s register was still needed after a select
— watched by the four differentials and gale's on-target baselines
(filter_axis 37 / control_step 158 / flat_flight 255 / controller_step 162).

## [0.11.34] - 2026-06-05

**Un-wire the default-on `mul`+`add`→`mla` fusion — it regresses on-target until
the allocator lands (#277).**

The fusion (v0.11.32, #257) correctly fires on the real `flat_flight`, but gale
measured a **+2 cyc on-target regression** on the G474RE (255 → 257 cyc), stable
across re-measures, even though it removes 2 instructions and the seam stays
`0x07FDF307`. Root cause: over the greedy single-pass selector, folding
`mul rM,..; add rD,rM,rX` → `mla` **extends the live ranges of the mul inputs**
to the mla point, and the added register pressure costs more than the
single-cycle `MLA` saves. The transform is **register-allocation-coupled** —
net-positive only once a spill-aware allocator chooses registers (VCR-RA-001,
#272).

- **Fix:** remove the default-on wiring in `arm_backend`. `fuse_mul_add` stays as
  fully-tested infrastructure in `synth_synthesis::liveness`, to be re-wired
  *with* the allocator (where it pays off), per the wiring design note.
- **Restores** `flat_flight` to the pre-fusion v0.11.31 codegen (mul 4 / mla 0 /
  170 instr / 255 cyc). All three differential fixtures result-identical
  (`control_step` 0x00210A55, `flight_seam` 0x07FDF307, `div_const` 338/338).

**Lesson (gale's, recorded):** a register-pressure-affecting transform needs an
**on-target / allocator-aware** gate, not a byte-count gate — `1891→1819 B` read
as a win while silicon cycles regressed.

**Falsification:** wrong if `flat_flight` is not byte-identical to v0.11.31, or
any fixture differential diverges.

## [0.11.33] - 2026-06-05

**Whole-reachable-graph closure now follows `call_indirect` into table functions
(#275, foundation — see the honest scope note).**

`--all-exports` compiled the closure of the exports over **direct** `call`
(#235), but a function reached only through `call_indirect` (a table entry) was
invisible to that closure and left out of the ELF — so a module that dispatches
through a function table is not self-contained.

- **Decoder:** parse the Element section (`elem_func_indices` on `DecodedModule`)
  — the function indices that populate the table, i.e. the possible
  `call_indirect` targets. Empty for modules with no element section, so their
  output is byte-identical.
- **Closure:** `reachable_from_exports` now unions in every table function once a
  reachable function performs a `call_indirect` (a sound over-approximation —
  any table entry could be the dynamic callee), then keeps following their direct
  calls transitively. Verified on a minimal indirect-call module: the
  call-only-via-table target is now compiled into the object (was absent).
- **Behavior-frozen:** the three differential fixtures stay result-identical
  (`control_step` 0x00210A55, `flight_seam` 0x07FDF307, `div_const` 338/338) —
  they use no element section, so the closure is unchanged.

**Scope / known remaining (not in this release).** This lands the *reachability*
half. `call_indirect` **dispatch** in the `select_with_stack` (`--all-exports`)
path is still incomplete: the indirect call is currently dropped during
selection, and the encoder's table-base expansion uses R11 — which collides with
synth's R11 = linear-memory-base ABI. So a module using indirect dispatch now has
its table functions *present* in the ELF but the indirect call itself is not yet
wired end-to-end. Modules using only **direct** calls are fully self-contained.
Tracked for a follow-up.

**Falsification:** wrong if a module using only direct `call` still omits a
reachable internal callee, or if any fixture differential diverges.

## [0.11.32] - 2026-06-05

**`mul`+`add` → `mla` fusion now fires on the real `flat_flight` (#257 follow-up).**

The fusion shipped in v0.11.31 but fired **zero times** on gale's deployed
`flat_flight` object (`mul=4, mla=0`, byte-identical to pre-fusion). Root cause:
the soundness check `used_elsewhere` scanned the **whole function** for any read
of the mul-result register — but the single-pass allocator *reuses* that register
(`r8`) for unrelated later values, and the reads of those reincarnations falsely
blocked every fusion.

- **Fix:** replace the whole-function scan with a **precise live-range check** —
  the mul result must be dead after the add until the register is next redefined.
  Reads of a later, unrelated value in the same physical register no longer block
  the fusion. (Commutativity was already handled; gale's guess was a red herring —
  the bug was liveness precision.)
- **Measured on the real object** (`flat_flight.loom.wasm`, `cortex-m4
  --relocatable`): `mul 4 → 2`, `mla 0 → 2`, `170 → 168` instructions. The two
  filter products (`gyro*980`, `accel*20`) now fuse as intended.
- **Behavior-frozen:** all three differential fixtures result-identical
  (`control_step` 0x00210A55, inlined+flat `flight_algo` **0x07FDF307 with the
  fusion firing**, `div_const` 338/338).
- Removes the now-dead `op_may_use` helper; adds a regression test pinning the
  register-reuse pattern (`mul r8; add r2,r5,r8; movw r8,#980; mul r2,r7,r8`).

**Falsification:** this release is wrong if gale's G474RE reflash shows
`flat_flight` cycles *not* decreasing, or any fixture differential diverging from
the hashes above.

## [0.11.31] - 2026-06-05

**gale codegen pass: a load/store correctness fix + two `flat_flight` instruction-selection wins (#257/#258/#259).**

Three gale-reported items from the wasm-cross-LTO silicon work, all behavior-frozen
against the differential fixtures (`control_step` 0x00210A55, inlined+flat
`flight_algo` 0x07FDF307, `div_const` 338/338 — all result-identical).

- **Load/store `imm12` offset bounds check (#259, correctness).** The eight
  thumb32 load/store immediate-offset encoders masked `offset & 0xFFF` and emitted
  unconditionally — for `offset >= 4096` the access silently targeted the wrong
  address. They now error (forcing register-offset addressing), closing the
  load/store sibling of the #253/#255 silent-miscompile class. Defensive: the
  selector already materializes large offsets, so no live breakage.
- **`cmp`/`cmn` immediate folding (#258, lever #3).** A compare against a constant
  bound now folds into `cmp a, #C` (positive) or `cmn a, #|C|` (negative) instead
  of materializing the bound into a register — the int8 clamps cost 18 IT-blocks
  vs native's 6.
- **`mul` + `add` → `mla` fusion (#257, lever #2).** The flight filter's
  `gyro*980 + accel*20` lowered as separate `mul` then `add`; it now fuses to a
  single `mla`. New `ArmOp::Mla` + a liveness-driven, control-flow-sound fusion
  pass (`fuse_mul_add`: fires only when the mul result is read solely by the add).
  Measured: `flat_flight` text 1891 → 1819 bytes (~18 muls fused), `flight_seam`
  still 0x07FDF307 with the fusion firing.

**Falsification:** this release is wrong if a load/store with `offset >= 4096`
emits a truncated (wrong) address instead of erroring, or if any `mul;add`
fusion / `cmp`/`cmn` fold changes a frozen differential's result. Verified: all
three fixtures result-identical; the fusion's measured byte delta lands only on
the filter sites; new encoder/fusion unit tests cover the bounds + soundness
declines.

## [0.11.30] - 2026-06-05

**Self-contained native-pointer ABI: register-promote the stack-pointer global so a dissolved leaf seam runs with no host runtime (#237).**

v0.11.29 made wasm *statics* base-independent under `--native-pointer-abi`, but a
real loom-dissolved seam (gale's `mutex_m.loom.wasm`) also reads its **stack
pointer** from a wasm global — `(global $__stack_pointer (mut i32) 65536)` — and
synth lowered `global.get`/`global.set` as `[R9, idx*4]`, a load from a globals
table that a runtime is expected to populate. A drop-in object has no such
runtime, so `R9` is garbage and the stack mis-addresses.

**Fix (opt-in `--native-pointer-abi`):**
- The decoder now captures each global's `i32.const` initializer + mutability
  (previously discarded).
- The CLI identifies the stack-pointer global (mutable `i32` whose init is a
  plausible stack top) and threads it through `CompileConfig`.
- The selector register-promotes it: `global.get $sp` materializes
  `__synth_wasm_data + init` (MOVW/MOVT) — the real stack top — and frame
  arithmetic carries that base, so SP-relative loads become true memory
  accesses. `global.set $sp` is dead in a leaf, balanced function and is
  dropped. The SP init doubles as the static-data base that separates pointer
  consts (`>= base`, e.g. a `&static_spinlock` call arg → relocated) from
  frame-size scalars (`< base`, e.g. `i32.const 16` → plain immediate).

**Falsification:** this release is wrong if, for a leaf host-pointer seam compiled
with `--native-pointer-abi`, the emitted object retains any `R9`-relative globals
access, or a frame-size constant is emitted as a `__synth_wasm_data` relocation.
Verified on `mutex_m.loom.wasm`: 12 `__synth_wasm_data` MOVW/MOVT relocations
(SP read + every spinlock pointer arg), **0 R9 references**, all imports +
internal callees proper `THM_CALL` relocs. Frozen `control_step` fixture stays
bit-identical (13/13, ORACLE PASS) — every new path is gated behind the flag.

---

**Verified-codegen infrastructure (VCR-*) — constant-immediate folding + a class of latent encoder miscompiles fixed (epic #242).**

The verified-codegen roadmap (`artifacts/verified-codegen-roadmap.yaml`) began
landing incrementally. This release adds the constant-immediate-folding family
and — found via the roadmap's *verify-before-transform* discipline — fixes a
class of latent silent miscompiles in the Thumb-2 data-processing immediate
encoders.

- **Constant-immediate folding:** `i32.and`/`or`/`xor` fold a constant operand
  `0..=0xFF`, and `i32.add`/`sub` a constant `0..=0xFFF`, directly into the
  instruction immediate, dropping the `movw` materialization (#250/#252/#254).
  Fires on real code (`control_step`'s frame `sub #16`), differentials
  result-identical.
- **Analysis foundation:** register def/use + liveness + dead-store /
  redundant-const detection (`crates/synth-synthesis/src/liveness.rs`, #243/#245)
  — pure analysis, the basis for the upcoming spill-capable allocator.

**Encoder correctness (latent silent-miscompile class, Ok-or-Err):**
- `ORR`/`EOR` immediate emitted a silent `0xBF00` NOP instead of the operation
  (#251).
- `ADD`/`SUB` immediate `>= 0x100` (incl. `add sp, #frame`) silently
  mis-encoded — `#256` became `#0`, **corrupting the stack of any function with a
  ≥256-byte frame**. Now uses ADDW/SUBW (T4) for `0x100..=0xFFF`, errors beyond
  (#253).
- `CMP`/`ADDS`/`SUBS` immediate packed raw bits without ThumbExpandImm — a
  comparison/arithmetic against the wrong constant. Now share a correct
  `try_thumb_expand_imm` reverse-encoder and error on un-encodable values,
  forcing register materialization (#255).

**Falsification:** this release is wrong if any Thumb-2 data-processing immediate
encoder (`AND`/`ORR`/`EOR`/`ADD`/`SUB`/`CMP`/`ADDS`/`SUBS`) emits bytes that
decode to a value other than the requested immediate, or emits a NOP/silently
wrong instruction instead of erroring on an un-encodable immediate. Verified:
`try_thumb_expand_imm` round-trips the modified-immediate patterns; `add sp,#256`
→ `0d f2 00 1d` (ADDW), not `#0`; the three frozen differentials
(`control_step` 0x00210A55, inlined+flat `flight_algo` 0x07FDF307, `div_const`
338/338) stay result-identical across every change.

## [0.11.29] - 2026-06-04

**`--native-pointer-abi`: wasm statics as base-independent `.data`, so host-pointer drop-ins work on silicon (#237).**

A loom-dissolved host-pointer primitive (e.g. `z_impl_k_mutex_unlock`) mixes two
memory-access classes that need different base treatment, but synth lowered both
as `[linmem_base + addr]`:
- a **host `*ptr` arg** (a real kernel pointer) needs `base = 0` for a native
  deref (`[0 + ptr] == [ptr]`), set by the caller's trampoline; and
- a **function-static** (a wasm-resident `static`, e.g. a `k_spinlock`) at a
  compile-time-const address needs `base = &(placed wasm data)`.

`base` can't be both, so with the `base=0` trampoline the static resolved to the
raw wasm offset as an absolute address and MPU-faulted on the nucleo_g474re
before producing output.

**Fix (opt-in `--native-pointer-abi`):** under the flag, a const memory address
**anywhere in the wasm linear memory** is a static and is addressed
**base-independently** — the whole linear-memory minimum is emitted as one
RAM-resident region (a writable `.data` when there is initialized data, else a
`.bss`/NOBITS — no flash cost), with a `__synth_wasm_data` section-base symbol,
and the access materializes `__synth_wasm_data + addr` via `R_ARM_MOVW_ABS_NC` /
`R_ARM_MOVT_ABS` relocations (new `ArmOp::MovwSym`/`MovtSym`; `CodeRelocation`
gains a `RelocKind`). This covers **both** initialized `(data)` statics **and
zero-init/BSS** ones — a `static k_spinlock lock;` is zero-init (no `(data)`
segment), the common kernel case. Runtime (host-pointer) addresses — beyond the
linear memory — keep the `[R11=0 + addr]` native deref. The two coexist in one
function (the mutex: host `k_mutex*` **and** its `static lock`).

- **Opt-in → frozen by default.** Without the flag the base-relative
  `[R11+const]` path is unchanged, so the value-in/value-out leaves
  (`control_step`/`flat_flight`) — whose silicon numbers depend on it — stay
  **bit-identical** (all six differential fixtures verified).
- **Object-level proof** (`native_pointer_static.wat`; `arm-none-eabi-readelf`):
  with the flag, `.data` is present (`WA`), `__synth_wasm_data` is a defined
  OBJECT symbol, and the static store carries MOVW_ABS/MOVT_ABS relocations
  against it; the host-pointer load stays base-relative. Without the flag,
  neither appears. Unit test
  `test_237_static_store_is_symbol_relative_under_native_pointer_abi`.

## [0.11.28] - 2026-06-04

**`--all-exports --relocatable` now emits reachable internal callees, not just the exports (#235).**

A loom-dissolved export can retain a non-inlinable internal callee — e.g. a
`core::panicking::panic_fmt` reached from an overflow-checked arithmetic path
that loom correctly declines to inline. Previously `--all-exports --relocatable`
compiled *only* the exported functions, leaving such a callee as an undefined
symbol (`func_N`, `U`) in the ET_REL object, so the host link failed. The only
way to compile a non-export (`--func-index N`) produced an ET_EXEC image with
startup stubs that `ld` rejects — there was no path to a linkable object set.

**Fix:** `--all-exports` now also compiles every internal (non-imported) function
**reachable** from the exports via `call`, transitively (new
`reachable_from_exports`). Each non-exported callee is emitted under its
`func_{index}` symbol — exactly the name an internal `call` relocation already
references — so it resolves within the same object. Imports stay external (the
linker resolves them).

- **Behavior frozen:** a module whose exports call no internal function (every
  current leaf fixture) yields exactly the exports, so output is bit-identical —
  verified across all six differential fixtures (ARM `div_const`/`control_step`/
  `flight_seam`; RV32 `control_step`/`controller_step`/`signed_div_const`).
- **Proof:** for an export calling a non-exported helper, the helper's symbol
  goes from `UND` → `FUNC GLOBAL DEFAULT` in the ET_REL object (`reachable_helper.wat`
  repro; `arm-none-eabi-readelf -s`). Unit tests `reachable_from_exports_*_235`.

## [0.11.27] - 2026-06-03

**RV32 fix: signed-division overflow guard no longer clobbers the dividend (#232).**

A v0.11.26 regression (introduced by the #231 lowest-free allocator). The
`i32.div_s` `INT_MIN / -1` overflow guard pops its dividend/divisor off the
vstack and then allocates scratch registers for the `INT_MIN` and `-1`
comparison constants. Because the popped operands are no longer on the vstack,
`live_regs` did not protect them, and the lowest-free allocator reused the
dividend's register for the `INT_MIN` constant — clobbering it before the guard's
`bne` read it. `filter_axis_decide(1000,100,500)` returned 0 instead of 1088 on
qemu_riscv32 (round-robin in v0.11.25 had marched to a different register and
masked the latent bug).

**Fix:** new `alloc_temp_avoiding(&[Reg])` — the guard materializes its constants
into a register that avoids the (popped-but-live) dividend and divisor. Applied
to both the i32 guard and the i64 `INT64_MIN / -1` guard (the i64 path is not yet
reachable — i64 params/locals are unimplemented — but carries the same latent
defect). Same liveness-across-a-branch-region class as #226.

- **Regression proof:** new `scripts/repro/signed_div_const.{wat,wasm}` +
  `signed_div_const_riscv_differential.py` — 5/5 vectors (incl. the 1088 repro,
  the `INT_MIN` overflow edge, and negatives) match wasmtime. Unit test
  `signed_div_guard_does_not_clobber_operands_232`.
- All five prior fixtures stay bit-identical (ARM `div_const`/`control_step`/
  `flight_seam`; RV32 `control_step`/`controller_step`). The rest of the #231
  caller-saved win is preserved (leaf functions still spill 0 callee-saved regs).

## [0.11.26] - 2026-06-03

**Cleanup: RV32 allocator prefers caller-saved registers (lowest-free, not round-robin).**

Audit-cycle cleanup of the RISC-V temp allocator. `alloc_temp` recycled the pool
`[t0..t6, s1..s6]` with a monotonic `next_temp` round-robin counter — "fine for
straight-line code" but, even after #226 made it skip live registers, it kept
marching *forward* into the callee-saved s-registers instead of reusing a
just-freed low register. So short-lived expressions needlessly used s-registers
and paid the #220 save/restore prologue tax.

Now that the vstack liveness is tracked (#226), `alloc_temp` simply returns the
**lowest-indexed free temp**. The pool lists caller-saved t-registers first, so a
function stays in them whenever ≤7 values are simultaneously live — the
callee-saved s-registers become a genuine overflow reserve rather than something
the round-robin consumed by accident.

- **Behavior frozen, oracle-confirmed bit-identical:** all five differential
  fixtures — ARM `div_const` 338/338, `control_step` 13/13 (`0x00210a55`),
  `flight_seam` `0x07FDF307`; RV32 `control_step` (`0x00210a55`),
  `controller_step` (`0x05ff0000`).
- **Measured delta:** `controller_step` RV32 `.text` 440 → 368 bytes (−72 B,
  −18 instructions); callee-saved spills 6 → 0; frame 48 → 16 bytes. Results
  unchanged (register renaming).
- The broader local register allocation / constant-CSE work (the Opt-3 perf lever
  gale flagged in #209) remains separate; this is just the round-robin → lowest-free
  cleanup.

## [0.11.25] - 2026-06-03

**RISC-V: fix register allocator clobbering a live value across `select` (#226).**

The RV32 temp allocator recycled its 13-register pool round-robin with no
awareness of the operand stack. A value left live on the `vstack` (e.g. an
`updates << 24` byte computed early and packed in at the end) had its register
re-handed-out as scratch once the round-robin wrapped past the pool length —
silently clobbering it. `controller_step_decide`, which keeps `updates << 24`
live across three `select`-based clamps, lost the updates byte on qemu_riscv32
(got `0x000000ff`, wasmtime `0x05ff0000` in the bundled repro).

**Fix:** `alloc_temp` now skips any register currently pinned by a live `vstack`
entry (`live_regs`), so an in-flight value is never reused as scratch. If every
temp is pinned, it flags `alloc_exhausted` and the function is skipped (honest
skip-and-continue under `--all-exports`) rather than miscompiled — the same
discipline as the ARM regalloc-exhaustion path. This is the RISC-V analogue of
the ARM #193 live-value reservation.

- Differential proof (`controller_step_riscv_differential.py`): 5/5 vectors —
  including gale's `(6400,0,-12800,0,3200,0,5)` — now match wasmtime, with
  callee-saved registers preserved (#220 still holds). Before the fix, all 5
  mismatched.
- Regression tests: `alloc_temp_skips_live_vstack_regs_226`,
  `alloc_temp_flags_exhaustion_when_all_pinned_226`.

## [0.11.24] - 2026-06-03

**Cleanup: drop the dead divisor constant on the reciprocal-multiply path (#221).**

Audit-cycle cleanup of the Opt 1b reciprocal-multiply codegen (introduced in
v0.11.19). When a non-power-of-two constant `div_u` is lowered via the
Granlund-Montgomery UMULL high-word multiply, the divisor itself is never read —
the multiply consumes the precomputed magic constant, not the divisor. The
divisor's eager `i32.const` materialization was therefore dead on this path but
still emitted. This drops it (the cost-gate UDIV fallback still materializes its
own divisor, so behavior is unchanged).

- **Behavior frozen, oracle-confirmed:** all three differential fixtures stay
  bit-identical — `div_const` 338/338, `control_step` 13/13 (`0x00210a55`),
  `flight_seam` `0x07FDF307`.
- **Measured delta:** −20 bytes `.text` on `div_const.wat` (5 reciprocal-multiply
  const-div sites × one dead 4-byte `MOVW` each), and −1 executed instruction per
  const-div call site at runtime.
- Regression test asserts the dead `MOVW #500` is no longer emitted on the UMULL
  path (`test_209_const_divisor_uses_reciprocal_multiply`).

## [0.11.23] - 2026-06-03

**RISC-V backend: implement `Select`, non-parameter locals, and i32 sign-extend (#223).**
The RV32 selector rejected ops the ARM backend handles, blocking every realistic
function (the straight-line `filter_axis` slipped through; `control_step` /
`controller_step` / `flat_flight` did not). Added:
- **`select`** (ternary) — lowers to a short branch + two moves (RV32 has no
  conditional-move), for both i32 and i64 operands. Pervasive: every saturating
  clamp / min/max lowers to it.
- **Non-parameter locals** (`local.get/set/tee` for `idx >= num_params`) — now
  frame-backed: each i32 local gets a 4-byte stack slot (`sw`/`lw`). The slots
  sit at the bottom of the frame; the #220 callee-saved spills go above, in one
  unified prologue -- so locals + saved registers share a single `addi sp,-N`.
- **`i32.extend8_s` / `i32.extend16_s`** — `slli`+`srai` (RV32 has no sign-extend).

With these + #220, gale's dissolved `control_step` compiles to RV32 and runs
correctly: a unicorn RV32 differential matches wasmtime -- and the ARM backend --
on `(3000,50,40,0) = 0x00210a55` across vectors, reading its `.rodata` table via
`s11` and preserving the caller's callee-saved registers. Fixtures:
`scripts/repro/control_step_riscv_differential.py`; unit tests
`select_lowers_to_branch_223`, `sign_extend_uses_slli_srai_223`,
`non_param_local_uses_frame_223`; 163 riscv tests green.

Note: i32 locals only (i64 locals would need two slots) -- not yet hit by the
dissolved modules; leaf functions per #220.

Falsification: wrong if any RV32 function with `select`/non-param-locals/sign-
extend returns a value differing from wasmtime, or if the unified frame
misaligns a local or saved-register slot.

## [0.11.22] - 2026-06-03

**RISC-V backend: preserve callee-saved registers per the RV psABI (#220).**
The RV32 register allocator hands out callee-saved s-registers (`s1`..`s6`) as
temporaries once the caller-saved `t`-registers are exhausted, but the backend
emitted no prologue/epilogue — so a function that used them **corrupted the
caller's s-registers** (including `s11` = `__linear_memory_base`), hanging
qemu_riscv32 timing loops. gale's first on-target RISC-V finding, now reachable
via #218.

A post-build pass (`preserve_callee_saved`) scans the function body for the
callee-saved registers it writes and wraps it in a balanced prologue
(`addi sp,sp,-N; sw s_i,..`) + epilogue (`lw s_i,..; addi sp,sp,N`) before every
`ret` -- spilling+restoring exactly those registers (the ARM backend's
`push {r4-r8,lr}` equivalent). It is a no-op for functions that use only
caller-saved (`t`/`a`) registers, so simple functions pay nothing. `s0` (fp) and
`s11` (linmem base) are excluded -- the allocator never targets them.

Validated on `filter_axis_decide` via a unicorn RV32 differential: the result
matches wasmtime on signed/unsigned vectors AND the caller's sentinel-seeded
s-registers are restored. Fixtures: `scripts/repro/filter_axis.{wasm,wat}` +
`filter_axis_riscv_differential.py`. Unit tests
`callee_saved_registers_preserved_220` + `no_frame_when_only_caller_saved_220`;
160 riscv backend tests green.

Note: leaf functions only for now (these wasm functions make no calls); non-leaf
`ra`/caller-saved preservation across calls is a follow-up.

Falsification: wrong if any RV32 function writes a callee-saved register without
spilling it, or if the wrapped body changes its returned value.

## [0.11.21] - 2026-06-03

**Expose RV32 target profiles so `-b riscv` is reachable from `compile` (#218).**
The RISC-V backend existed and worked, but there was no way to target it: `-t`
only accepted Cortex-M triples, so `-b riscv` always inherited the default
`ArmCortexM` profile and bailed (`RISC-V backend cannot compile for ArmCortexM`),
and the short ISA names the toolchains use (`rv32imac`, …) were "unknown target
triple". This was purely a CLI/target-profile wiring gap.

- `TargetSpec::from_triple` now accepts the short RV32 names — `rv32imac`,
  `rv32imc`, `rv32im`, `rv32i`, `rv32gc`, the generic `riscv32`/`rv32`, and the
  `esp32c3` board alias (RV32IMC) — alongside the existing long LLVM triples,
  via a new parameterized `TargetSpec::riscv32(extensions)`.
- `synth compile -b riscv` with no `--target` now defaults to `rv32imac` instead
  of inheriting the ARM profile, so the backend is reachable out of the box.
- The "unknown target triple" error now lists the RV32 options, and `-t`'s help
  text documents them.

`synth compile fn.wasm -b riscv -t rv32imac --relocatable` (and `-t rv32imc`,
`-t esp32c3`, or bare `-b riscv`) now emit a RISC-V (`EM_RISCV`, ELFCLASS32)
relocatable object. This unblocks the wasm→loom→`synth -b riscv`→RV32 path for
ESP32-C3 / qemu_riscv32. Tests: `test_rv32_short_target_names_218` (parsing) +
`test_resolve_target_spec_riscv_default_218` (the `-b riscv` default).

Not in scope (follow-ups): `target-info` still only knows the ARM board profiles
(it uses board `HardwareCapabilities`, not target triples); RISC-V codegen
quality/correctness is validated separately on-target.

Falsification: this release is wrong if `synth compile -b riscv -t rv32imac`
fails to produce a valid RISC-V object, or if an RV32 target name resolves to a
non-RISC-V spec.

## [0.11.20] - 2026-06-02

**Cost-gate the reciprocal-multiply — fixes the Opt 1b register-pressure
regression (#209).** v0.11.19's `UMULL` reciprocal-multiply needs more live
scratch than `UDIV` (the magic constant + UMULL's two output registers), and
gale's `control_step_decide` — four constant `div_u` (`/500 /5 /80 /1000`) on the
9-register R0–R8 pool (after the #212 R12 reserve) with a deep operand stack —
exhausted the allocator, which **hard-failed** (`register exhaustion … function
too complex`) instead of spilling. It had compiled correctly on v0.11.18, so Opt
1b regressed it from "compiles + correct" to "won't compile."

Two changes:
- **Cost-gate:** if the reciprocal-multiply's scratch registers can't be
  allocated, fall back to the guard-elided `UDIV` (which needs no new temps and
  is always correct). The function always compiles; only the tightest divides
  lose the multiply.
- **Two-temp `a == false` path:** the common (no add-indicator) case now reuses
  `dst` as UMULL's throwaway low word, so it needs only the magic + high-word
  registers. This dropped `control_step`'s peak pressure enough that **all four
  divides keep `UMULL`** — it compiles *and* keeps the full Opt 1b win.

Validated: `control_step_decide` now compiles and matches wasmtime **13/13**
across a vector spread, including gale's reference `(3000,50,40,0) →
0x00210A55`. Committed as a permanent fixture
(`scripts/repro/control_step.wasm` + `control_step_differential.py`, which loads
the `.rodata` table into linear memory). The `div_const` oracle still passes
338/338 (the two-temp path is exercised by `/500`, `/641`, …). Unit test
`test_209_multi_const_div_does_not_exhaust` asserts four constant `div_u` under
pressure compile (UMULL or UDIV fallback), never hard-fail.

Falsification: this release is wrong if any function with constant `div_u`
fails to compile under register pressure, or if a cost-gated `UDIV` fallback
produces a result differing from the WebAssembly spec (wasmtime).

## [0.11.19] - 2026-06-02

**Reciprocal-multiply for constant unsigned division (#209 Opt 1b).** A
non-power-of-two constant divisor in `i32.div_u` no longer emits `UDIV` (≈12
cycles on Cortex-M4) — it lowers to the Granlund–Montgomery magic-number
sequence: `UMULL` (the new ARM op) to take the high word of `dividend × magic`,
then an `a`-selected shift (≈3–5 cycles). This is the dominant `control_step`
win gale's silicon stats pointed to (#210): the binning divides `/500 /5 /80
/1000` now multiply instead of divide.

For `x / 500`:
```
movw r3,#0x4dd3; movt r3,#0x1062    ; magic = 0x10624DD3
umull r4,r5,r0,r3                   ; r5 = umulhi(magic, x)
lsrs r2,r5,#5                       ; q = r5 >> 5
```
versus the previous `movw r1,#500; udiv r2,r0,r1`.

New `ArmOp::Umull { rdlo, rdhi, rn, rm }` with Thumb-2 (`0xFBA0`) and A32
(`0xE0800090`) encodings, an SMT-bitvector semantics model in synth-verify, and
the test ARM interpreter taught `UMULL` + the immediate `LSL/LSR/ASR` forms. The
magic numbers are computed by `magicu()` (Hacker's Delight §10-9), covering both
the `a` (add-indicator) and `s == 0` cases.

Power-of-two divisors still use `LSR`, `/1` a `MOV`, signed division and `rem_u`
keep their Opt 1a guard-elided forms (signed reciprocal-multiply and the `rem`
variant are deferred). Validated against the wasmtime differential oracle:
**338/338** across 13 lowered forms × 26 edge-case inputs — now including `/7`
(`a = true`), `/641` (`s = 0`), and `/0x7FFFFFFF` (`a = true, s = 31`) to
exercise every codegen branch. `magicu` is separately checked against brute-force
`n / d` for a spread of divisors × dividends; the `UMULL` encoding is byte-checked
on both ISAs; encoder fuzz stayed total (262k execs, no panic).

Falsification: this release is wrong if any `i32.div_u` by a constant produces a
result differing from the WebAssembly spec (wasmtime) — in particular if a magic
number or the `a`/`s` selection is off for any dividend.

Also adds the fully-dissolved (flat, no internal call) `flight_algo` from #215 as
a second differential fixture (`scripts/repro/flight_seam_flat.{wasm,wat}`); the
harness auto-detects the internal `bl` so it guards both the inlined (#212) and
flat (#215) lowering shapes. #215 was the same R12/IP scratch-clobber as #212 —
Opt 1a's guard elision (v0.11.17) shifted register allocation in the larger
function onto R12, exposing the latent bug; the #212 reserve (v0.11.18) already
fixes it (verified on the v0.11.18 tag: `0x07FDF307`).

## [0.11.18] - 2026-06-02

**Reserve R12/IP as encoder scratch — fixes the inlined-callee-after-opaque-call
miscompile (#212).** The encoder uses R12 (IP) as its scratch register: it lowers
an indexed linear-memory access `[R11 + addr + #off]` to
`ADD ip, addr, #off; LDR/STR rd, [R11, ip]`, and several constant/VFP helpers also
clobber IP. But R12 was *also* in `ALLOCATABLE_REGS`, so under register pressure
the operand allocator could place a live value in R12 — which the next memory
access's `ADD ip, …` then overwrote.

gale's loom-inlined `flight_algo` hit this: it calls the opaque `filter_step`
(which stores the divided fields `st[0]`/`st[4]` via `i32.div_s /1000`), then runs
the inlined `controller_step` body that reads them back as `0 - (mdeg>>6 +
rate>>7)`. The constant `0` (the negation base) was allocated to R12; the very
next `i32.load` emitted `ADD ip, addr, #4`, turning `0 - sum` into
`(addr + 4) - sum` — a huge value that saturated aileron/elevator to 127. The
non-divided fields (yaw, updates) read correctly because their negation base
landed in a normal temp, not R12. The flat (un-inlined) version was correct
because it never reached the pressure that hands out R12.

Fix: R12 is now reserved alongside R9/R10/R11 (`ALLOCATABLE_REGS` is R0–R8;
`RESERVED_REGS` includes R12) — a live operand can never reside in the encoder's
scratch. This matches the standard ABI treatment of IP as a reserved scratch.
i64 register pairs are unaffected (R12's pair-hi was always reserved, so R12 was
never a valid i64 lo).

Validated against the wasmtime differential oracle: synth's ARM now matches
ground truth `0x07FDF307` (was `0x07FD7F7F`) on gale's exact vector. Regression
fixtures: `scripts/repro/flight_seam.{wasm,wat}` +
`scripts/repro/flight_seam_differential.py` (runs the full `flight_algo`,
including the internal `bl filter_step`, under unicorn), plus
`test_212_selector_never_allocates_r12` and the updated allocator-invariant unit
tests. The #209 constant-division oracle still passes 260/260 (the two changes
compose).

Falsification: this release is wrong if any compiled function reads a stale
register for a memory value across an indexed load/store — i.e. if the
`flight_seam` differential (or any inlined-reader-after-opaque-call) diverges
from wasmtime.

## [0.11.17] - 2026-06-02

**Constant-divisor strength reduction + dead trap-guard elision (#209 Opt 1).**
When the divisor of `i32.div_u/div_s/rem_u/rem_s` is a known constant (the
immediately-preceding op is `i32.const C` — sound because `i32.const` is a
(0,1) stack op, so it *is* the value the division pops as its divisor),
`select_with_stack` now lowers it without the dead runtime traps:

- A nonzero constant divisor makes the div-by-zero `CMP/BNE/UDF` guard dead —
  it is elided. For `div_s`, a non-`-1` constant also makes the INT_MIN/-1
  overflow guard (`MOVW/MOVT` INT_MIN + `CMP` + `CMN #1` + `BNE` + `UDF #1`)
  dead — also elided. gale's `control_step` (binning `/500 /5 /80 /1000`) loses
  3 instructions per unsigned divide and ~9 per signed divide.
- `div_u` by a power of two `2^k` lowers to `LSR rd, rn, #k` — no `UDIV`, no
  guard (`0x8000_0000` counts as `2^31` since the divisor is unsigned).
- Division by 1 becomes an identity `MOV`; `rem` by 1 becomes `MOV #0`.

A constant *zero* divisor keeps the guard (it must still trap at runtime). The
signed `div_s` by `-1` keeps the overflow guard (INT_MIN/-1 traps). Only the
unsigned path strength-reduces beyond guard elision; signed power-of-two (which
needs a rounding-bias sequence) and the non-power-of-two reciprocal-multiply
(needs a new `UMULL` op) are deferred to a follow-up.

Validated against the wasmtime differential oracle: 260/260 across all 10
lowered forms × 26 edge-case inputs (INT_MIN, `0x8000_0000`, `0xFFFF_FFFF`,
power-of-two boundaries, signed negatives) on the actual `--relocatable`
`select_with_stack` path. Regression fixtures:
`scripts/repro/div_const.wat` + `scripts/repro/div_const_differential.py`, and
seven `test_209_*` selector unit tests asserting the lowered instruction
sequences (and that zero/`-1` divisors keep their guards).

Falsification: this release is wrong if any `i32.div_*`/`i32.rem_*` by a
constant produces a result differing from the WebAssembly spec semantics
(wasmtime) — including the trap behaviour for a constant-zero divisor.

## [0.11.16] - 2026-06-02

**Param-register reservation — fixes the call-free param clobber (#193), gale's
dropped-operand bug (#210).** In `select_with_stack`, a register-backed param
lives in r0–r3 but is not on the operand stack, so the temp/pair/reload
allocators (`alloc_temp_safe`, `alloc_consecutive_pair`, and the spilled-operand
reloads in `pop_operand`/`peek_operand`) — which avoided only the operand-stack-
live registers — could hand a still-live param's register out for a constant,
i64 result, or reload under pressure, clobbering it before a later read. gale's
**call-free** `control_step_decide`: `coolant_c` is param 2 → r2, and the
constant `80` was materialized into r2 → `subs r3,r2,r2` (= 80−80 = 0), forcing
`enrich` to 0. (Call-*containing* functions were already safe — #204 frame-backs
their params; this is the call-free gap.)

Every temp/pair/reload allocation now reserves the param registers that are
still live at that point (tracked by each param's last read, like the #204
frame-backing's liveness). The `i64_lowering_doesnt_clobber_params` fuzz, which
exercised this class, is now green (1M+ executions, 0 clobbers).

Regression test: `test_193_const_does_not_clobber_live_param` (a constant after
enough pressure to exhaust the temp bank must not land on a live param's r0).

_Falsification:_ this release is wrong if any instruction in a call-free
function writes a parameter's home register (r0–r3) before that parameter's last
`local.get`.

## [0.11.15] - 2026-06-01

**ARM32 (A32) encoder dropped the register index on indexed loads/stores
(#206).** On the default `--target arm`, `Ldr`/`Str`/`Ldrb`/`Strb`/`Ldrh`/`Strh`/
`Ldrsb`/`Ldrsh` fed their address through `encode_mem_addr`, which returns only
the 12-bit immediate — so a register offset (`[rn, rm, #off]`, e.g. a WASM
`iN.load`/`store` with a runtime address) silently collapsed to `[rn, #off]`,
sending the access to the wrong address. A register offset now materializes
`ip = rn + rm` (clobbering the scratch IP/R12) and loads from `[ip, #off]`,
uniform across word/byte/halfword/signed forms. This only affected the default
ARM/A32 target; Cortex-M (Thumb-2) was already correct (its encoder handles the
register-offset addressing mode), which is why gale's `--target cortex-m4` build
was unaffected. Found while diagnosing #204.

Regression test: `test_encode_arm32_indexed_load_keeps_index_206` (verify-bytes —
`ldr r0,[r11,r1,#8]` must encode as `ADD ip,r11,r1` + `LDR r0,[ip,#8]`, never a
bare `LDR r0,[r11,#8]`).

_Falsification:_ this release is wrong if any ARM32 `Ldr*`/`Str*` whose `MemAddr`
carries an `offset_reg` encodes to a single instruction (the register index would
again be dropped).

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
