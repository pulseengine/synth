# The home-register alias class (#1189) — enumeration, RQ-65-ALIASCLASS

**Question.** `local.get` of a register-homed local pushes THE HOME REGISTER
uncopied onto the operand stack. Any later write to that register through a
different path is a silent overwrite of the local. #1190 fixed one consumer
(the if/else join). How many others exist, on all four legs?

**Answer, in one line.** After a mechanical audit of every emitted instruction
over 4,628 direct-selector functions and an execution oracle over 117 consumer
shapes on four legs: the class had **two unfound consumers left** — aarch64
`rotl` (#1221, an in-place negate of a param home) and the direct selector's
i64-param `local.set`/`local.tee` (#1222, a half-written pair) — plus two
adjacent non-alias defects (#1223, an IR fold; #1226, the multi-module
`.wast` param-width table, surfaced by the #1222 fix). Both alias consumers
are fixed in this artifact; every other site is either guarded or pinned
with a stated structural reason below. The enumeration is complete OVER THE
STATED INPUTS, with the bound spelled out at the end.

Related history, so the class is seen as one thing: #193 (temp allocated into
a live param), #518 (i64 hi half unreserved), #663 (loop back-edge liveness),
#677 (bulk-memory pointer walked in place), #973 (reload into a committed
operand), #989 (get→set→use WAR), #1048 (i64 shift expansion masked the amount
in place), #776/#1221 (aarch64 rotl negate), #1189 (if/else join), #1222 (i64
param set). Eight consumers over 30 releases, each found as a wrong answer.

## Producers — where a home reaches the operand stack uncopied

| leg | producer | what is aliased |
|---|---|---|
| ARM direct (`select_with_stack`; every `--relocatable` compile, #197, and every self-contained function the optimized path declines) | `LocalGet` of a param in `local_to_reg` (call-free function, AAPCS r0–r3, i64 as an even-aligned pair), of a #390-promoted i32 local (r4–r8), of an f32/f64 param on a hard-float target (S/D register) | the home register / pair itself (`StackVal::Reg { reg: home }`) |
| ARM optimized (`ir_to_arm`) | `Opcode::Load` of a param: `vreg_to_arm[dest] = param_regs[i]`; of a non-param local: the local's register | the physical param register, no copy |
| RV32 | `lower_local_get` of a **param**: **COPIES** (`mv dst, a_n`) — the home never reaches the vstack. Of a #472-**promoted** local (`s8..s10`): aliased directly | the s-register |
| AArch64 | `WasmOp::LocalGet` of a param in a leaf function that never writes a param (`!home_params`): `stack.push(params[i])` | the AAPCS64 register |

## Consumers — every site that WRITES a stack entry's register, per leg

Disposition key: **GUARD** = code path that copies/reserves, with an execution
oracle; **PIN** = a stated structural reason a write cannot happen, watched by
a test; **FIXED** = a new miscompile found by this artifact, fixed red-first.

### ARM direct selector (the audited leg)

Method: `synth_synthesis::home_alias::audit` — for every instruction with a
`source_line`, the exhaustive (222-variant, no-wildcard) `gp_defs`/`vfp_defs`
table names what it writes; a write to a live home (loop-back-edge extended
liveness, #663) that is not the local's own set/tee and not straight-line
into an inline epilogue is a hit. Swept over the pinned spec testsuite (257
files) + tests/wast + tests/wat + fixtures + scripts/repro on {relocatable,
self-contained} x {cortex-m4, cortex-m4f}, WITH the suite submodule present
(the lane's first figures — 4,628 functions, 2,372 homes — were a suite-only
run: the script's corpus root resolved one level too shallow and never saw
tests/wat, fixtures or scripts/repro): **1,045 (module, leg) pairs, 8,317
functions, 8,776 homes, 261,440 attributed instructions, 0 hits**
(`home_alias_audit_corpus_1189.py`, CI job `home-alias-audit-1189`). The
first run over the FULL corpus reported 12 hits, every one a false positive
of the WALK and fixed in the walk rather than pinned: (a) 8 x the inline
epilogue `pop {r4-r8, pc}` at a mid-function `return` / function-level
`br_if` — it restores a promoted local's r4 and RETURNS in the same
instruction, but the terminal-write scan started PAST the writer
(`cabi_arena_{bind,realloc}.wat` func_0, `home_alias_class_1189_promo.wat`
p_brif); (b) 4 x the caller-save RESTORE `vldr s0, [sp, #n]` of an f32 home
after a `bl` (`f32_ops_719.wat` xhome/xcall2) — the audit had not stated the
AAPCS VFP caller-saved clobber (s0–s15) on calls, so the `bl` that makes the
restore necessary was invisible and the restore looked like the write. Calls
now carry the clobber in `vfp_defs` (a MISSING restore is a hit — re-swept:
none on the corpus) and the round trip is proven on the stream
(`write_is_bracketed_by_save_restore`); each exemption's negative variant
reproduces exactly its own shape (8 / 4) and nothing else.

**Potency, wired.** `hits: 0` over a corpus proves the sweep RAN, not that
the detector FIRES, so the sweep's self-test phase runs first:
`SYNTH_HOME_ALIAS_AUDIT=verbose,plant` makes `home_alias::plant_probe` plant
ONE synthetic write of a watched home at op 0 of every function that has a
home still read later (on a copy of the stream) and every such function MUST
decline with the needle at `op 0` — pinned EXACTLY per (fixture, leg), both
directions: i32 params r0–r3 58/7/58/7, promoted locals r4–r8 11/9/11/9, VFP
homes 0/0/11/11 (soft-float m4 has none); 192 planted writes reported, 0
declines without the plant. Historical potency, kept: the same audit on the
pre-#1190 compiler flags exactly the 10 functions #1190 recorded as wrong
and none of its 7 pinned-clean ones.

**#1226, stated plainly.** The walk is correct and #1226 was never a
home-register WRITE: it is a mis-HOMING, and its real mechanism is wider
than first filed — the synth-cli `.wast` driver path threads NO declared-
width tables at all (`Vec::new()` for params/returns i64/f32/f64, each
annotated "WAST fixture suite is i32-only"), so on ANY `.wast`, single-module
included, an i64/f32/f64 param or result whose width body inference cannot
recover is homed as i32. Measured: the same module text as `.wat` gives
`second3` homes=4 / `mov r0, r2; mov r1, r3`; as `.wast` homes=2 / `mov r0,
r1`. This audit trusts the selector's home table by construction, so it
never saw #1226 itself; the 16 hits were the #1222 pair-write (fired by body
inference) landing in the neighbour's wrongly assigned R1, and the
declared-width gate removed them by changing the emission, not the walk —
no coverage of home writes was lost. It is pinned RED-FIRST on the `homes=`
count instead: `home_alias_width_1226.wast`, its last module derived at run
time as a single `.wast` and as the identical `.wat`, (merged, single-wast,
wat) = (7, 6, 8) relocatable / (4, 4, 8) self-contained, `wast < wat` on all
4 legs until a fix makes them equal and flips the pin. Consequence for the
`#1222` row below: its spec-suite instances are `.wast` inputs, where the
declared table is empty and the pair-write arm never fires — they are NOT
fixed by #1222 and stay wrong until #1226 is fixed.

| consumer | disposition | reason / evidence |
|---|---|---|
| every temp-allocating op (binary, unary, compare, load, const, conversions, select, block/if results) | PIN | `alloc_temp_safe` excludes stack-live registers AND `live_params` (#193: every register-homed local until its last read, i64 hi halves included #518, loop-extended #663); a dest is never a live home. Audited: 0 hits over the corpus; executed: 117 shapes x 2 ARM legs match wasmtime |
| `if (result)`/`else` join `mov R_then, R_else` | GUARD | #1190: then-result that is a live home is copied on the then path; oracle `join_alias_1189_differential.py` |
| `block`/`loop`/`br`/`br_if`/`br_table` value carry (#509/#931) | PIN | the block result register is a fresh temp with the home only ever a SOURCE (`bbrif`/`bfall` in #1190; `brif_blk`, `brtab`, `blkfall`, `loopcnt` here); a function-level `br_if` with a home value keeps the home intact on the fall-through (`brif_fn`, executed) |
| `return` / function-level `br` result move into R0 | PIN | the move runs straight-line into the inline epilogue (`add sp; pop {…, pc}`) — no later op can run; the audit proves this ON THE STREAM (`write_is_terminal`), and a `br_if` that wrote R0 before a conditional branch would stay a hit |
| the inline epilogue `pop {r4-r8, pc}` itself (mid-function `return`, function-level `br_if`) | PIN | it WRITES r4–r8 — a promoted local's home — and returns in the same instruction, so the writer IS the terminator; `Pop` has no conditional form in `ArmOp` and both encoders emit it unconditionally. The first full-corpus run flagged 8 of these because the terminal scan started past the writer; a `pop` without `pc` stays a hit (unit-tested) |
| `local.set`/`local.tee` of the SAME local (i32) | GUARD | the one legitimate writer; #989 snapshots still-live aliases first (`war_set`, executed) |
| `local.set`/`local.tee` of an **i64 param** | **FIXED #1222** | wrote only the lo half, at `index_to_reg(i)` instead of the AAPCS pair, with the alias snapshot reserving only `val_lo`; now `write_i64_param_home` moves both halves at the `local_to_reg` home, ordered for partial overlap, with both halves of `val` reserved — for `.wat`/`.wasm` input (the oracle's own i64 fixture, executed). The spec-suite functions first listed as affected (`fac.wast fac-opt`, `loop.wast while`, `local_set/local_tee.wast type-param-i64`, the 64-bit bulk-memory `checkRange`s, `memory_grow64 check-memory-zero`) are `.wast` inputs: #1226's real mechanism leaves their declared widths EMPTY, the arm (gated on the declared width) never fires there, and they remain wrong until #1226 is fixed |
| `local.set`/`tee` of ANOTHER local | PIN | stores to the frame slot / moves into the other local's register; the source home is read only (`set_other`, `tee_other`, executed) |
| `memory.fill`/`memory.copy` walking pointers | GUARD | #677 `bulk_mutable_operand` copies a live operand to scratch (`fill`, `copy`, executed) |
| `call` argument marshalling / caller-saved clobber (core registers) | PIN | a call-containing function frame-backs its integer params (#193/#204) and promotion is leaf-only (#390), so no CORE home exists to alias (`icall` row in #1190) |
| `call` caller-saved clobber (VFP, cortex-m4f) | PIN | an f32/f64 param or #1069-homed float local KEEPS its S/D home across a call; s0–s15 are AAPCS caller-saved and the selector saves the home to a frame slot before the `bl` and reloads it after. `vfp_defs` states the clobber on every call-shaped op and the audit proves the round trip ON THE STREAM (`write_is_bracketed_by_save_restore`: same register, same static slot, the save before any other write of the home in the op, nothing between save and restore touching the slot, its base register or control flow) — a missing restore, a restore from another slot, a store into the slot, an SP move or a label in between all stay hits (unit-tested). Corpus: 0 hits with the clobber stated; executed: `f32_ops_719_differential.py` (238/238 bit-exact vs wasmtime, incl. "f32-across-call spill/reload", m4f under unicorn) |
| spill-on-exhaustion reloads | GUARD | #973 `pop_operand_committed` reserves already-popped operands; the #1189 copy declines honestly if displaced |
| encoder expansions with hidden scratch (`POPCNT`→R11 #1021, i64 shift amount #1048, VCVT transit S-register) | out of the audit's sight, stated | the `ArmOp` names no home there; covered by the expansion-canary gates and #1048's read-only amount |

### ARM optimized selector (`ir_to_arm`)

| consumer | disposition | reason / evidence |
|---|---|---|
| every IR op's dest | PIN | a local's vreg is in `local_vregs` and is never freed, so its physical register is never handed to another dest; test `optimized_path_never_writes_a_param_home_1189` walks 18 families with `gp_defs`: nothing writes r1–r3, r0 once (the result). Executed: `arm-self` leg, 57 i32 + 38 i64 + 11 promo shapes |
| `if`/`else` | PIN | `wasm_to_ir` lowers only fixed if/else shapes into a `Select` with a FRESH dest; any surviving `If` routes the function to the direct selector |
| `(x - x) + x` | **not this class — #1223, pinned OPEN** | an IR fold/DCE defect (the folded const wins over the surviving use); recorded wrong value pinned in the oracle until fixed |

### RV32

| consumer | disposition | reason / evidence |
|---|---|---|
| any consumer of a **param** | PIN | `local.get` COPIES (`mv dst, a_n`); test `param_local_get_copies_and_no_consumer_writes_the_home_1189` (a1 never a dest, a0 only by the result move). This is the "accident of implementation" the artifact names: a future "alias params on the vstack" byte-saving change must get past this test and the rv32 leg of the oracle |
| temp-allocating ops on a **promoted** local | PIN | `s8..s10` are outside the temp pool; test `promoted_local_is_written_only_by_its_own_set_and_the_epilogue_1189`; executed: `promo` module, 9 functions |
| `br`/`br_if` edge canonical register | GUARD (unreachable today) | `canonicalize_edge_value` copies a promoted register instead of donating it; `promotion_stays_depth0_or_931_guard_goes_live` pins the coupling (#931) |
| `local.set`/`tee` of the promoted local | GUARD | `snapshot_aliases` (#472) |
| i64 params | decline | #312 (pinned as a decline, never a wrong answer) |

### AArch64

| consumer | disposition | reason / evidence |
|---|---|---|
| every temp-allocating op | PIN | `TEMPS` = x9..x15, disjoint from the x0..x7 argument registers; the reconciliation register is drawn from `TEMPS` too; test `param_homes_are_never_a_destination_1189` (17 two-operand + 4 unary families, w1 never an Rd) |
| `i32.rotl`/`i64.rotl` count negate | **FIXED #1221** | the #776 fix negated `k` "in its own now-dead register" — dead only for a temp; a param home read back as `-count`. Now a param count is negated into a scratch chosen with `n`, `k`, `dst` held live; a temp count keeps the #776 bytes (`i32_rotl_is_neg_then_rorv`, `i32_rotl_temp_count_keeps_in_place_neg_1221`) |
| loads: `dst = ea` reuse | PIN | `ea` is a fresh temp from `form_ea`, never the popped address |
| `local.set` of a param | PIN | `writes_param` forces `home_params`, so a written param is slot-resident and `local.get` LOADS a copy |
| `if`/`block` reconciliation | PIN | reserved register from `TEMPS` (VCR-A64-CF-001) |

## Execution oracle (`home_alias_class_1189_differential.py`, CI job `home-alias-class-1189-oracle`)

117 functions (58 i32, 48 i64, 11 promoted-local) x 2–4 vectors x 4 legs,
every expected value from wasmtime, memory pre-filled identically on both
sides, declines pinned per leg EXACTLY. Red-first on main (`af819788`): `live
vectors: 990 matched, 9 diverged`, naming #1221 (7 vectors) and #1222 (2);
fixture half: 10/10 pinned wrong vectors from main's own bytes. After the
fixes: `999 matched, 0 diverged`, 10/10 still reproduce from the fixture,
#1223 pinned open. 1,629 emulations.

Byte-identity of the fixes over 1,419 compiles / 10,725 functions (spec suite
+ local corpus, {arm-reloc, arm-self, aarch64}): 58 functions changed, every
one an aarch64 function containing `rotl` or an ARM function that
`local.set`/`tee`s an i64 param; 0 newly declined, 0 newly accepted, no
skip-set moved.

## The bound of the search — stated, not implied

* The static audit sees every EMITTED instruction of the ARM direct selector,
  so a `_ =>` arm nobody walked cannot hide a write — but only over the inputs
  swept (the pinned suite + local corpus, 8,317 functions on 1,045 (module,
  leg) pairs; the 805-module
  real-world census is not on the lane machine). The per-family oracle covers
  the consumer families the corpus may not exercise with a home operand.
* Instructions with `source_line: None` are not audited (prologue/epilogue;
  the count is reported: 33,406 over the full sweep, ~4.0 per function).
* Hidden scratch inside encoder expansions is outside the `ArmOp` and the
  audit (item above); the expansion-canary gates own it.
* The other three legs have no per-op attribution, so they are pinned by
  structural tests plus the execution oracle, not by an audit of every
  emitted word.
* VFP homes (cortex-m4f) are audited statically (the m4f sweep legs, with the
  AAPCS VFP call clobber stated); the f32-across-call shape the sweep
  exercises is executed under unicorn by the CI-wired
  `f32_ops_719_differential.py` (238/238 bit-exact), not by this artifact's
  own oracle.
