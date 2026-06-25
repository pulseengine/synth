# #468 scoping spike — redundant linear-memory-base materialization

**Issue:** synth#468 · **Epic:** #242 (VCR-*) · north-star #390
**Status:** IMPLEMENTED flag-off (`SYNTH_BASE_CSE`) — see "Implemented" below.
Default-on flip held for the on-target cycle gate, exactly like the cmp→select /
local-promotion / immediate-shift / dead-frame levers.

## The pattern

A straight-line run of stores to constant addresses re-materializes the
linear-memory base on **every** store. The optimized (non-relocatable) lowering
emits, per `i32.store* (i32.const ADDR) V`:

```
movw ip, #<base_lo>      ; ip = 0x.... (linmem base, a compile-time constant)
movt ip, #<base_hi>
add.w ip, ip, rN         ; rN = the (also constant) address
str.w  rV, [ip]
```

The base is loop-invariant — identical for every store in the function — yet it
is rebuilt (`movw`+`movt` = 8 B, ~2 cyc) before each one. A run of N stores pays
N base-materializations where **1** would do.

## Measurement (this spike's fixture + the frozen corpus)

`redundant_base_materialization.wat` — 7 consecutive const-address stores,
neutral addresses/values (tied to nothing real). Count of base-materializations
(`movw ip,#<base_lo>`) per path, ARM cortex-m4:

| fixture | optimized path | relocatable path |
|---|---:|---:|
| redundant_base_materialization | **7** (6 redundant) | **0** |
| control_step | 2 | 0 |
| flight_seam | 21 | 0 |
| flight_seam_flat | 42 | 0 |

Reproduce (needs a Thumb-2-aware disassembler, e.g. `arm-none-eabi-objdump`).
All these fixtures share the linmem base `0x20000100`, so the base low half is
`#256` — the exact pattern the table counts:

```sh
synth compile scripts/repro/redundant_base_materialization.wat \
      -o /tmp/rbm.elf -b arm --target cortex-m4 --all-exports
arm-none-eabi-objdump -d -M force-thumb /tmp/rbm.elf | grep -c 'movw	ip, #256'
```

On the 7-store fixture the redundant 6 cost **48 B** (6 × `movw`+`movt`) and
~**12 cyc**. The waste scales with store-run length — flight_seam_flat shows 42
base-materializations in the optimized path.

## Root cause + the two-path finding (the load-bearing result)

The two codegen paths diverge, and **the relocatable path already implements the
target codegen**:

* **Relocatable path** (`select_with_stack`; what the frozen byte gate compiles):
  the base is a *relocated symbol*, not a constant, so the lowering pins it in a
  **stable register** (`fp`) once and addresses every store as `str.w rV,[fp,#off]`
  — **0 redundant materializations**. This is exactly the shape #468 wants.

* **Optimized path** (`optimizer_bridge.rs::ir_to_arm`; non-relocatable): the base
  is an absolute constant, and the lowering re-materializes it into **`ip` (r12)**
  per store. `ip` is *encoder scratch* (the encoder reuses it to expand indexed
  loads — see the R12-reserve fix), so it provably **cannot** hold the base across
  stores. The optimized path therefore has no persistent base register today.

So the fix is **not a post-pass peephole** — it is an allocator-aware change in
`optimizer_bridge.rs`: reserve a **stable callee-saved register** for the base
(as the relocatable path does with `fp`), materialize it once at function entry
when ≥2 const-address stores share it, and address each store `[base, #off]`.
This answers the scoping question "why is `ip`/r12 used here?" — the optimized
path uses a fuller register file but spends scratch on a re-built constant rather
than reserving a base reg; the disasm even shows it spilling store *values* to the
frame (`str.w rN,[sp,#off]`) instead of caching the invariant base.

## Frozen-safe rationale

For **this** commit it is frozen-safe *by construction* — no codegen is touched;
frozen gate verified green on the branch.

For the **eventual CSE** it is contingent, and the impl PR must verify it: the
property holds *only if the change is confined to the optimized path*. The frozen
byte gate (`frozen_codegen_bytes.rs`) compiles `--relocatable` (base-materialization
count already **0**), so a strictly optimized-path CSE changes bytes the goldens
never cover — but note the optimized path has **no cargo-CI byte gate at all**; its
only result checks are the out-of-CI unicorn differential + the on-target gate. So
"frozen-safe" is a constraint the impl must hold to (don't let the CSE leak into the
relocatable lowering), not a free property — and the optimized-path result evidence
is the differential, not a cargo test.

## Implemented — `SYNTH_BASE_CSE` (flag-off)

The scoping spike above anticipated "reserve a callee-saved base reg, hoist
`movw/movt` once per straight-line run." The implementation found a cleaner,
stronger invariant and is **simpler** than the per-run plan:

* **R11 is realloc-immune.** `reallocate_function`'s pool is `R0–R8`; it
  identity-preserves everything outside it. So the base lives in **R11**,
  materialized **once at function entry**, and survives every later segment
  untouched — no per-run re-materialization, no cross-segment remap hazard. R11
  is also outside local promotion's `R4–R8` pool and is not the encoder scratch
  (R12). It is reserved from every optimized-path allocator via
  `param_reserved_regs` + the const pool.
* **Const addresses fold into the access immediate.** `i32.store (i32.const ADDR)
  V` → `str V,[R11,#ADDR+off]` (planner-verified single-use const address,
  `ADDR+off ≤ imm12`), dropping the per-access `movw/movt` base **and** the now-
  dead address materialization — the latter is the register-pressure relief that
  makes the reserved base a net win, not a wash.
* **A standalone planner** (`plan_base_cse`, unit-tested) decides activation:
  ≥2 foldable const-address accesses AND every opcode in the base-CSE-safe set.
  Any `Branch`/`CondBranch` (multi-block), `Select`, `Global*`, `MemorySize/Grow`,
  `Call`, i64, or unenumerated op declines the whole function (`None` → unchanged
  per-access codegen). v1 is therefore confined to single-basic-block field
  initializers — #468's exact target — keeping it clear of the optimized path's
  separately-tracked multi-block lowering.

Result on `init_fields`: **.text 336 B → 218 B (−118 B, −35 %)**, base
materialized once, all 7 addresses folded, matching the relocatable path's
`str [fp,#off]` shape.

### Oracle (this path has NO cargo byte-gate — frozen gate compiles `--relocatable`)

1. **Flag-off bit-identical** — verified by an explicit `.text` diff of a fixture
   corpus against a pre-change baseline binary (4/4 identical), plus the full
   optimized-path test suite (`wast_compile` et al.) green. base-CSE is `None`
   when the flag is unset, so off ⇒ byte-identical by construction.
2. **Differential** (`base_cse_differential.py`, unicorn): `init_fields`
   flag-off == flag-on == wasmtime by comparing **linear memory** (the fixture
   returns nothing); `init_branch` asserts flag-on `.text` byte-identical to
   flag-off (base-CSE correctly **declines** on control flow).
3. **On-target cycle gate** (same protocol as the prior levers), then default-on
   flip via a `SYNTH_NO_BASE_CSE` opt-out — **held for silicon**.

### Follow-ups
* Multi-block support (needs the optimized path's `block`/`br_if` lowering fixed
  first — `init_branch` flag-off already miscompiles, independent of base-CSE; a
  separate optimized-path control-flow bug worth its own issue).
* Dynamic (non-const) addresses in an active function could still source the base
  from R11 (`add R12,R11,r_addr`) instead of re-materializing — deferred.
