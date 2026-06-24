# #468 scoping spike — redundant linear-memory-base materialization

**Issue:** synth#468 · **Epic:** #242 (VCR-*) · north-star #390
**Status:** SCOPING SPIKE (no codegen change — frozen-safe by construction).
The byte-changing CSE is the explicitly-separate next gated step (flag-off →
on-target cycle gate → default-on flip), exactly like the cmp→select /
local-promotion / immediate-shift levers.

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

## Next gated step (separate PR)

1. Flag-off CSE in `optimizer_bridge.rs` (`SYNTH_BASE_CSE`, default off ⇒
   bit-identical optimized path) — reserve a callee-saved base reg, hoist
   `movw/movt` once per const-base store-run, rewrite stores to `[base,#off]`.
   Soundness: only runs of stores whose base is the same compile-time constant
   with no intervening base clobber; base reg dead-after / restored in epilogue.
2. Differential (unicorn): optimized-path ELF, flag-off == flag-on == wasmtime;
   the 7-store fixture is the non-vacuity case.
3. On-target cycle gate (same protocol as the prior levers), then default-on flip
   + re-freeze any optimized-path goldens it touches.
