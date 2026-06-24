# Optimized-path ABI model — and the #470 determination

**Issue:** #470 (resolved here) · **Epic:** #242 (VCR-*) · context: VCR-RA-002 (#428)
**Status:** ANALYSIS / determination — no codegen change, frozen-safe.

## Question

#470 asked: the optimized (non-relocatable) path emits an **exported** leaf that
clobbers callee-saved r4-r8 with `bx lr` and **no push** — is that an AAPCS
violation?

## Determination: by-design, not a bug

synth has **two ABI models**, selected by `--relocatable`:

| | optimized (default, non-reloc) | `--relocatable` |
|---|---|---|
| codegen | `OptimizerBridge::ir_to_arm` | `select_with_stack` (direct selector) |
| linmem base | absolute const (0x20000100) | `fp`-relative (arrives at runtime) |
| AAPCS | **no** — by design | **yes** |
| use | self-contained bare-metal image (synth controls all callers) | host-link ET_REL / external AAPCS callers |

This is documented in `arm_backend.rs`: the optimized path *"does not preserve
caller-saved registers across calls — both wrong for a host-linked object, where
the linmem base arrives via `fp` at runtime and callees follow AAPCS."* The
callee-saved clobber is the same fact one level deeper: `ir_to_arm`'s
prologue/epilogue logic only frames on a spill (never emits a callee-saved
`push`), and its temp pool prefers r4-r8 (`CANDIDATES = [R4..R8]`), so optimized
leaves use and clobber callee-saved registers.

## Why the self-contained model is self-consistent (verified)

`intra_module_callee_saved.wat` is the evidence. A call-containing function is
**declined by the optimizer** (it only optimizes leaves) and falls back to the
**direct selector**, which:

- holds values live across a call on the **frame**, not in registers — caller
  `a` does `str.w r3,[sp]` before `bl $b` and `ldr.w r5,[sp]` after, so it never
  relies on `$b` preserving r4-r8;
- `push {r4-r8,lr}` / `pop {…,pc}` to preserve callee-saved for **its** caller.

So an optimized leaf (`$b`: clobbers r4,r5,r6, no push) corrupts nothing — every
caller in a self-contained image spills across calls. Confirmed on
`-b arm --target cortex-m4` (non-relocatable).

The only exposure is an **external AAPCS caller** holding live r4-r8 across the
boundary — exactly the host-link case, for which `--relocatable` is the required,
documented path. No fix to the optimized path is warranted.

## Consequence for VCR-RA-002 (#428)

This also resolves the baseline worry flagged in the VCR-RA-002 spike (#471): the
`push {r4-r8,lr}` measured on-target lives on the **call-containing / relocatable**
path (direct selector), **not** optimized leaves (which have no push by design).
So #470 does **not** reset VCR-RA-002's baseline — the prologue-shrink lever
targets the direct-selector / relocatable prologue, which is correct to shrink
when the body provably uses no callee-saved register.
