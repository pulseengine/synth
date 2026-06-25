# #472 scoping spike — port the ARM perf levers to the RISC-V backend

**Issue:** synth#472 · **Epic:** #242 (VCR-*) · north-star #390
**Status:** SCOPING SPIKE (no codegen change — frozen-safe by construction).
The byte-changing lever ports are the explicitly-separate next gated steps
(flag-off → RV32 differential → qemu_riscv32 / ESP32-C3 cycle gate → default-on
flip), exactly like the ARM cmp→select / local-promotion / imm-shift / dead-frame /
base-CSE levers.

## The gap

The RV32 backend lags the ARM backend on dissolved code: the ARM perf levers that
landed v0.13–v0.15 (cmp→select, local-promotion, immediate-shift-fold, dead-frame
elimination, base-CSE) have **no RV32 equivalent yet**. #472 asks: port the
applicable levers to `synth-backend-riscv` so RV32 closes the same per-function
overhead the ARM levers removed.

**Load-bearing finding — the port is NOT a 1:1 mapping of all three named levers.**
Read against the RV32IMAC backend source, one lever does not apply, one applies
directly, one applies in a RISC-V-specific form, and there is a fourth,
RISC-V-only opportunity the ARM base-CSE work surfaced.

## Lever-by-lever (source-grounded in `crates/synth-backend-riscv/src/selector.rs`)

### 1. cmp→select → **N/A for RV32IMAC**

`lower_select` (selector.rs:930) emits the branchy form — `bne cond,zero,La;
mv dst,b; j Lend; La: mv dst,a; Lend:` (5 instructions for an i32 select). This is
**already the minimal correct lowering**: RV32IMAC has **no conditional-move**
(`czero.*` is the Zicond extension, not in IMAC; there is no predication like ARM's
IT block). The ARM lever fused cmp→select into IT-predicated moves — there is no
RV32IMAC instruction to fuse into. **Conclusion:** skip for the base ISA. A future,
separate item could exploit branchless idioms for *special* selects (select-vs-0
via `seqz`/`neg`/`and` masking; or Zicond when targeting a core that has it), but
that is not a port of the ARM lever and is out of #472's scope.

### 2. local-promotion → **APPLIES (direct analogue of ARM #390)**

Non-param i32 locals are **always frame-spilled**: `local.set` emits
`sw src, off(sp)` and `local.get` emits `lw dst, off(sp)` (selector.rs:1070-1090,
~1023). A leaf function pays `sw`+`lw` traffic for every local access where a
callee-saved register would do — exactly the ARM #390 situation. RV32 has a
generous register file (s1–s11 callee-saved, t0–t6 temps), so leaf locals can be
register-promoted with no prologue cost beyond the existing `preserve_callee_saved`
save (selector.rs:307,317), which already brackets touched callee-saved regs.
**Port:** the ARM `compute_local_promotion` shape (i32, write-before-read, depth-0,
≥2 reads, leaf-only) maps directly; home eligible locals in s-registers instead of
frame slots.

### 3. immediate-shift-fold → **APPLIES (RISC-V-specific form)**

`I32Shl/ShrS/ShrU` lower through `bin` (selector.rs:1184) to the **register** shift
forms `sll/sra/srl` (selector.rs:739). A constant shift amount is first
materialized into a register (`i32.const N` → `emit_load_imm` = `li tmp,N`), then
consumed as `rs2`. RV32 has immediate shift forms `slli/srli/srai` (shamt in the
instruction) — folding a constant shift amount into them drops the `li tmp,N`.
**Port:** when the shift-amount operand is a known `i32.const` in `[0,31]`, emit
`slli/srli/srai rd, rs1, #N` instead of `li tmp,N; sll rd,rs1,tmp` — saves one
instruction per constant shift. (`Slli/Srli/Srai` ops already exist in the op enum,
selector.rs:233-235 — only the selector wiring is missing.)

### 4. const-address-fold → **APPLIES (RISC-V-only; the base-CSE analogue)**

The ARM base-CSE lever (#468) had two halves: (a) hoist the re-materialized
linear-memory base, and (b) fold constant store/load addresses into the access
immediate. **Half (a) does not exist on RV32** — the base already lives
persistently in `s11`/x27 (`LINEAR_MEM_BASE`, selector.rs:137); it is never
re-materialized. But **half (b) is missing**: `lower_load_word`/`lower_store_word`
(selector.rs:1493+) unconditionally emit `add tmp, s11, addr; lw/sw dst, off(tmp)`,
where `addr` for a constant address is a `li`'d register. For a constant address
with `ADDR+offset` in the 12-bit signed `lw/sw` immediate window, this folds to
`lw/sw dst, (ADDR+offset)(s11)` — dropping **both** the `li addr,ADDR` and the
`add tmp,s11,addr` (2 instructions per constant-address access).

## Measured sizes (`.text`, this spike's fixtures + the existing corpus)

| fixture | ARM `.text` | RV32 `.text` | RV32 lever headroom |
|---|---:|---:|---|
| `redundant_base_materialization` (7 const-addr stores) | 336 B | 120 B (30 insn) | const-addr-fold: ~2 insn × 7 = **~56 B** |
| `leaf_caller_saved` (1 param + 3 i32 locals) | 200 B | 104 B (26 insn) | local-promotion: the `sw`/`lw` local traffic |
| `shifts` (2 const shifts) | 188 B | 44 B (11 insn) | imm-shift-fold: 1 `li` × 2 = **~8 B** |

(RV32 `.text` is already smaller than ARM in absolute bytes — RV32 is a 4-byte
fixed encoding vs Thumb-2's mixed 2/4, and these leaves avoid ARM's `movw/movt`
base materialization. The lever headroom is the RV32-vs-RV32 win — the per-function
overhead removed — which is what the on-target cycle ratio reflects.)

## Must carry from the start: the #474 promotion-exhaustion fallback

ARM local-promotion shipped a v0.15.1 fix (#474): promotion must **never** cause a
compile failure — when register pressure exhausts the promotable pool, fall back to
the frame-slot path rather than erroring. The RV32 local-promotion port must carry
the same fallback by construction: if the s-register budget is exhausted, the local
stays frame-slotted (the current, correct path). The RV32 selector already has an
`alloc_exhausted` → `Unsupported` → skip-and-continue mechanism (#226) to model
this against.

## Gated implementation plan (each a separate PR)

1. **imm-shift-fold** (smallest, self-contained): const shift amount → `slli/srli/
   srai`. Flag-off → RV32 differential → cycle gate → flip.
2. **const-address-fold**: const `lw/sw` address → fold into the access immediate
   off `s11`. Flag-off → RV32 differential → cycle gate → flip.
3. **local-promotion**: port `compute_local_promotion` to s-registers, leaf-only,
   carrying the #474 fallback. Flag-off → RV32 differential → cycle gate → flip.
4. (cmp→select: out of scope for RV32IMAC — see above.)

**Oracle note:** the RV32 path has no cargo byte-gate and (unlike ARM) no local
RISC-V disassembler on the dev host. The differential will need an RV32 execution
harness (unicorn `UC_ARCH_RISCV` or qemu_riscv32, comparing against wasmtime), and
a small RV32 instruction decoder for byte-level assertions — built as part of step 1.
The final cycle win is validated on qemu_riscv32 / ESP32-C3, the same on-target
protocol as the ARM cycle gate.
