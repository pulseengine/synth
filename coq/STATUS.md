# Synth Rocq Proof Suite -- Status

Last audited: 2026-02-20

## Numbers at a Glance

| Metric                 | Value   |
|------------------------|---------|
| `.v` files             | 23      |
| Total lines            | 6 596   |
| `Qed.` (closed proofs)| 106     |
| `Admitted.` (open)     | 122     |
| Axioms (in Integers.v) | 10     |
| Proof-to-admit ratio   | 0.87:1  |

Note: "Axioms" count the `Axiom` declarations in `Common/Integers.v` for
`clz`, `ctz`, `popcnt` (I32 and I64), their range properties, and the
division/remainder formulas.  These are modeling axioms, not proof holes.

---

## Per-File Matrix

### Infrastructure (no correctness proofs expected)

| File | Lines | Qed | Admitted | Status |
|------|------:|----:|---------:|--------|
| `Common/Base.v`              | 128 | 4  | 0 | Complete |
| `Common/Integers.v`         | 346 | 9  | 2 | Partial -- `add_zero`, `i64_to_i32_to_i64_wrap` admitted; 10 axioms |
| `Common/StateMonad.v`       |  64 | 3  | 0 | Complete |
| `ARM/ArmInstructions.v`     | 155 | 0  | 0 | Complete (definitions only) |
| `ARM/ArmState.v`            | 237 | 6  | 0 | Complete |
| `ARM/ArmSemantics.v`        | 412 | 5  | 2 | Partial -- `exec_preserves_other_regs`, `add_zero_right` admitted |
| `ARM/ArmRefinement.v`       | 168 | 0  | 2 | Placeholder -- Sail integration pending |
| `WASM/WasmInstructions.v`   | 206 | 0  | 0 | Complete (definitions only) |
| `WASM/WasmSemantics.v`      | 664 | 6  | 0 | Complete |
| `WASM/WasmValues.v`         | 107 | 2  | 0 | Complete |
| `Extraction/CompilerExtract.v` | 94 | 0 | 0 | Complete (extraction directives only) |

### Compilation

| File | Lines | Qed | Admitted | Status |
|------|------:|----:|---------:|--------|
| `Synth/Compilation.v`       | 640 | 3  | 2 | Partial -- 2 example `compile_wasm_program` lemmas admitted |
| `Synth/Tactics.v`           | 137 | 1  | 0 | Complete |

### Correctness Proofs

| File | Lines | Qed | Admitted | Status |
|------|------:|----:|---------:|--------|
| `Synth/Correctness.v`               | 280 |  6 |  0 | Complete -- i32 add/sub/mul/and/or/xor |
| `Synth/CorrectnessSimple.v`         | 580 | 27 |  2 | Partial -- `local_get`, `local_set` admitted |
| `Synth/CorrectnessI32.v`            | 506 |  8 | 21 | Partial -- 8 Qed (add/sub/mul/divs/divu/and/or/xor), 21 admitted |
| `Synth/CorrectnessI64.v`            | 374 |  0 | 29 | Placeholder -- all 29 theorems admitted |
| `Synth/CorrectnessI64Comparisons.v` | 366 | 19 |  0 | Complete -- 11 comparisons + 3 bit-manip + 5 shift/rotate |
| `Synth/CorrectnessConversions.v`    | 278 |  0 | 21 | Placeholder -- all conversions admitted |
| `Synth/CorrectnessF32.v`            | 209 |  0 | 20 | Placeholder -- all f32 ops admitted |
| `Synth/CorrectnessF64.v`            | 209 |  0 | 20 | Placeholder -- all f64 ops admitted |
| `Synth/CorrectnessMemory.v`         | 100 |  0 |  8 | Placeholder -- all memory ops admitted |
| `Synth/CorrectnessComplete.v`       | 336 |  0 |  0 | Index file (no proofs, re-exports other modules) |

---

## Admitted Proof Triage

### Category 1 -- Closable Now (pattern already exists)

These follow the exact same `synth_binop_proof` or manual unfold/rewrite
pattern already demonstrated by the proven proofs in the same file, but the
proof body says `admit.` instead of applying the tactic.

| Theorem | File | Blocker |
|---------|------|---------|
| `i32_shl_correct` | CorrectnessI32.v | Shift compilation uses placeholder `LSL R0 R0 0`; once the compile case emits a real operand, `synth_binop_proof` closes it |
| `i32_shru_correct` | CorrectnessI32.v | Same as shl |
| `i32_shrs_correct` | CorrectnessI32.v | Same as shl |
| `i32_rotl_correct` | CorrectnessI32.v | Compilation emits `[]`; once non-empty, proof follows rotr pattern |
| `i32_rotr_correct` | CorrectnessI32.v | `ROR R0 R0 0` placeholder; real operand needed |

Estimated effort: 1-2 days once `Compilation.v` shift cases are fixed.

### Category 2 -- Needs Multi-Instruction Reasoning

Proofs that involve a 2+ instruction ARM sequence and need intermediate
state lemmas (e.g., `exec_program_app`).

| Theorem | File | Notes |
|---------|------|-------|
| `i32_rems_correct` | CorrectnessI32.v | SDIV + MLS; proof is 80% written, stuck on register read-after-write through `set_reg` |
| `i32_remu_correct` | CorrectnessI32.v | UDIV + MLS; same blocker |
| `i32_eqz_correct` (strong form) | CorrectnessI32.v | CMP + MOV + MOVEQ; needs flag-aware reasoning |
| All 10 i32 comparison (strong form) | CorrectnessI32.v | CMP + MOV + MOVcc; needs conditional-move semantics chain |

Estimated effort: 3-5 days for remainder pair, 5-10 days for comparisons.

### Category 3 -- Needs Register-Pair / 64-bit Work (i64)

All 29 admits in `CorrectnessI64.v`.  These mirror the i32 pattern but the
current compilation (`Compilation.v`) treats i64 as low-32-bit only.
Full correctness requires a register-pair model (`R0:R1` for first operand,
`R2:R3` for second).

Estimated effort: 3-5 days infrastructure + 1 day per operation.

### Category 4 -- Floating-Point (f32, f64)

All 40 admits in `CorrectnessF32.v` and `CorrectnessF64.v`.  Blocked on:

1. IEEE 754 semantics -- need Flocq library integration.
2. VFP instruction semantics in `ArmSemantics.v` are stubs (`Some s`).
3. Theorem statements use placeholder results (`I32.zero` / `I64.zero`).

Estimated effort: 2-4 weeks for Flocq integration; 1-2 days per operation
after that.

### Category 5 -- Conversion Operations

All 21 admits in `CorrectnessConversions.v`.
- Integer conversions (3): `i32_wrap_i64`, `i64_extend_i32_s/u` -- closable
  once the compilation cases emit real code (currently `[]`).
- Float<->Int conversions (16): blocked on Flocq + VFP semantics.
- Float promotions (2): blocked on Flocq.

### Category 6 -- Memory Operations

All 8 admits in `CorrectnessMemory.v`.  The memory model (`Z -> I32.int`)
exists and `load_store_mem_eq/neq` are proven.  Blockers:

- Load proofs need the `LDR` semantics path through `exec_instr` connected
  to the WASM `memory` field.
- Store proofs need the `STR` path + proof that `store_mem` matches WASM
  memory update.

Estimated effort: 3-5 days.

### Category 7 -- Modeling Gaps (Axioms, not Admitted)

| Axiom | File | Risk |
|-------|------|------|
| `I32.clz`, `I32.ctz`, `I32.popcnt` | Integers.v | Low -- well-understood bit ops, provable with `Zdigits` |
| `I64.clz`, `I64.ctz`, `I64.popcnt` | Integers.v | Same |
| `div_mul_rem_{unsigned,signed}` | Integers.v | Medium -- standard Z arithmetic, tedious but straightforward |
| `remu_formula`, `rems_formula` | Integers.v | Medium -- follows from division properties |
| `SailARM.sail_exec_instr` | ArmRefinement.v | High -- placeholder for Sail-generated code |

### Misc Admitted

| Theorem | File | Notes |
|---------|------|-------|
| `I32.add_zero` | Integers.v | Trivial; needs `Z.mod_small` + `Z.add_0_r` |
| `i64_to_i32_to_i64_wrap` | Integers.v | Straightforward modular arithmetic |
| `exec_preserves_other_regs` | ArmSemantics.v | Needs `get_set_reg_neq` path |
| `add_zero_right` | ArmSemantics.v | Depends on `I32.add_zero` |
| `local_get_correct` | CorrectnessSimple.v | Needs register-to-local correspondence lemma |
| `local_set_correct` | CorrectnessSimple.v | Same |
| `ex_compile_simple_add` | Compilation.v | Example; needs `simpl` + `reflexivity` after list unfolding |
| `ex_compile_increment_local` | Compilation.v | Same pattern |

---

## Next Targets (recommended order)

1. **Close `I32.add_zero`** and the two `ArmSemantics.v` admits that depend
   on it.  These are one-liners that improve the ratio immediately.

2. **Fix shift compilation** in `Compilation.v` (replace `0` placeholders
   with `(I32.repr (unsigned y mod 32))`-style operands), then close the 5
   i32 shift/rotate admits in `CorrectnessI32.v`.

3. **Write a `synth_3instr_comparison_proof` tactic** that handles the
   CMP + MOV + MOVcc pattern, then close all 11 i32 comparison admits in
   `CorrectnessI32.v`.

4. **Close `i32_rems_correct` and `i32_remu_correct`** using
   `exec_program_app` + `get_set_reg_neq`.

5. **Prove `local_get_correct` and `local_set_correct`** in
   `CorrectnessSimple.v` by adding a register-local correspondence lemma.

6. **Tackle memory operations** -- straightforward once the LDR/STR
   semantics path is connected.

7. **i64 register-pair model** -- infrastructure investment that unblocks 29
   admits.

8. **Flocq integration** -- unblocks all 40 floating-point and 16
   float-conversion admits.
