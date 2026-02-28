# Synth Proof Contributor Guide

## Prerequisites

- [Rocq 9.0](https://rocq-prover.org/) (formerly Coq) installed via opam
- Familiarity with basic functional programming
- Recommended reading: [Software Foundations Vol. 1](https://softwarefoundations.cis.upenn.edu/)

## Architecture

```
Synth/
  Common/        -- Shared definitions: integers, base tactics, state monad
  ARM/           -- ARM processor model: state, instructions, semantics
  WASM/          -- WebAssembly model: values, instructions, stack semantics
  Synth/         -- Compilation function and correctness proofs
  Extraction/    -- OCaml code extraction directives
```

The dependency graph flows downward: `Synth/` imports everything above it.

## Custom Tactics

The file `Synth/Tactics.v` provides automation for common proof patterns:

| Tactic | Use Case | What It Does |
|--------|----------|-------------|
| `synth_binop_proof` | Binary operations (add, sub, mul, and, or, xor) | Intros, unfolds `compile_wasm_to_arm` and `exec_program`, rewrites register hypotheses, closes with `get_set_reg_eq` |
| `synth_comparison_proof` | Comparison operations producing booleans | Similar to `synth_binop_proof` but tuned for comparison result patterns |
| `synth_unop_proof` | Unary operations (clz, ctz, popcnt, eqz) | Single-operand variant of `synth_binop_proof` |
| `synth_simplify` | Manual proofs | Unfolds all execution and stack operations |
| `synth_destruct_stack` | Manual proofs | Rewrites the stack hypothesis and simplifies |
| `synth_solve` | Manual proofs | Tries `reflexivity`, `get_set_reg_eq`, `ring` |
| `synth_auto` | Exploratory | Chains `synth_simplify`, `synth_destruct_stack`, `synth_solve` |

## Proof Structure

Every correctness theorem follows this pattern:

```coq
Theorem compile_<op>_correct :
  forall wstate astate v1 v2 stack',
    (* Precondition: WASM stack has operands *)
    wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
    (* Precondition: ARM registers hold operands *)
    get_reg astate R0 = v1 ->
    get_reg astate R1 = v2 ->
    (* Precondition: WASM execution succeeds *)
    exec_wasm_instr <WasmOp> wstate = Some (...) ->
    (* Postcondition: ARM execution produces matching result *)
    exists astate',
      exec_program (compile_wasm_to_arm <WasmOp>) astate = Some astate' /\
      get_reg astate' R0 = <expected_result>.
```

## Worked Example: Closing an Admitted Proof

Suppose `CorrectnessI32.v` contains:

```coq
Theorem compile_i32_xor_correct : forall wstate astate v1 v2 stack',
  wstate.(stack) = VI32 v2 :: VI32 v1 :: stack' ->
  get_reg astate R0 = v1 ->
  get_reg astate R1 = v2 ->
  exec_wasm_instr I32Xor wstate = Some (...) ->
  exists astate', ...
Proof.
  admit.
Admitted.
```

To close it:

1. **Check that `Compilation.v` has a real compilation case** for `I32Xor`:
   ```coq
   | I32Xor => [Eor R0 R0 (OpReg R1)]
   ```
   If the case returns `[]` or a placeholder, the proof cannot close yet.

2. **Replace the proof body** with the automation tactic:
   ```coq
   Proof.
     synth_binop_proof.
   Qed.
   ```

3. **Build** to verify: `make` from the `coq/` directory.

If `synth_binop_proof` doesn't close it (e.g., multi-instruction sequences), use the manual approach:

```coq
Proof.
  intros wstate astate v1 v2 stack' Hstack HR0 HR1 Hwasm.
  unfold compile_wasm_to_arm.
  unfold exec_program, exec_instr. simpl.
  rewrite HR0, HR1.
  eexists. split.
  - reflexivity.
  - simpl. apply get_set_reg_eq.
Qed.
```

## Contributing a New Proof

1. Check `coq/STATUS.md` for the current triage -- pick a theorem from "Closable Now".
2. Open the corresponding `Correctness*.v` file.
3. Find the `Admitted` proof and check the compilation case in `Compilation.v`.
4. Replace `admit. Admitted.` with the appropriate tactic and `Qed.`
5. Run `make` to verify the proof compiles.
6. Update `coq/STATUS.md` counts.
7. Submit a PR with the title: `proof: close <theorem_name> in <file>`

## Building

```bash
cd coq/
make          # Build all proofs
make clean    # Remove build artifacts
make validate # Check for remaining Admitted
```

## Common Pitfalls

- **Compilation returns `[]`**: The proof cannot close if `compile_wasm_to_arm` maps the instruction to an empty list. Fix the compilation case first.
- **Register read-after-write**: Multi-instruction proofs need `get_set_reg_eq` (same register) and `get_set_reg_neq` (different register) lemmas from `ArmState.v`.
- **`simpl` diverges**: Use `cbn` or targeted `unfold` instead of `simpl` when terms are large.
- **Axiom dependencies**: Some proofs depend on axioms in `Integers.v` (e.g., `div_mul_rem`). These are sound modeling axioms but cannot be `Qed`'d until the axioms themselves are proven.
