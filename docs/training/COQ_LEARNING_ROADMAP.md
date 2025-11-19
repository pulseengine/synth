# Coq Learning Roadmap for Synth Team

**Purpose**: Transform the Synth development team into competent Coq verification engineers capable of proving correctness of WebAssembly-to-ARM compilation.

**Target Audience**: Software engineers with strong systems programming background (Rust/C++) but no formal methods experience.

**Timeline**: 3 months to productive; 6 months to proficient; 12 months to expert

---

## Table of Contents

1. [Prerequisites](#prerequisites)
2. [Learning Phases](#learning-phases)
3. [Resources](#resources)
4. [Synth-Specific Training](#synth-specific-training)
5. [Team Structure](#team-structure)
6. [Progress Tracking](#progress-tracking)
7. [Common Pitfalls](#common-pitfalls)

---

## Prerequisites

### Required Background

✅ **You have:**
- Strong Rust/C++ programming experience
- Understanding of ARM assembly
- Understanding of WebAssembly semantics
- Familiarity with mathematical proofs (high school algebra level is sufficient)
- Comfort with recursion and inductive data structures

❌ **You don't need:**
- PhD in formal methods
- Category theory knowledge
- Haskell experience (helpful but not required)
- Prior theorem prover experience

### Environment Setup

```bash
# Install Coq 8.18+ (latest stable)
sudo apt-get install opam
opam init
opam install coq coqide

# Install useful Coq libraries
opam install coq-mathcomp-ssreflect
opam install coq-ext-lib
opam install coq-stdpp

# Verify installation
coqc --version  # Should show 8.18 or later

# Install VSCode + Coq plugin (alternative to CoqIDE)
code --install-extension maximedenes.vscoq
```

---

## Learning Phases

### Phase 0: Foundations (Week 1-2) - 20 hours

**Goal**: Understand basic Coq syntax and proof tactics.

#### Day 1-3: Coq Basics
- **Read**: Software Foundations Vol 1 (Logical Foundations) - Chapters 1-3
  - Basics: Functional programming in Coq
  - Induction: Proof by induction
  - Lists: Polymorphic lists and higher-order functions

- **Practice**:
  ```coq
  (* Exercise 1: Write simple recursive functions *)
  Fixpoint factorial (n : nat) : nat :=
    match n with
    | O => 1
    | S n' => n * factorial n'
    end.

  (* Exercise 2: Prove basic properties *)
  Theorem factorial_positive : forall n, factorial n > 0.
  Proof.
    induction n.
    - simpl. omega.
    - simpl. omega.
  Qed.
  ```

#### Day 4-7: Tactics and Proof Strategies
- **Read**: Software Foundations Vol 1 - Chapters 4-6
  - Tactics: Basic tactics (intro, apply, rewrite)
  - Logic: Propositional and predicate logic
  - IndProp: Inductively defined propositions

- **Practice**:
  ```coq
  (* Exercise 3: Practice common tactics *)
  Theorem example_proof : forall (P Q R : Prop),
    (P -> Q) -> (Q -> R) -> P -> R.
  Proof.
    intros P Q R HPQ HQR HP.
    apply HQR.
    apply HPQ.
    exact HP.
  Qed.
  ```

**Checkpoint**: Can you prove simple list properties without looking at solutions?

---

### Phase 1: Intermediate Coq (Week 3-6) - 40 hours

**Goal**: Master common proof patterns and data structure reasoning.

#### Week 3-4: Advanced Tactics
- **Read**: Software Foundations Vol 1 - Chapters 7-10
  - Maps: Total and partial maps
  - Imp: Simple imperative language
  - ImpParser: Lexing and parsing
  - ImpCEvalFun: Evaluation as a function

- **Focus on**:
  - `destruct` with patterns
  - `inversion` for impossible cases
  - `assert` for intermediate lemmas
  - `remember` for complex terms
  - `auto` and `eauto` for automation

- **Practice**:
  ```coq
  (* Exercise 4: Prove map properties *)
  Definition total_map (A : Type) := nat -> A.

  Definition update {A : Type} (m : total_map A) (x : nat) (v : A) :=
    fun x' => if x =? x' then v else m x'.

  Theorem update_eq : forall (A : Type) (m : total_map A) x v,
    (update m x v) x = v.
  Proof.
    intros. unfold update.
    rewrite Nat.eqb_refl. reflexivity.
  Qed.

  Theorem update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (update m x1 v) x2 = m x2.
  Proof.
    intros. unfold update.
    rewrite Nat.eqb_neq in H.
    destruct (x1 =? x2) eqn:E.
    - contradiction.
    - reflexivity.
  Qed.
  ```

#### Week 5-6: State and Semantics
- **Read**: Software Foundations Vol 2 (Programming Language Foundations) - Chapters 1-4
  - Equiv: Program equivalence
  - Hoare: Hoare logic basics
  - Hoare2: Hoare logic with assertions
  - Smallstep: Small-step operational semantics

- **Practice**:
  ```coq
  (* Exercise 5: Simple machine state *)
  Record machine_state := {
    reg0 : nat;
    reg1 : nat;
    reg2 : nat;
    mem : nat -> nat
  }.

  Inductive instruction :=
  | ADD (rd rs : nat)
  | LOAD (rd : nat) (addr : nat)
  | STORE (addr : nat) (rs : nat).

  Definition step (i : instruction) (s : machine_state) : machine_state :=
    match i with
    | ADD rd rs =>
        match rd, rs with
        | 0, 0 => {| reg0 := s.(reg0) + s.(reg0);
                     reg1 := s.(reg1);
                     reg2 := s.(reg2);
                     mem := s.(mem) |}
        | 0, 1 => {| reg0 := s.(reg0) + s.(reg1);
                     reg1 := s.(reg1);
                     reg2 := s.(reg2);
                     mem := s.(mem) |}
        (* ... etc *)
        | _, _ => s
        end
    (* ... other cases *)
    | _ => s
    end.

  (* Prove properties about instruction sequences *)
  Theorem add_commutative : forall s rd rs1 rs2,
    step (ADD rd rs1) (step (ADD rd rs2) s) =
    step (ADD rd rs2) (step (ADD rd rs1) s).
  Proof.
    (* This would be false in general - good exercise to find counterexample *)
  Admitted.
  ```

**Checkpoint**: Can you define a simple imperative language and prove basic semantic properties?

---

### Phase 2: Verification Patterns (Week 7-10) - 60 hours

**Goal**: Apply Coq to real compiler verification scenarios.

#### Week 7-8: CompCert Study
- **Read**: [CompCert C Compiler](https://github.com/AbsInt/CompCert)
  - `lib/Coqlib.v`: Common utilities and tactics
  - `common/Values.v`: Machine integers and values
  - `common/Memory.v`: Memory model
  - `backend/Registers.v`: Register allocation

- **Study Patterns**:
  ```coq
  (* Pattern 1: Simulation diagrams *)
  Definition simulation (sem1 sem2 : semantics) : Prop :=
    forall s1 t s1',
      step sem1 s1 t s1' ->
      exists s2', step sem2 s1 t s2' /\ match_states s1' s2'.

  (* Pattern 2: Backward simulations for optimization *)
  Definition backward_simulation (sem1 sem2 : semantics) : Prop :=
    forall s2 t s2',
      step sem2 s2 t s2' ->
      exists s1', step sem1 s1 t s1' /\ match_states s1' s2'.

  (* Pattern 3: Determinacy lemmas *)
  Lemma step_deterministic : forall sem s t1 s1' t2 s2',
    step sem s t1 s1' ->
    step sem s t2 s2' ->
    t1 = t2 /\ s1' = s2'.
  ```

#### Week 9-10: CakeML ARM Backend Study
- **Read**: [CakeML ARM backend](https://github.com/CakeML/cakeml)
  - `compiler/backend/arm8/arm8_targetScript.sml`: ARM8 target definition
  - `compiler/backend/arm8/arm8_targetProofScript.sml`: Correctness proofs
  - `compiler/encoders/arm8/arm8_compilerProofScript.sml`: Encoding proofs

- **Translate HOL4 → Coq**:
  ```coq
  (* HOL4 style *)
  Theorem arm8_add_correct:
    !r1 r2 rd s.
      evaluate_instr (Add rd r1 r2) s =
      let v1 = s.regs r1 in
      let v2 = s.regs r2 in
      s with regs updated_by ((rd =+ v1 + v2))

  (* Coq translation *)
  Theorem arm8_add_correct : forall r1 r2 rd s,
    evaluate_instr (Add rd r1 r2) s =
    let v1 := s.(regs) r1 in
    let v2 := s.(regs) r2 in
    update_reg s rd (v1 + v2).
  Proof.
    intros. unfold evaluate_instr. simpl.
    reflexivity.
  Qed.
  ```

**Checkpoint**: Can you prove a simple compiler transformation preserves semantics?

---

### Phase 3: Synth-Specific Training (Week 11-14) - 60 hours

**Goal**: Apply Coq to actual Synth WebAssembly-to-ARM verification.

#### Week 11: ARM Semantics in Coq

**Task**: Formalize 10 ARM instructions from `synth-verify/src/arm_semantics.rs`

```coq
(* File: synth-coq/theories/ArmSemantics.v *)

Require Import ZArith.
Require Import Coqlib.
Open Scope Z_scope.

(* ARM register file *)
Definition regfile := nat -> Z.

(* ARM state *)
Record arm_state := {
  regs : regfile;
  flags : nat;  (* NZCV flags *)
  pc : Z;
}.

(* ARM instructions *)
Inductive arm_instr :=
  | ADD (rd rn rm : nat)
  | SUB (rd rn rm : nat)
  | AND (rd rn rm : nat)
  | ORR (rd rn rm : nat)
  | EOR (rd rn rm : nat)
  | LSL (rd rn shift : nat)
  | LSR (rd rn shift : nat)
  | MOV (rd rm : nat)
  | CMP (rn rm : nat)
  | B (offset : Z).

(* Instruction semantics *)
Definition exec_instr (i : arm_instr) (s : arm_state) : arm_state :=
  match i with
  | ADD rd rn rm =>
      let v1 := s.(regs) rn in
      let v2 := s.(regs) rm in
      let result := v1 + v2 in
      {| regs := fun r => if Nat.eqb r rd then result else s.(regs) r;
         flags := s.(flags);
         pc := s.(pc) + 4 |}

  | SUB rd rn rm =>
      let v1 := s.(regs) rn in
      let v2 := s.(regs) rm in
      let result := v1 - v2 in
      {| regs := fun r => if Nat.eqb r rd then result else s.(regs) r;
         flags := s.(flags);
         pc := s.(pc) + 4 |}

  (* ... other instructions *)
  | _ => s  (* placeholder *)
  end.

(* Example property: ADD is commutative in source operands *)
Theorem add_commutative : forall rd rn rm s,
  rn <> rm ->
  exec_instr (ADD rd rn rm) s = exec_instr (ADD rd rm rn) s.
Proof.
  intros rd rn rm s Hneq.
  unfold exec_instr.
  f_equal.
  - extensionality r.
    destruct (Nat.eqb r rd); auto.
    ring.
  - reflexivity.
  - reflexivity.
Qed.
```

**Exercise**: Prove the following properties for each instruction:
1. Determinacy: Same input state → same output state
2. PC increment: Non-branch instructions increment PC by 4
3. Register preservation: Unmodified registers retain values

#### Week 12: WASM Semantics in Coq

**Task**: Formalize 10 WASM instructions from `synth-verify/src/wasm_semantics.rs`

```coq
(* File: synth-coq/theories/WasmSemantics.v *)

Require Import ZArith List.
Import ListNotations.

(* WASM values *)
Inductive wasm_val :=
  | I32 (n : Z)
  | I64 (n : Z)
  | F32 (f : float32)
  | F64 (f : float).

(* WASM stack machine state *)
Record wasm_state := {
  stack : list wasm_val;
  locals : nat -> wasm_val;
  memory : Z -> byte;
}.

(* WASM instructions *)
Inductive wasm_instr :=
  | I32Const (n : Z)
  | I32Add
  | I32Sub
  | I32Mul
  | I32And
  | I32Or
  | I32Xor
  | LocalGet (idx : nat)
  | LocalSet (idx : nat).

(* Instruction semantics *)
Definition exec_wasm (i : wasm_instr) (s : wasm_state) : option wasm_state :=
  match i with
  | I32Const n =>
      Some {| stack := I32 n :: s.(stack);
              locals := s.(locals);
              memory := s.(memory) |}

  | I32Add =>
      match s.(stack) with
      | I32 v2 :: I32 v1 :: rest =>
          Some {| stack := I32 (v1 + v2) :: rest;
                  locals := s.(locals);
                  memory := s.(memory) |}
      | _ => None  (* Type error *)
      end

  | I32Sub =>
      match s.(stack) with
      | I32 v2 :: I32 v1 :: rest =>
          Some {| stack := I32 (v1 - v2) :: rest;
                  locals := s.(locals);
                  memory := s.(memory) |}
      | _ => None
      end

  (* ... other instructions *)
  | _ => Some s  (* placeholder *)
  end.

(* Key property: Type preservation *)
Theorem i32_add_preserves_types : forall s s' v1 v2,
  s.(stack) = I32 v2 :: I32 v1 :: s'.(stack) ->
  exists v, exec_wasm I32Add s = Some {|
    stack := I32 v :: s'.(stack);
    locals := s.(locals);
    memory := s.(memory)
  |}.
Proof.
  intros s s' v1 v2 Hstack.
  exists (v1 + v2).
  unfold exec_wasm.
  rewrite Hstack.
  reflexivity.
Qed.
```

#### Week 13: Compilation Correctness

**Task**: Prove 5 WASM→ARM synthesis rules correct

```coq
(* File: synth-coq/theories/SynthCorrectness.v *)

Require Import ArmSemantics WasmSemantics.

(* Compilation function *)
Definition compile_wasm_to_arm (w : wasm_instr) : list arm_instr :=
  match w with
  | I32Add =>
      (* Assume: R0 = top of stack, R1 = second *)
      [ADD 0 0 1]

  | I32Sub =>
      [SUB 0 0 1]

  | I32And =>
      [AND 0 0 1]

  (* ... *)
  | _ => []
  end.

(* State correspondence *)
Definition states_match (ws : wasm_state) (as : arm_state) : Prop :=
  match ws.(stack) with
  | I32 v :: rest =>
      as.(regs) 0 = v  (* Top of WASM stack in R0 *)
  | _ => True
  end.

(* Main correctness theorem *)
Theorem compile_i32_add_correct : forall ws ws' as,
  exec_wasm I32Add ws = Some ws' ->
  states_match ws as ->
  exists as',
    exec_instr (ADD 0 0 1) as = as' /\
    states_match ws' as'.
Proof.
  intros ws ws' as Hwasm Hmatch.
  unfold exec_wasm in Hwasm.
  destruct ws.(stack) as [|v2 [|v1 rest]]; try discriminate.
  destruct v2 as [n2|]; try discriminate.
  destruct v1 as [n1|]; try discriminate.
  injection Hwasm as Hws'.
  subst ws'.

  (* Now prove ARM side *)
  exists (exec_instr (ADD 0 0 1) as).
  split.
  - reflexivity.
  - unfold states_match. simpl.
    unfold exec_instr. simpl.
    (* Need to prove: (R0 + R1) matches new stack top *)
    admit.  (* Exercise: complete this *)
Admitted.
```

**Exercise**: Complete the above proof and extend to:
- `I32Sub`
- `I32Mul`
- `I32And`
- `I32Or`

#### Week 14: Integration with Sail

**Task**: Study Sail-generated Coq and integrate with Synth proofs

```bash
# Get ARM specification in Sail
git clone https://github.com/rems-project/sail-arm
cd sail-arm

# Generate Coq from Sail
sail -coq -o arm_spec.v arm.sail

# Study the generated Coq
head -100 arm_spec.v
```

**Exercise**: Replace hand-written ARM semantics with Sail-generated semantics:

```coq
(* Before: Hand-written *)
Definition exec_instr (i : arm_instr) (s : arm_state) : arm_state :=
  match i with
  | ADD rd rn rm => (* manual encoding *)
  | ...
  end.

(* After: Use Sail-generated *)
Require Import arm_spec.  (* Generated from Sail *)

Definition exec_instr (i : arm_instr) (s : arm_state) : arm_state :=
  sail_arm_execute i s.  (* Use official ARM semantics *)
```

**Checkpoint**: Can you prove a complete WASM→ARM compilation rule using Sail-generated ARM semantics?

---

### Phase 4: Advanced Topics (Week 15-26) - 120 hours

**Goal**: Handle complex verification challenges.

#### Month 4-5: Floating Point

**Challenge**: IEEE 754 floating point is notoriously difficult to verify.

- **Read**: [Flocq library](http://flocq.gforge.inria.fr/)
  - `Fappli_IEEE.v`: IEEE 754 formalization
  - `Fprop_relative.v`: Relative error bounds
  - `Fcore_generic_fmt.v`: Generic floating-point formats

- **Practice**:
  ```coq
  Require Import Flocq.Core.Fcore.

  (* Prove: F32.add is commutative (up to rounding) *)
  Theorem f32_add_commutative : forall (x y : float32),
    is_finite x -> is_finite y ->
    F32.add x y = F32.add y x.
  Proof.
    intros x y Hx Hy.
    (* This requires deep understanding of Flocq *)
    admit.
  Admitted.
  ```

- **Synth Exercise**: Prove ARM `FADD` ≡ WASM `f32.add`

#### Month 5-6: Memory and Pointers

**Challenge**: Memory models are complex (aliasing, alignment, bounds).

- **Read**: CompCert Memory model (`common/Memory.v`)
  - `Mem.load`: Load from memory
  - `Mem.store`: Store to memory
  - `Mem.valid_pointer`: Pointer validity
  - `Mem.unchanged_on`: Unchanged memory regions

- **Practice**:
  ```coq
  (* Prove: Store then load returns stored value *)
  Theorem load_after_store : forall m addr chunk v m',
    Mem.store chunk m addr v = Some m' ->
    Mem.load chunk m' addr = Some v.
  Proof.
    intros. eapply Mem.load_store_same; eauto.
  Qed.

  (* Prove: Non-aliasing stores commute *)
  Theorem store_commute : forall m addr1 addr2 chunk1 chunk2 v1 v2,
    addr1 <> addr2 ->
    (* ... need disjoint memory conditions ... *)
    Admitted.
  ```

- **Synth Exercise**: Prove `i32.load` and `i32.store` correctness

#### Month 6: Automation and Tactics

**Goal**: Build custom tactics to accelerate proof development.

```coq
(* Custom tactic library for Synth *)
Ltac synth_simpl :=
  unfold exec_instr, exec_wasm;
  simpl;
  autounfold with synth_db;
  auto with synth_hints.

Ltac synth_destruct_stack :=
  match goal with
  | [ H : context[match ?s.(stack) with _ => _ end] |- _ ] =>
      destruct s.(stack) as [|v1 [|v2 rest]]; try discriminate
  end.

Ltac synth_solve_correspondence :=
  unfold states_match;
  simpl;
  f_equal;
  try ring;
  try solve [auto].

(* Use in proofs *)
Theorem compile_i32_mul_correct : forall ws ws' as,
  exec_wasm I32Mul ws = Some ws' ->
  states_match ws as ->
  exists as', exec_instr (MUL 0 0 1) as = as' /\ states_match ws' as'.
Proof.
  intros.
  synth_destruct_stack.
  synth_simpl.
  eexists; split; [reflexivity|].
  synth_solve_correspondence.
Qed.
```

**Exercise**: Build a tactic that automatically solves 80% of simple arithmetic instruction proofs.

**Checkpoint**: Can you prove 10 instructions in a day (vs. 1/day when starting)?

---

## Resources

### Books

1. **Software Foundations (Free, Online)**
   - Vol 1: Logical Foundations [⭐ Start here]
   - Vol 2: Programming Language Foundations [⭐ For compilers]
   - Vol 3: Verified Functional Algorithms
   - URL: https://softwarefoundations.cis.upenn.edu/

2. **Certified Programming with Dependent Types (CPDT)**
   - By Adam Chlipala
   - More advanced, focuses on automation
   - URL: http://adam.chlipala.net/cpdt/

3. **Programs and Proofs**
   - By Ilya Sergey
   - Practical approach to verification
   - URL: https://ilyasergey.net/pnp/

### Papers (Essential Reading)

1. **CakeML: A Verified Implementation of ML** (POPL 2014)
   - Understand the end-to-end verification approach

2. **A Trustworthy Monadic Formalization of the ARMv7 Instruction Set Architecture** (ITP 2010)
   - ARM formalization techniques

3. **CompCert: Formal Verification of a Realistic Compiler** (CACM 2009)
   - Industry-standard compiler verification

4. **Formal Verification of a Modern Boot Loader** (FM 2019)
   - Practical systems verification

5. **CakeML ARMv8 Backend** (ITP 2022) [⭐ Most relevant]
   - Exactly what Synth needs to do

### Online Courses

1. **Formal Reasoning About Programs** (MIT 6.822)
   - By Adam Chlipala
   - URL: http://adam.chlipala.net/frap/

2. **Programming Language Foundations in Agda** (PLFA)
   - Similar to Coq but different syntax
   - Good for understanding concepts
   - URL: https://plfa.github.io/

### Tools

1. **CoqIDE**: Official IDE for Coq
2. **VSCode + VsCoq**: Modern editor integration
3. **Proof General**: Emacs mode for Coq
4. **Company-Coq**: Enhanced Emacs support
5. **jsCoq**: Run Coq in browser (for quick experiments)

### Community

1. **Coq Discourse**: https://coq.discourse.group/
2. **Coq Zulip Chat**: https://coq.zulipchat.com/
3. **Stack Overflow**: Tag `coq`
4. **Reddit**: r/Coq (small but active)

---

## Synth-Specific Training

### Week 11-12: ARM + WASM Formalization

**Objective**: Formalize actual Synth instruction semantics.

**Input**:
- `crates/synth-verify/src/arm_semantics.rs` (2,987 lines)
- `crates/synth-verify/src/wasm_semantics.rs` (1,461 lines)

**Output**:
- `synth-coq/theories/ArmSemantics.v` (10 instructions)
- `synth-coq/theories/WasmSemantics.v` (10 instructions)

**Success Metrics**:
- All 20 instructions compile in Coq
- Basic sanity properties proved (determinacy, type preservation)
- Automated test generation from Rust property tests

### Week 13-14: Synthesis Rules

**Objective**: Prove 5 WASM→ARM compilation rules.

**Input**:
- `crates/synth-synthesis/src/rules.rs`
- Choose simplest rules first (I32Add, I32Sub, I32And, I32Or, I32Xor)

**Output**:
- `synth-coq/theories/SynthCorrectness.v`
- 5 theorems of form:
  ```coq
  Theorem compile_X_correct : forall ws as,
    states_match ws as ->
    exec_wasm X ws = Some ws' ->
    exists as',
      exec_arm (compile X) as = as' /\
      states_match ws' as'.
  ```

**Success Metrics**:
- All 5 theorems proven (no `Admitted`)
- Proofs are maintainable (< 50 lines each)
- Proofs use custom tactics (not just `auto`)

### Week 15-16: Integration with Sail

**Objective**: Replace hand-written ARM semantics with Sail-generated.

**Input**:
- ARM ASL specification from https://developer.arm.com/
- `asl_to_sail` translator
- Sail Coq backend

**Output**:
- `synth-coq/theories/ArmSpec.v` (generated from Sail)
- Updated `SynthCorrectness.v` using official ARM semantics

**Success Metrics**:
- Sail successfully generates Coq for target ARM instructions
- Previous proofs still work with Sail semantics (or identified differences)
- Confidence that ARM semantics are correct by construction

### Month 5-6: Scale Up

**Objective**: Prove all 151 WASM operations.

**Approach**:
1. Categorize by difficulty:
   - Easy (30 ops): I32 arithmetic/bitwise → 1-2 days each
   - Medium (60 ops): I64, loads/stores → 3-5 days each
   - Hard (61 ops): Floats, control flow → 5-10 days each

2. Build automation:
   - Generate proof skeletons automatically
   - Custom tactics for common patterns
   - Proof by reflection where possible

3. Parallel development:
   - 2 engineers work independently on different categories
   - Weekly integration and code review
   - Shared tactic library

**Success Metrics**:
- 151/151 operations proven correct
- Average proof time < 2 days per operation
- No `Admitted` in production code
- Maintainable proofs (< 100 lines average)

---

## Team Structure

### Roles

**Lead Verification Engineer** (1.0 FTE)
- **Prerequisites**: PhD in formal methods OR 5+ years Coq experience
- **Responsibilities**:
  - Architect proof strategy
  - Build custom tactic libraries
  - Review all proofs
  - Interface with certification consultants
- **Hire Priority**: ⭐⭐⭐ CRITICAL - hire first

**Verification Engineer** (1.0 FTE)
- **Prerequisites**: MS in CS + willing to learn Coq intensively
- **Responsibilities**:
  - Write Coq proofs for WASM/ARM operations
  - Test and validate semantics
  - Maintain proof automation
- **Training**: 3 months intensive Coq training before productive

**Rust/Coq Integration Engineer** (0.5 FTE)
- **Prerequisites**: Strong Rust + basic Coq
- **Responsibilities**:
  - Maintain Rust ↔ Coq correspondence
  - Extract verified code from Coq
  - Property-based testing
  - CI/CD for verification
- **Training**: 6 weeks Coq training

### External Support

**Coq Expert Consultant** ($200/hr, 5 hours/week)
- Review proof strategy
- Unblock difficult proofs
- Code review critical theorems
- **Budget**: $52K/year

**ISO 26262 Certification Consultant** ($250/hr, 10 hours/month)
- Ensure proofs meet certification requirements
- Audit proof artifacts
- Prepare certification documentation
- **Budget**: $30K/year

---

## Progress Tracking

### Milestones

#### Month 1: Foundations Complete ✓
- [ ] All team members complete Software Foundations Vol 1
- [ ] Can prove simple list properties independently
- [ ] Comfortable with `induction`, `destruct`, `rewrite`, `apply`

#### Month 2: Intermediate Skills ✓
- [ ] Complete Software Foundations Vol 2 Chapters 1-4
- [ ] Can define operational semantics for toy language
- [ ] Understand simulation diagrams

#### Month 3: Productive ✓
- [ ] Formalized 10 ARM + 10 WASM instructions in Coq
- [ ] Proved 5 synthesis rules correct
- [ ] Built custom tactic library

#### Month 4-6: Scaling ✓
- [ ] Integrated Sail-generated ARM semantics
- [ ] Proved 50% of all operations (75/151)
- [ ] Automated 50% of proof effort

#### Month 7-12: Expert ✓
- [ ] All 151 operations proven
- [ ] End-to-end compiler correctness theorem
- [ ] Certification artifacts prepared

### Metrics

Track weekly:
- **Lines of Proof Code (LOPC)**: Target 500-1000 LOPC/week/engineer
- **Theorems Proved**: Target 2-3 new theorems/week (early), 5-10/week (late)
- **Proof Automation Ratio**: (auto-solved lemmas) / (total lemmas), target > 50%
- **Proof Maintenance**: Time to update proof after semantics change, target < 1 day

### Weekly Stand-up Questions

1. What theorems did you prove this week?
2. What proofs are you stuck on?
3. What new tactics did you develop?
4. What Rust code changed that affects proofs?
5. Blockers?

---

## Common Pitfalls

### For Beginners

**Pitfall 1: Fighting the proof assistant**
- **Symptom**: Spending hours on trivial lemma
- **Fix**: Step back, reformulate lemma, try different tactics
- **Prevention**: Ask for help after 2 hours stuck

**Pitfall 2: Overuse of `admit`**
- **Symptom**: Proof "done" but 20 `Admitted` lemmas
- **Fix**: Track admitted lemmas, schedule time to prove them
- **Prevention**: Never admit in production code path

**Pitfall 3: Proof by `omega`/`lia` abuse**
- **Symptom**: Every numeric property "solved" by `omega`
- **Fix**: These tactics are sound but hide understanding
- **Prevention**: Understand what `omega` proved, could you prove it manually?

**Pitfall 4: Copy-paste proofs**
- **Symptom**: 10 identical proof scripts with different names
- **Fix**: Extract common pattern into custom tactic or lemma
- **Prevention**: After 3rd similar proof, refactor

### For Intermediate Users

**Pitfall 5: Premature abstraction**
- **Symptom**: Spent 2 weeks building elegant framework, 0 actual proofs
- **Fix**: Prove 3 concrete cases first, then abstract
- **Prevention**: Follow "rule of three" - abstract after 3rd repetition

**Pitfall 6: Ignoring proof obligations**
- **Symptom**: `admit` all the "boring" side conditions
- **Fix**: Often the side conditions reveal bugs in main theorem
- **Prevention**: Prove all obligations, even if tedious

**Pitfall 7: Not using `Search` and `About`**
- **Symptom**: Re-proving lemmas that exist in stdlib
- **Fix**: `Search (_ + _ = _ + _).` finds commutativity lemmas
- **Prevention**: Always search before proving

**Pitfall 8: Weak specification**
- **Symptom**: Proved theorem but doesn't capture actual requirement
- **Fix**: Write specification first, prove second
- **Prevention**: Review spec with domain expert before proving

### For the Team

**Pitfall 9: Lack of proof style guide**
- **Symptom**: Every engineer writes proofs differently, hard to review
- **Fix**: Establish style guide (naming, tactic usage, file structure)
- **Prevention**: Code review for style, not just correctness

**Pitfall 10: No regression testing**
- **Symptom**: Semantics change breaks 50 proofs, takes 2 weeks to fix
- **Fix**: CI runs `make validate` on every commit
- **Prevention**: Modular proof structure minimizes brittleness

**Pitfall 11: Forgetting extraction**
- **Symptom**: Beautiful Coq proof, but can't extract to runnable code
- **Fix**: Test extraction early and often
- **Prevention**: Weekly "extract and run" integration test

**Pitfall 12: Ignoring performance**
- **Symptom**: `Qed` takes 10 minutes, iteration is painful
- **Fix**: Use `Defined` for transparent proofs, `Qed` for opaque
- **Prevention**: Profile proof compilation time, optimize hotspots

---

## Recommended Schedule

### Intensive Track (3 months to productive)

**Month 1**: Full-time Coq training
- Week 1-2: Software Foundations Vol 1 (40 hrs/week)
- Week 3-4: Software Foundations Vol 2 (40 hrs/week)

**Month 2**: Guided practice
- Week 1: CompCert study (20 hrs) + Synth experiments (20 hrs)
- Week 2: CakeML study (20 hrs) + Synth experiments (20 hrs)
- Week 3-4: Formalize 10 ARM + 10 WASM instructions (40 hrs/week)

**Month 3**: Real work
- Week 1-4: Prove 5 synthesis rules (40 hrs/week)

**After Month 3**: Productive contributor (2-3 proofs/week)

### Part-Time Track (6 months to productive)

**Months 1-2**: Foundations (10 hrs/week)
- Software Foundations Vol 1

**Months 3-4**: Intermediate (10 hrs/week)
- Software Foundations Vol 2

**Months 5-6**: Application (15 hrs/week)
- Formalize Synth semantics
- Prove first synthesis rules

**After Month 6**: Productive contributor (1 proof/week)

---

## Coq Proficiency Levels

### Level 0: Beginner (Week 1-4)
- ✓ Can read and understand simple Coq definitions
- ✓ Can apply basic tactics: `intro`, `apply`, `rewrite`, `simpl`, `reflexivity`
- ✓ Can prove simple list properties with `induction`
- ✗ Struggles with complex `destruct` or `inversion`

### Level 1: Novice (Week 5-12)
- ✓ Can define recursive functions and prove their properties
- ✓ Comfortable with `destruct`, `inversion`, `remember`
- ✓ Can read and modify existing proofs
- ✓ Understands simulation diagrams conceptually
- ✗ Struggles to build custom tactics

### Level 2: Intermediate (Month 4-6)
- ✓ Can formalize operational semantics independently
- ✓ Can prove compiler correctness for toy languages
- ✓ Comfortable with Ltac scripting basics
- ✓ Can prove 1-2 Synth operations per week
- ✗ Struggles with advanced automation

### Level 3: Advanced (Month 7-12)
- ✓ Can architect proof strategy for large verification project
- ✓ Builds custom tactic libraries
- ✓ Can prove 5-10 Synth operations per week
- ✓ Understands proof by reflection
- ✗ Not yet expert in specialized domains (floating point, concurrency)

### Level 4: Expert (Year 2+)
- ✓ Can verify any Synth component independently
- ✓ Contributes to Coq ecosystem (tactics, libraries)
- ✓ Mentors junior verification engineers
- ✓ Handles edge cases (floating point, memory models) confidently
- ✓ Can estimate proof effort accurately

---

## FAQ

### Q: Do I need a PhD to learn Coq?

**A**: No. Software Foundations is designed for undergrads. What you need:
- Strong programming background (Rust/C++ level)
- Comfort with recursion and induction
- Willingness to think differently (proofs ≠ code)
- Patience (expect steep learning curve for 2-3 months)

### Q: How long until I'm productive?

**A**:
- **3 months** intensive (40 hrs/week) → 2-3 proofs/week
- **6 months** part-time (10 hrs/week) → 1 proof/week
- **12 months** → 5-10 proofs/week (expert level)

### Q: Can we hire contractors to do Coq proofs?

**A**: Partially. You can hire for:
- Initial setup and architecture (Coq expert consultant)
- Difficult theorems (5-10 hrs/week consultant)
- Code review and audit (monthly)

But core team must learn Coq because:
- Proofs require deep domain knowledge (ARM/WASM semantics)
- Proofs must be maintained as code evolves
- Certification auditors will question your understanding

### Q: What if we find Coq too difficult?

**A**: Alternatives:
1. **Isabelle/HOL**: Similar power, different syntax (used by CakeML)
2. **Lean**: Modern, growing community (used by Microsoft)
3. **F***: More automation, but less mature for compilation
4. **Dafny**: Simpler, but less expressive

**Recommendation**: Stick with Coq for Synth because:
- Sail generates Coq (not Isabelle/Lean/F*/Dafny)
- Largest community and library ecosystem
- Industry adoption (CompCert, CertiKOS, CakeML uses HOL4 but concepts transfer)

### Q: How do we balance proof work with feature development?

**A**:
- **Month 1-3**: 100% training, 0% features
- **Month 4-6**: 80% proofs, 20% features
- **Month 7-12**: 60% proofs, 40% features
- **Year 2+**: 40% proofs, 60% features (maintenance mode)

### Q: What if Rust code changes break proofs?

**A**: This is the hardest part of verification. Strategies:
1. **Stable interfaces**: Freeze ARM/WASM semantics early
2. **Modular proofs**: Isolate proof dependencies
3. **Regression testing**: CI catches broken proofs immediately
4. **Proof refactoring**: Budget 20% time for proof maintenance

### Q: How much does Coq verification slow down development?

**A**: Honest answer:
- **Month 1-6**: 3-5x slower (learning overhead)
- **Month 7-12**: 2x slower (proving takes time)
- **Year 2+**: 1.5x slower (proofs pay off by catching bugs early)
- **Year 3+**: Break-even (fewer bugs, faster debugging)

### Q: Will certification auditors accept our Coq proofs?

**A**: Yes, IF:
- Proofs are readable and well-documented
- Coq itself is qualified (TCL1) or trusted (TCL2)
- Certification consultant validates approach
- ISO 26262-8 Tool Confidence Level analysis is performed

CompCert is certified for ISO 26262 ASIL D, proving it's possible.

---

## Next Steps

1. **This Week**:
   - Set up Coq environment
   - Start Software Foundations Vol 1 Chapter 1
   - Each team member: 10 hours Coq study

2. **This Month**:
   - Complete Software Foundations Vol 1
   - Weekly Coq study group (2 hours)
   - Share solutions and discuss challenges

3. **This Quarter**:
   - Complete Software Foundations Vol 2
   - Formalize first 10 Synth operations in Coq
   - Hire Lead Verification Engineer

4. **This Year**:
   - Prove all 151 WASM operations correct
   - Integrate Sail-generated ARM semantics
   - Prepare certification artifacts

---

## Conclusion

Becoming Coq experts is achievable for the Synth team. Key success factors:

1. **Commitment**: 3 months intensive training before expecting productivity
2. **Expertise**: Hire 1 Lead Verification Engineer with Coq background
3. **Support**: Budget for Coq expert consultant (5 hrs/week)
4. **Patience**: Steep learning curve but proven payoff (see: CompCert, CakeML)
5. **Pragmatism**: Use automation, don't prove everything manually

Timeline:
- Month 3: First proofs
- Month 6: Productive (2-3 proofs/week)
- Month 12: Expert (5-10 proofs/week)
- Month 18: ASIL D certification ready

**You can do this.** Thousands of engineers have learned Coq successfully. The Synth team has strong systems programming skills and domain expertise - that's 80% of what's needed. The remaining 20% (Coq tactics) is learnable in 3 months of focused effort.

**Good luck!** 🚀

---

**Document Version**: 1.0
**Last Updated**: 2025-11-19
**Owner**: Synth Verification Team
**Status**: Ready for team rollout
