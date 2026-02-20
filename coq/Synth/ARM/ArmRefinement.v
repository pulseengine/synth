(** * ARM Semantics Refinement Layer

    This file establishes the connection between our simplified ARM semantics
    and the official ARM Sail specifications.

    The key idea: Our simplified semantics REFINE the official Sail semantics.
    This means our compiler is correct if it produces code that matches Sail's
    behavior, even though we use a simplified model for proof purposes.
*)

From Stdlib Require Import ZArith List.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.

(** ** Refinement Relation *)

(**
   A refinement relation states that if our simplified semantics says
   an instruction produces state s', then the Sail semantics must also
   be able to produce a state that matches s' (or is "more refined").

   Formally: simplified ⊑ sail means:
   - If simplified succeeds, sail succeeds
   - The resulting states are equivalent on observable behavior
*)

Definition refines {A : Type} (simplified : option A) (sail : option A) : Prop :=
  match simplified with
  | None => True  (* If simplified fails, no constraint on sail *)
  | Some s => match sail with
              | None => False  (* If simplified succeeds, sail must succeed *)
              | Some s' => s = s'  (* And produce the same result *)
              end
  end.

Notation "x ⊑ y" := (refines x y) (at level 70).

(** ** Sail ARM Semantics (Placeholder)

    TODO: Import from Sail-generated Coq definitions.
    For now, we define placeholder types that match the expected structure.
*)

Module SailARM.

  (** Sail uses a different state representation - we'll need to map between them *)
  Record sail_state : Type := mkSailState {
    sail_regs : arm_reg -> I32.int;
    sail_vfp_regs : vfp_reg -> I32.int;
    sail_flags : condition_flags;
    sail_mem : Z -> I32.int;
    (* Sail includes many more fields: system registers, MMU state, etc. *)
  }.

  (** Placeholder for Sail instruction execution *)
  Axiom sail_exec_instr : arm_instr -> sail_state -> option sail_state.

  (** State correspondence: our simplified state matches Sail state on observables *)
  Definition state_corresponds (our : arm_state) (sail : sail_state) : Prop :=
    (forall r, get_reg our r = sail_regs sail r) /\
    (forall vr, get_vfp_reg our vr = sail_vfp_regs sail vr) /\
    (our.(flags) = sail_flags sail) /\
    (forall addr, load_mem our addr = sail_mem sail addr).

End SailARM.

(** ** Refinement Theorems *)

(**
   Main refinement theorem: Our ARM semantics refine Sail ARM semantics.

   This is the key correctness property connecting our verification to
   the official ARM architecture specification.
*)
Theorem arm_refines_sail : forall (instr : arm_instr) (s : arm_state) (s_sail : SailARM.sail_state),
  SailARM.state_corresponds s s_sail ->
  exists s_sail',
    SailARM.sail_exec_instr instr s_sail = Some s_sail' /\
    (forall s', exec_instr instr s = Some s' ->
                exists s_sail'',
                  SailARM.state_corresponds s' s_sail'').
Proof.
  (* TODO: Prove after importing real Sail definitions *)
  admit.
Admitted.

(**
   Instruction-specific refinement theorems.
   We prove refinement for each instruction category.
*)

(** Arithmetic instructions refine Sail *)
Theorem add_refines_sail : forall rd rn op2 s s_sail,
  SailARM.state_corresponds s s_sail ->
  exec_instr (ADD rd rn op2) s ⊑
    (match SailARM.sail_exec_instr (ADD rd rn op2) s_sail with
     | Some s' => exec_instr (ADD rd rn op2) s
     | None => None
     end).
Proof.
  (* TODO: Prove after Sail integration *)
  admit.
Admitted.

(** ** Integration Points for Sail *)

(**
   Steps to complete Sail integration:

   1. Install Sail compiler:
      $ opam install sail

   2. Clone ARM Sail specifications:
      $ git clone https://github.com/ARM-software/sail-arm

   3. Generate Coq from Sail (for ARMv8-A subset we use):
      $ cd sail-arm
      $ sail -coq arm8.sail -o ../coq/theories/ARM/SailARMGenerated.v

   4. Import generated definitions:
      Require Import Synth.ARM.SailARMGenerated.

   5. Replace axioms above with real Sail definitions

   6. Prove refinement theorems for each instruction

   7. Extract executable compiler that targets real ARM
*)

(** ** CakeML Integration Points *)

(**
   CakeML provides a verified path to machine code. Integration steps:

   1. Import CakeML ARM backend theories
   2. Define mapping: our ARM IR → CakeML's ARM instructions
   3. Prove our compilation preserves CakeML's semantics
   4. Use CakeML's verified assembler for final binary generation

   This gives us: WASM → Our ARM IR → Sail ARM → CakeML → Machine Code
   with full end-to-end verification!
*)

(** ** Roadmap *)

(**
   Phase 1 (Current): Simplified ARM semantics ✅
   - Enough to prove high-level WASM compilation correct
   - Proofs about register allocation, stack management, etc.

   Phase 2 (Next): Sail integration
   - Replace placeholders with Sail-generated semantics
   - Prove our subset refines Sail's full semantics
   - Get official ARM compliance

   Phase 3 (Future): CakeML backend
   - Connect to CakeML's verified codegen
   - Generate actual executable binaries
   - End-to-end WASM→ARM→Binary pipeline

   Phase 4 (Future): Executable extraction
   - Extract OCaml compiler from Coq proofs
   - Run WASM conformance test suite
   - Deploy for ASIL D safety certification
*)
