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
(**
   T3 — GENUINELY UNPROVABLE AS STATED (opaque-axiom placeholder), NOT a
   tractable residual. [SailARM.sail_exec_instr] (line 59) is declared as an
   [Axiom], i.e. an opaque function symbol with NO computational content and NO
   defining equations. The conclusion here requires exhibiting a concrete
   witness [s_sail'] together with a proof that
   [SailARM.sail_exec_instr instr s_sail = Some s_sail'] — but nothing in the
   context can reduce or constrain an opaque axiom to [Some _], so no such
   witness is derivable. This is a modeling-scaffold limitation, not a missing
   arithmetic lemma: it cannot be closed without REPLACING the axiom with a
   real, computational Sail semantics.

   WHAT WOULD CLOSE IT / WHERE THE REAL WORK LIVES. The Sail anchoring the North
   Star calls for (VCR-ISA-001, epic #242) has since landed as
   [Synth.ARM.SailArmBridge] — a per-instruction hand-transcription of the
   rems-project/sail-arm arm-v9.4-a execute clauses with line-level provenance,
   plus BRIDGE lemmas proving [ArmSemantics.v]'s instruction equals the Sail
   transcription on the shared state projection (92 Qed, real, actively
   extended round by round). That file, not this placeholder, is the live Sail
   correspondence; the spike (docs/design/vcr-isa-001-spike.md) measured that
   importing the 42 MB Sail-generated Rocq model wholesale is infeasible at
   synth's scale, which is exactly why [sail_exec_instr] here stays an opaque
   axiom rather than a real definition. This theorem is retained only as the
   historical statement of the intended global refinement shape; it is honestly
   Admitted (T3), superseded by the SailArmBridge per-instruction bridges. *)
Theorem arm_refines_sail : forall (instr : arm_instr) (s : arm_state) (s_sail : SailARM.sail_state),
  SailARM.state_corresponds s s_sail ->
  exists s_sail',
    SailARM.sail_exec_instr instr s_sail = Some s_sail' /\
    (forall s', exec_instr instr s = Some s' ->
                exists s_sail'',
                  SailARM.state_corresponds s' s_sail'').
Proof.
  (* T3: [SailARM.sail_exec_instr] is an opaque Axiom (line 59) — the required
     [= Some s_sail'] witness is not derivable. Superseded by the real
     per-instruction bridges in [Synth.ARM.SailArmBridge]. See the block
     comment above for the full rationale and closure path. *)
  admit.
Admitted.

(**
   Instruction-specific refinement theorems.
   We prove refinement for each instruction category.
*)

(** Arithmetic instructions refine Sail.

    T3 — same opaque-axiom obstacle as [arm_refines_sail]. Unfolding [refines],
    when [exec_instr (ADD ..) s = Some r] the goal reduces to
    [Some r = match SailARM.sail_exec_instr (ADD ..) s_sail with
              | Some _ => Some r | None => None end],
    which holds iff [SailARM.sail_exec_instr (ADD ..) s_sail = Some _]. That is
    again a claim about the opaque [Axiom] with no defining equation, so it is
    not derivable. Closure requires replacing [sail_exec_instr] with a real
    computational Sail semantics; the live per-instruction ADD/ADDS/CMP bridges
    already exist in [Synth.ARM.SailArmBridge] (Round 1+), which is where the
    genuine ADD↔Sail correspondence is proved. Honestly Admitted (T3),
    superseded. *)
Theorem add_refines_sail : forall rd rn op2 s s_sail,
  SailARM.state_corresponds s s_sail ->
  exec_instr (ADD rd rn op2) s ⊑
    (match SailARM.sail_exec_instr (ADD rd rn op2) s_sail with
     | Some s' => exec_instr (ADD rd rn op2) s
     | None => None
     end).
Proof.
  (* T3: opaque [SailARM.sail_exec_instr] Axiom; superseded by the real ADD/ADDS
     bridges in [Synth.ARM.SailArmBridge]. See the comment above. *)
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
