(** * The Block/End correspondence obligation — stated, and its obstruction
    pinned (#1057, RQ-64-CFOBLIG)

    THIS FILE CONTAINS NO CORRECTNESS THEOREM. Every [Qed] below is a
    kernel-checked statement about what the CURRENT ARM model does, made so
    that the obstruction to the Block/End obligation is a fact the checker
    holds rather than a sentence in a status file. When VCR-ISA-001 closes a
    gap, the matching lemma here stops compiling — that is the intended
    signal, the same red-first shape the differential gates use. Nothing
    here is named [*_correct]; nothing here is admitted.

    ** The obligation (what a Block/End theorem must say)

    WASM side (WasmBlocks.v, kernel-checked): [exec_wasm_blocks] runs a
    [Block body End_ cont] by running [body], and on a [WBranch 0] outcome
    UNWINDS the operand stack to the block's entry height and resumes with
    [cont] ([exec_wasm_blocks_block_taken]); a [Loop] RE-ENTERS its body on
    [WBranch 0] ([exec_wasm_blocks_loop_reenter]); [Br l] is an unconditional
    [WBranch l] ([exec_wasm_blocks_br]).

    ARM side (what ships — select_with_stack.rs, arm_backend.rs): [Block]
    emits nothing; [Loop] emits a zero-size [Label] at its start; [End] emits
    the block's end [Label] and, for a branched-to arity-1 block, a
    [MOV r_res, top] into a result register the allocator picked at the FIRST
    branch edge; [Br depth] emits [edge_value_move] then an unconditional
    [B label]; [BrIf depth] emits [CMP cond, #0 ; BNE label]. Labels resolve
    to BYTE offsets by iterating the real encoder's size probe until the
    16-/32-bit branch widths converge.

    So the theorem to state is: under a simulation relation [R] between
    [wasm_state] and [arm_state], if the WASM run of a (nested) block
    structure ends in outcome [o], the ARM run of its compiled code from the
    block's first index reaches, in some number of steps, EXACTLY the index
    the compiler resolved for [o] — the index after the matching [End_]'s
    label for a fall-through or a depth-0 branch, the enclosing label for a
    deeper branch, the loop's start for a loop back-edge — in a state that
    is again [R]-related to the WASM state AFTER unwinding. The branch
    landing index must be derived from the compiled layout (a
    [compile_blocks] that resolves label depth to distance through the
    enclosing structure), never a free parameter: with the offset free the
    statement collapses to [brif_correct], which already holds and says
    nothing about End.

    ** The obstruction (why it cannot be discharged against ArmSemantics.v
       today), each item tied to a kernel-checked lemma or a measured shipped
       fact — this is the VCR-ISA-001 input

    O1. NO EXECUTOR-VISIBLE UNCONDITIONAL BRANCH. [exec_program_pc] takes a
        branch only for [BCondOffset]; the shipped [Br] lowers to [B label].
        In the model, [B off] is delegated to [exec_instr], which writes the
        PC REGISTER by byte arithmetic while the executor advances its own
        INDEX by one — two disjoint program counters, and the register one
        is never read back. Pinned by [exec_program_pc_B_not_taken] below:
        an unconditional branch executes as a fall-through, for every
        offset. [BL] has the identical shape ([exec_program_pc_BL_not_taken]),
        which is why gale's [Call] rows (31 of 180) share this obstruction.
        This is NOT a ten-line fix: intercepting [B off] in the index
        executor requires deciding the UNIT of [off], and the shipped unit
        is bytes over variable-length Thumb-2 encodings (O3).

    O2. NO BACKWARD BRANCH. [exec_program_pc] computes the taken target as
        [pc + 1 + Z.to_nat off]; for a negative offset [Z.to_nat] is 0, so a
        backward conditional branch lands on [pc + 1] whether or not its
        condition holds — a loop back-edge is a fall-through, silently.
        Pinned by [exec_program_pc_bcond_backward_falls_through] and made
        concrete by [arm_count_loop_body_runs_once]: a three-instruction
        counting loop (ADD ; CMP #10 ; BNE -3) is executed by the model as
        straight-line code, R0 = 1 on exit, where WasmBlocks.v's
        [ex_loop_counts_down_to_zero] shows the WASM side iterating. Every
        [Loop]/[End_] correspondence is therefore unstatable until the
        executor's pc arithmetic is signed and its fuel counts STEPS rather
        than the depth budget [S (length prog)] (ArmSemantics.v documents
        "Compilation.v only emits forward (skip-ahead) offsets" as a design
        assumption; a loop violates it by construction). Blast radius of
        changing that arithmetic, measured: [exec_program_pc] is used in 4
        files (ArmSemantics 20 sites, CorrectnessI32 27, CorrectnessBrIf 11,
        Compilation 1) — the #73 trap-guard proofs and [brif_correct] all
        unfold through [exec_program_pc_bcond] and must be re-checked.

    O3. INDEX-GRANULAR PC AGAINST BYTE-RESOLVED LABELS. The model's pc is an
        instruction index; [compile_brif off] models "instructions skipped".
        The shipped resolver (arm_backend.rs, branch resolution) sums the
        REAL encoder's per-instruction byte length, with [Label] at 0 bytes,
        iterating as 16-bit branches widen to 32-bit. The two closed
        resolution miscompiles live exactly there: #483 (branch target lands
        MID-INSTRUCTION) and #740 (T3 [B<cond>.W] offsets halved). An
        index-granular Block/End theorem would have been GREEN across both.
        That is the #1021 popcnt shape one level up: an index model of a
        byte-resolved branch is a silent claim that encoding sizes do not
        matter to resolution. The model needs a per-instruction size
        function DERIVED from the shipped encoder (the #936
        [straightline_expansion_real] pattern) and a byte-addressed pc.

    O4. NO COMPOSITIONAL STATE RELATION. Compilation.v defines
        [state_correspondence] (a 2-deep R0/R1 stack view, R4-R7 locals,
        memory equality); it appears in ZERO theorem statements — every one
        of the existing correctness Qed relates ONE instruction under fixed
        register hypotheses ([get_reg astate R0 = v1] ...), and
        [compile_wasm_program = flat_map compile_wasm_to_arm] composes
        lowerings that each assume operands in R0/R1, which a stack machine
        does not provide instruction to instruction. A block's body is an
        arbitrary sequence; without a relation preserved ACROSS instructions
        the state at [End_] cannot be related to anything. [brif_correct]
        sidesteps this by being stated AT the branch point; a Block/End
        theorem cannot, because its content is what happens between the
        branch and the join.

    O5. THE RESULT REGISTER IS AN ALLOCATION DECISION. For a value-carrying
        block, the shipped [End] emits [MOV r_res, top] into a register the
        allocator chose lazily at the first branch edge (select_with_stack.rs,
        [result_reg: None, // allocated lazily at the first br edge],
        [edge_value_move]); the #509 and #930 miscompiles were in this
        value dimension. An atomic [compile_wasm_to_arm End_ = []] would be
        the popcnt-shaped silent claim that End is code-free. This model has
        no blocktype and no allocator state, so the arity-1 join is not
        expressible; WasmBlocks.v models VOID blocks only and says so.

    ** What VCR-ISA-001 must supply, in order of dependence

    (a) an executor whose pc is a BYTE address with an encoder-derived size
        function, in which [B]/[BL]/[BCondOffset] are all executor-visible
        and offsets may be negative (closes O1, O2, O3 together — they are
        one decision, not three);
    (b) a step-counted fuel discipline for (a), and the re-check of the 59
        [exec_program_pc] sites (O2's blast radius);
    (c) a simulation relation preserved across instructions — the
        register-parametric framework #73 named and [state_correspondence]
        sketched (O4) — before any body-spanning theorem;
    (d) blocktype arity and the join register in the model (O5), which is
        VCR-RA/VCR-DEC territory as much as ISA modelling.

    Until (a)-(c) exist, a Block/End theorem is either unstatable (loops,
    calls, byte-level landing) or statable only for the fragment — forward,
    void, index-granular — that is blind to every closed control-flow
    miscompile. That fragment is deliberately NOT proven here: a green Qed
    that could not have caught #483, #500, #509, #740 or #930 would be
    exactly the overclaim this artifact forbids. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.ARM.ArmSemantics.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.
Require Import Synth.WASM.WasmSemantics.
Require Import Synth.WASM.WasmBlocks.

Import ListNotations.
Open Scope Z_scope.

(** ** O1 — the unconditional branch is not a branch in the index executor

    [B off] updates the PC register and the executor moves to [pc + 1]
    regardless of [off]. *)
Lemma exec_program_pc_B_not_taken : forall fuel prog pc s off,
  nth_error prog pc = Some (B off) ->
  exec_program_pc (S fuel) prog pc s
  = exec_program_pc fuel prog (pc + 1)%nat
      (set_reg s PC (I32.add (get_reg s PC) (I32.repr off))).
Proof.
  intros fuel prog pc s off H.
  rewrite (exec_program_pc_instr fuel prog pc s _ H I).
  cbn [exec_instr]. reflexivity.
Qed.

(** [BL off] — the shape behind every [Call] — sets LR and the PC register,
    and the executor still moves to [pc + 1]. *)
Lemma exec_program_pc_BL_not_taken : forall fuel prog pc s off,
  nth_error prog pc = Some (BL off) ->
  exec_program_pc (S fuel) prog pc s
  = exec_program_pc fuel prog (pc + 1)%nat
      (set_reg (set_reg s LR (I32.add (get_reg s PC) (I32.repr 4))) PC
               (I32.add (get_reg s PC) (I32.repr off))).
Proof.
  intros fuel prog pc s off H.
  rewrite (exec_program_pc_instr fuel prog pc s _ H I).
  cbn [exec_instr]. reflexivity.
Qed.

(** ** O2 — a backward conditional branch is a fall-through

    For [off < 0] the taken and not-taken targets coincide at [pc + 1]: the
    condition's value is unobservable, so no loop back-edge can be
    represented. *)
Lemma exec_program_pc_bcond_backward_falls_through :
  forall fuel prog pc s cond off,
  off < 0 ->
  nth_error prog pc = Some (BCondOffset cond off) ->
  exec_program_pc (S fuel) prog pc s = exec_program_pc fuel prog (pc + 1)%nat s.
Proof.
  intros fuel prog pc s cond off Hoff H.
  rewrite (exec_program_pc_bcond fuel prog pc s cond off H).
  destruct off as [| p | p]; [lia | lia |].
  cbn [Z.to_nat].
  replace (pc + 1 + 0)%nat with (pc + 1)%nat by lia.
  destruct (eval_condition cond (flags s)); reflexivity.
Qed.

(** ** O2, concretely — the model runs a counting loop's body exactly once

    [ADD R0, R0, #1 ; CMP R0, #10 ; BNE -3] is the shape an encoder emits
    for "loop until R0 = 10". From R0 = 0 the WASM analogue iterates
    (WasmBlocks.v, [ex_loop_counts_down_to_zero]); this model exits with
    R0 = 1, having taken the BNE to [pc + 1 + 0]. Observed through
    [I32.unsigned] so the comparison is a plain [Z]. *)
Definition arm_count_loop : arm_program :=
  [ADD R0 R0 (Imm I32.one);
   CMP R0 (Imm (I32.repr 10));
   BCondOffset Cond_NE (-3)].

Definition arm_state0 : arm_state :=
  mkArmState (fun _ => I32.zero) (mkFlags false false false false)
             (fun _ => I32.zero) (fun _ => I32.zero)
             (fun _ => I32.zero) (fun _ => I32.zero).

Example arm_count_loop_body_runs_once :
  match exec_program_br arm_count_loop arm_state0 with
  | Some s' => I32.unsigned (get_reg s' R0)
  | None => -1
  end = 1.
Proof. vm_compute. reflexivity. Qed.
