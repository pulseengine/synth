(** * ARM Operational Semantics

    This file defines the operational semantics of ARM instructions.
    Each instruction is defined as a state transformation function.

    Based on synth-verify/src/arm_semantics.rs
*)

Require Import ZArith.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.

Open Scope Z_scope.

(** ** Flag Computation Helpers *)

(** Compute negative flag: result < 0 (signed) *)
Definition compute_n_flag (result : I32.int) : bool :=
  Z.ltb (I32.signed result) 0.

(** Compute zero flag: result == 0 *)
Definition compute_z_flag (result : I32.int) : bool :=
  I32.eq result I32.zero.

(** Compute carry flag for addition *)
Definition compute_c_flag_add (x y : I32.int) : bool :=
  let ux := I32.unsigned x in
  let uy := I32.unsigned y in
  Z.ltb I32.max_unsigned (ux + uy).

(** Compute overflow flag for addition *)
Definition compute_v_flag_add (x y result : I32.int) : bool :=
  let sx := I32.signed x in
  let sy := I32.signed y in
  let sr := I32.signed result in
  (* Overflow if: pos + pos = neg OR neg + neg = pos *)
  orb
    (andb (andb (Z.leb 0 sx) (Z.leb 0 sy)) (Z.ltb sr 0))
    (andb (andb (Z.ltb sx 0) (Z.ltb sy 0)) (Z.leb 0 sr)).

(** Update flags after arithmetic operation *)
Definition update_flags_arith (result : I32.int) (c v : bool) : condition_flags :=
  mkFlags
    (compute_n_flag result)
    (compute_z_flag result)
    c
    v.

(** ** Instruction Semantics *)

(** Execute a single ARM instruction *)
Definition exec_instr (i : arm_instr) (s : arm_state) : option arm_state :=
  match i with
  (* Arithmetic operations *)
  | ADD rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.add v1 v2 in
      Some (set_reg s rd result)

  | SUB rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.sub v1 v2 in
      Some (set_reg s rd result)

  | MUL rd rn rm =>
      let v1 := get_reg s rn in
      let v2 := get_reg s rm in
      let result := I32.mul v1 v2 in
      Some (set_reg s rd result)

  | SDIV rd rn rm =>
      let v1 := get_reg s rn in
      let v2 := get_reg s rm in
      match I32.divs v1 v2 with
      | Some result => Some (set_reg s rd result)
      | None => None  (* Division by zero or overflow *)
      end

  | UDIV rd rn rm =>
      let v1 := get_reg s rn in
      let v2 := get_reg s rm in
      match I32.divu v1 v2 with
      | Some result => Some (set_reg s rd result)
      | None => None  (* Division by zero *)
      end

  | MLS rd rn rm ra =>
      (* MLS: rd = ra - (rn * rm) *)
      let vn := get_reg s rn in
      let vm := get_reg s rm in
      let va := get_reg s ra in
      let product := I32.mul vn vm in
      let result := I32.sub va product in
      Some (set_reg s rd result)

  (* Bitwise operations *)
  | AND rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.and v1 v2 in
      Some (set_reg s rd result)

  | ORR rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.or v1 v2 in
      Some (set_reg s rd result)

  | EOR rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.xor v1 v2 in
      Some (set_reg s rd result)

  | MVN rd op2 =>
      let v := eval_operand2 op2 s in
      let result := I32.repr (Z.lnot (I32.unsigned v)) in
      Some (set_reg s rd result)

  (* Shift operations *)
  | LSL rd rn shift =>
      let v := get_reg s rn in
      let shift_amt := I32.repr (Z.of_nat shift) in
      let result := I32.shl v shift_amt in
      Some (set_reg s rd result)

  | LSR rd rn shift =>
      let v := get_reg s rn in
      let shift_amt := I32.repr (Z.of_nat shift) in
      let result := I32.shru v shift_amt in
      Some (set_reg s rd result)

  | ASR rd rn shift =>
      let v := get_reg s rn in
      let shift_amt := I32.repr (Z.of_nat shift) in
      let result := I32.shrs v shift_amt in
      Some (set_reg s rd result)

  | ROR rd rn shift =>
      let v := get_reg s rn in
      let shift_amt := I32.repr (Z.of_nat shift) in
      let result := I32.rotr v shift_amt in
      Some (set_reg s rd result)

  (* Move operations *)
  | MOV rd op2 =>
      let v := eval_operand2 op2 s in
      Some (set_reg s rd v)

  | MOVW rd imm =>
      (* Move 16-bit immediate to lower 16 bits *)
      Some (set_reg s rd imm)

  | MOVT rd imm =>
      (* Move 16-bit immediate to upper 16 bits *)
      let current := get_reg s rd in
      let lower := I32.and current (I32.repr 0xFFFF) in
      let upper := I32.shl imm (I32.repr 16) in
      let result := I32.or lower upper in
      Some (set_reg s rd result)

  (* Comparison *)
  | CMP rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      let result := I32.sub v1 v2 in
      (* Update flags but don't write to register *)
      let c := compute_c_flag_add v1 (I32.sub I32.zero v2) in
      let v := compute_v_flag_add v1 (I32.sub I32.zero v2) result in
      let new_flags := update_flags_arith result c v in
      Some (set_flags s new_flags)

  (* Bit manipulation - simplified implementations *)
  | CLZ rd rm =>
      (* Count leading zeros - placeholder *)
      let v := get_reg s rm in
      (* Real implementation would count leading zeros *)
      Some (set_reg s rd I32.zero)

  | RBIT rd rm =>
      (* Reverse bits - placeholder *)
      let v := get_reg s rm in
      Some (set_reg s rd v)

  | POPCNT rd rm =>
      (* Population count - placeholder *)
      let v := get_reg s rm in
      Some (set_reg s rd I32.zero)

  (* Memory operations *)
  | LDR rd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := load_mem s (I32.signed addr) in
      Some (set_reg s rd value)

  | STR rd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := get_reg s rd in
      Some (store_mem s (I32.signed addr) value)

  (* Control flow - simplified *)
  | B offset =>
      (* Branch: update PC *)
      let current_pc := get_reg s PC in
      let new_pc := I32.add current_pc (I32.repr offset) in
      Some (set_reg s PC new_pc)

  | BL offset =>
      (* Branch with link: save return address in LR *)
      let current_pc := get_reg s PC in
      let return_addr := I32.add current_pc (I32.repr 4) in
      let s' := set_reg s LR return_addr in
      let new_pc := I32.add current_pc (I32.repr offset) in
      Some (set_reg s' PC new_pc)

  | BX rm =>
      (* Branch and exchange *)
      let target := get_reg s rm in
      Some (set_reg s PC target)

  (* VFP operations - placeholders for now *)
  | VADD_F32 rd rn rm =>
      (* Placeholder: would need proper floating-point semantics *)
      Some s

  | VSUB_F32 rd rn rm =>
      Some s

  | VMUL_F32 rd rn rm =>
      Some s

  | VDIV_F32 rd rn rm =>
      Some s

  | _ =>
      (* Not yet implemented *)
      Some s
  end.

(** Execute a sequence of instructions *)
Fixpoint exec_program (prog : list arm_instr) (s : arm_state) : option arm_state :=
  match prog with
  | [] => Some s
  | i :: rest =>
      match exec_instr i s with
      | Some s' => exec_program rest s'
      | None => None
      end
  end.

(** ** Properties *)

(** Determinacy: executing an instruction produces at most one result *)
Theorem exec_instr_deterministic : forall i s s1 s2,
  exec_instr i s = Some s1 ->
  exec_instr i s = Some s2 ->
  s1 = s2.
Proof.
  intros i s s1 s2 H1 H2.
  rewrite H1 in H2.
  injection H2. auto.
Qed.

(** ADD is commutative in the operands *)
Theorem add_commutative : forall rd rn rm s,
  exec_instr (ADD rd rn (Reg rm)) s =
  exec_instr (ADD rd rm (Reg rn)) s.
Proof.
  intros. simpl.
  unfold eval_operand2.
  rewrite I32.add_commut.
  reflexivity.
Qed.

(** Setting a register doesn't affect other registers *)
Theorem exec_preserves_other_regs : forall rd rn rm s r,
  r <> rd ->
  match exec_instr (ADD rd rn (Reg rm)) s with
  | Some s' => get_reg s' r = get_reg s r
  | None => True
  end.
Proof.
  intros. simpl.
  rewrite get_set_reg_neq; auto.
Qed.

(** ADD with zero is identity (right) *)
Theorem add_zero_right : forall rd rn s,
  exec_instr (ADD rd rn (Imm I32.zero)) s =
  Some (set_reg s rd (get_reg s rn)).
Proof.
  intros. simpl.
  rewrite I32.add_zero.
  unfold get_reg at 1.
  rewrite I32.repr_unsigned.
  reflexivity.
Qed.

(** MOV transfers the value correctly *)
Theorem mov_correct : forall rd rs s,
  exec_instr (MOV rd (Reg rs)) s =
  Some (set_reg s rd (get_reg s rs)).
Proof.
  intros. simpl. reflexivity.
Qed.

(** Executing an empty program doesn't change state *)
Theorem exec_program_nil : forall s,
  exec_program [] s = Some s.
Proof.
  intros. reflexivity.
Qed.

(** Executing programs is associative (sequential composition) *)
Theorem exec_program_app : forall p1 p2 s,
  exec_program (p1 ++ p2) s =
  match exec_program p1 s with
  | Some s' => exec_program p2 s'
  | None => None
  end.
Proof.
  induction p1; intros.
  - simpl. reflexivity.
  - simpl. destruct (exec_instr a s) eqn:E; auto.
    apply IHp1.
Qed.
