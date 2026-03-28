(** * ARM Operational Semantics

    This file defines the operational semantics of ARM instructions.
    Each instruction is defined as a state transformation function.

    Based on synth-verify/src/arm_semantics.rs
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.

Import ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

(** ** Abstract VFP (Floating-Point) Operations

    VFP operations are axiomatized as abstract functions on bit patterns.
    VFP registers store I32.int values representing IEEE 754 bit patterns.

    This is sufficient for existence proofs (T2: ARM execution succeeds).
    Full result-correspondence proofs (T1) would require Flocq IEEE 754
    semantics to relate these bit-pattern operations to WASM float semantics.
*)

(** F32 arithmetic on bit patterns (single-precision, stored in S-registers) *)
Axiom f32_add_bits : I32.int -> I32.int -> I32.int.
Axiom f32_sub_bits : I32.int -> I32.int -> I32.int.
Axiom f32_mul_bits : I32.int -> I32.int -> I32.int.
Axiom f32_div_bits : I32.int -> I32.int -> I32.int.
Axiom f32_sqrt_bits : I32.int -> I32.int.
Axiom f32_abs_bits : I32.int -> I32.int.
Axiom f32_neg_bits : I32.int -> I32.int.

(** F64 arithmetic on bit patterns (double-precision, stored in D-registers) *)
Axiom f64_add_bits : I32.int -> I32.int -> I32.int.
Axiom f64_sub_bits : I32.int -> I32.int -> I32.int.
Axiom f64_mul_bits : I32.int -> I32.int -> I32.int.
Axiom f64_div_bits : I32.int -> I32.int -> I32.int.
Axiom f64_sqrt_bits : I32.int -> I32.int.
Axiom f64_abs_bits : I32.int -> I32.int.
Axiom f64_neg_bits : I32.int -> I32.int.

(** VFP comparison: updates FPSCR flags, modeled as updating ARM condition flags.
    Returns the new condition flags after comparing two VFP values. *)
Axiom f32_compare_flags : I32.int -> I32.int -> condition_flags.
Axiom f64_compare_flags : I32.int -> I32.int -> condition_flags.

(** VFP conversion operations on bit patterns *)
Axiom cvt_f32_to_f64_bits : I32.int -> I32.int.  (** F32 -> F64 promote *)
Axiom cvt_f64_to_f32_bits : I32.int -> I32.int.  (** F64 -> F32 demote *)
Axiom cvt_s32_to_f32_bits : I32.int -> I32.int.  (** Signed int -> F32 *)
Axiom cvt_f32_to_s32_bits : I32.int -> I32.int.  (** F32 -> Signed int *)

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

(** Compute carry flag for subtraction (CMP): C = 1 when v1 >= v2 unsigned (no borrow) *)
Definition compute_c_flag_sub (v1 v2 : I32.int) : bool :=
  Z.leb (I32.unsigned v2) (I32.unsigned v1).

(** Compute overflow flag for subtraction:
    Overflow when operands have different signs and result sign differs from first operand.
    Pos - Neg -> Neg (overflow) OR Neg - Pos -> Pos (overflow) *)
Definition compute_v_flag_sub (v1 v2 : I32.int) : bool :=
  let sv1 := I32.signed v1 in
  let sv2 := I32.signed v2 in
  let sr := I32.signed (I32.sub v1 v2) in
  orb
    (andb (andb (Z.leb 0 sv1) (Z.ltb sv2 0)) (Z.ltb sr 0))
    (andb (andb (Z.ltb sv1 0) (Z.leb 0 sv2)) (Z.leb 0 sr)).

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

  (* Shift operations — immediate *)
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

  (* Shift operations — register (shift amount in Rm, masked to 0-31 by I32.shl etc.) *)
  | LSL_reg rd rn rm =>
      let v := get_reg s rn in
      let shift_amt := get_reg s rm in
      Some (set_reg s rd (I32.shl v shift_amt))

  | LSR_reg rd rn rm =>
      let v := get_reg s rn in
      let shift_amt := get_reg s rm in
      Some (set_reg s rd (I32.shru v shift_amt))

  | ASR_reg rd rn rm =>
      let v := get_reg s rn in
      let shift_amt := get_reg s rm in
      Some (set_reg s rd (I32.shrs v shift_amt))

  | ROR_reg rd rn rm =>
      let v := get_reg s rn in
      let shift_amt := get_reg s rm in
      Some (set_reg s rd (I32.rotr v shift_amt))

  (* Reverse subtract: RSB Rd, Rn, Op2 = Op2 - Rn *)
  | RSB rd rn op2 =>
      let v1 := get_reg s rn in
      let v2 := eval_operand2 op2 s in
      Some (set_reg s rd (I32.sub v2 v1))

  (* Move operations *)
  | MOV rd op2 =>
      let v := eval_operand2 op2 s in
      Some (set_reg s rd v)

  | MOVEQ rd op2 =>
      (* Conditional move: only move if Z flag is set (equal) *)
      if s.(flags).(flag_z) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s  (* No operation if condition false *)

  | MOVNE rd op2 =>
      (* Conditional move: only move if Z flag is clear (not equal) *)
      if s.(flags).(flag_z) then
        Some s  (* No operation if condition false *)
      else
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)

  | MOVLT rd op2 =>
      (* Less than (signed): N != V *)
      if Bool.eqb s.(flags).(flag_n) s.(flags).(flag_v) then
        Some s
      else
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)

  | MOVLE rd op2 =>
      (* Less or equal (signed): Z set OR N != V *)
      if s.(flags).(flag_z) || negb (Bool.eqb s.(flags).(flag_n) s.(flags).(flag_v)) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVGT rd op2 =>
      (* Greater than (signed): Z clear AND N == V *)
      if negb s.(flags).(flag_z) && Bool.eqb s.(flags).(flag_n) s.(flags).(flag_v) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVGE rd op2 =>
      (* Greater or equal (signed): N == V *)
      if Bool.eqb s.(flags).(flag_n) s.(flags).(flag_v) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVLO rd op2 =>
      (* Lower (unsigned): C clear *)
      if s.(flags).(flag_c) then
        Some s
      else
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)

  | MOVLS rd op2 =>
      (* Lower or same (unsigned): C clear OR Z set *)
      if negb s.(flags).(flag_c) || s.(flags).(flag_z) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVHI rd op2 =>
      (* Higher (unsigned): C set AND Z clear *)
      if s.(flags).(flag_c) && negb s.(flags).(flag_z) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

  | MOVHS rd op2 =>
      (* Higher or same (unsigned): C set *)
      if s.(flags).(flag_c) then
        let v := eval_operand2 op2 s in
        Some (set_reg s rd v)
      else
        Some s

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
      let c := compute_c_flag_sub v1 v2 in
      let v := compute_v_flag_sub v1 v2 in
      let new_flags := update_flags_arith result c v in
      Some (set_flags s new_flags)

  (* Bit manipulation — axiomatized via I32.clz/rbit/popcnt *)
  | CLZ rd rm =>
      let v := get_reg s rm in
      Some (set_reg s rd (I32.clz v))

  | RBIT rd rm =>
      let v := get_reg s rm in
      Some (set_reg s rd (I32.rbit v))

  | POPCNT rd rm =>
      let v := get_reg s rm in
      Some (set_reg s rd (I32.popcnt v))

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

  (* VFP F32 arithmetic operations *)
  | VADD_F32 sd sn sm =>
      let vn := get_vfp_reg s sn in
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_add_bits vn vm))

  | VSUB_F32 sd sn sm =>
      let vn := get_vfp_reg s sn in
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_sub_bits vn vm))

  | VMUL_F32 sd sn sm =>
      let vn := get_vfp_reg s sn in
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_mul_bits vn vm))

  | VDIV_F32 sd sn sm =>
      let vn := get_vfp_reg s sn in
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_div_bits vn vm))

  | VSQRT_F32 sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_sqrt_bits vm))

  | VABS_F32 sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_abs_bits vm))

  | VNEG_F32 sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (f32_neg_bits vm))

  (* VFP F64 arithmetic operations *)
  | VADD_F64 dd dn dm =>
      let vn := get_vfp_reg s dn in
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_add_bits vn vm))

  | VSUB_F64 dd dn dm =>
      let vn := get_vfp_reg s dn in
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_sub_bits vn vm))

  | VMUL_F64 dd dn dm =>
      let vn := get_vfp_reg s dn in
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_mul_bits vn vm))

  | VDIV_F64 dd dn dm =>
      let vn := get_vfp_reg s dn in
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_div_bits vn vm))

  | VSQRT_F64 dd dm =>
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_sqrt_bits vm))

  | VABS_F64 dd dm =>
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_abs_bits vm))

  | VNEG_F64 dd dm =>
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s dd (f64_neg_bits vm))

  (* VFP comparison operations — update condition flags via VMRS APSR_nzcv, FPSCR *)
  | VCMP_F32 sn sm =>
      let vn := get_vfp_reg s sn in
      let vm := get_vfp_reg s sm in
      Some (set_flags s (f32_compare_flags vn vm))

  | VCMP_F64 dn dm =>
      let vn := get_vfp_reg s dn in
      let vm := get_vfp_reg s dm in
      Some (set_flags s (f64_compare_flags vn vm))

  (* VFP conversion operations *)
  | VCVT_F32_F64 sd dm =>
      let vm := get_vfp_reg s dm in
      Some (set_vfp_reg s sd (cvt_f64_to_f32_bits vm))

  | VCVT_F64_F32 dd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s dd (cvt_f32_to_f64_bits vm))

  | VCVT_S32_F32 sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (cvt_f32_to_s32_bits vm))

  | VCVT_F32_S32 sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd (cvt_s32_to_f32_bits vm))

  (* VFP move operations *)
  | VMOV sd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_vfp_reg s sd vm)

  | VMOV_ARM_TO_VFP sd rm =>
      let vm := get_reg s rm in
      Some (set_vfp_reg s sd vm)

  | VMOV_VFP_TO_ARM rd sm =>
      let vm := get_vfp_reg s sm in
      Some (set_reg s rd vm)

  (* VFP memory operations *)
  | VLDR_F32 sd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := load_mem s (I32.signed addr) in
      Some (set_vfp_reg s sd value)

  | VSTR_F32 sd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := get_vfp_reg s sd in
      Some (store_mem s (I32.signed addr) value)

  | VLDR_F64 dd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := load_mem s (I32.signed addr) in
      Some (set_vfp_reg s dd value)

  | VSTR_F64 dd rn offset =>
      let base := get_reg s rn in
      let addr := I32.add base (I32.repr offset) in
      let value := get_vfp_reg s dd in
      Some (store_mem s (I32.signed addr) value)
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
  intros rd rn rm s r Hneq. simpl. unfold eval_operand2.
  apply get_set_reg_neq. auto.
Qed.

(** ADD with zero normalizes the register value *)
Theorem add_zero_right : forall rd rn s,
  exec_instr (ADD rd rn (Imm I32.zero)) s =
  Some (set_reg s rd (I32.repr (get_reg s rn))).
Proof.
  intros. simpl. unfold eval_operand2.
  rewrite I32.add_zero. reflexivity.
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
  exec_program (@nil arm_instr) s = Some s.
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
  - simpl. destruct (exec_instr a s) eqn:E.
    + apply IHp1.
    + reflexivity.
Qed.
