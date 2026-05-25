(** * ARM Instructions

    This file defines the ARM instruction set that Synth targets.
    Based on synth-synthesis/src/rules.rs
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.

Open Scope Z_scope.
Open Scope bool_scope.

(** ** Operand 2 (Flexible Second Operand) *)

(** ARM instructions often have a flexible second operand that can be:
    - An immediate value
    - A register
    - A register with a shift operation
*)

Inductive operand2 : Type :=
  | Imm : I32.int -> operand2
  | Reg : arm_reg -> operand2
  | RegShift : arm_reg -> nat -> operand2.  (* register + shift amount *)

(** ** ARM Condition Codes *)

(** Condition codes used by conditional branch instructions.
    These correspond to the ARM condition field encoding. *)

Inductive condition : Type :=
  | Cond_EQ   (* Equal: Z=1 *)
  | Cond_NE   (* Not equal: Z=0 *)
  | Cond_CS   (* Carry set / unsigned higher or same: C=1 *)
  | Cond_CC   (* Carry clear / unsigned lower: C=0 *)
  | Cond_MI   (* Minus / negative: N=1 *)
  | Cond_PL   (* Plus / positive or zero: N=0 *)
  | Cond_VS   (* Overflow: V=1 *)
  | Cond_VC   (* No overflow: V=0 *)
  | Cond_HI   (* Unsigned higher: C=1 and Z=0 *)
  | Cond_LS   (* Unsigned lower or same: C=0 or Z=1 *)
  | Cond_GE   (* Signed greater or equal: N=V *)
  | Cond_LT   (* Signed less than: N!=V *)
  | Cond_GT   (* Signed greater than: Z=0 and N=V *)
  | Cond_LE   (* Signed less or equal: Z=1 or N!=V *)
  | Cond_AL.  (* Always (unconditional) *)

(** ** ARM Instruction Set *)

Inductive arm_instr : Type :=
  (* Arithmetic operations *)
  | ADD : arm_reg -> arm_reg -> operand2 -> arm_instr
  | SUB : arm_reg -> arm_reg -> operand2 -> arm_instr
  | MUL : arm_reg -> arm_reg -> arm_reg -> arm_instr
  | SDIV : arm_reg -> arm_reg -> arm_reg -> arm_instr
  | UDIV : arm_reg -> arm_reg -> arm_reg -> arm_instr
  | MLS : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr
        (* MLS rd rn rm ra: rd = ra - (rn * rm) *)

  (* Multi-precision arithmetic — for i64 lo/hi pair codegen.
     These mirror Rust ArmOp::Adds / Adc / Subs / Sbc
     (synth-backend/src/arm_encoder.rs:80–114).
     ADDS sets the C flag from unsigned overflow of the low half;
     ADC reads that C flag while computing the high half.
     SUBS / SBC follow the same pattern with borrow. *)
  | ADDS : arm_reg -> arm_reg -> operand2 -> arm_instr  (* ADD setting flags *)
  | ADC  : arm_reg -> arm_reg -> operand2 -> arm_instr  (* ADD with carry, reads C *)
  | SUBS : arm_reg -> arm_reg -> operand2 -> arm_instr  (* SUB setting flags *)
  | SBC  : arm_reg -> arm_reg -> operand2 -> arm_instr  (* SUB with carry, reads C *)

  (* Bitwise operations *)
  | AND : arm_reg -> arm_reg -> operand2 -> arm_instr
  | ORR : arm_reg -> arm_reg -> operand2 -> arm_instr
  | EOR : arm_reg -> arm_reg -> operand2 -> arm_instr
  | MVN : arm_reg -> operand2 -> arm_instr

  (* Shift and rotate operations — immediate *)
  | LSL : arm_reg -> arm_reg -> nat -> arm_instr  (* Logical shift left *)
  | LSR : arm_reg -> arm_reg -> nat -> arm_instr  (* Logical shift right *)
  | ASR : arm_reg -> arm_reg -> nat -> arm_instr  (* Arithmetic shift right *)
  | ROR : arm_reg -> arm_reg -> nat -> arm_instr  (* Rotate right *)

  (* Shift and rotate operations — register *)
  | LSL_reg : arm_reg -> arm_reg -> arm_reg -> arm_instr  (* LSL Rd, Rn, Rm *)
  | LSR_reg : arm_reg -> arm_reg -> arm_reg -> arm_instr  (* LSR Rd, Rn, Rm *)
  | ASR_reg : arm_reg -> arm_reg -> arm_reg -> arm_instr  (* ASR Rd, Rn, Rm *)
  | ROR_reg : arm_reg -> arm_reg -> arm_reg -> arm_instr  (* ROR Rd, Rn, Rm *)

  (* Reverse subtract: RSB Rd, Rn, Op2 = Op2 - Rn *)
  | RSB : arm_reg -> arm_reg -> operand2 -> arm_instr

  (* Move operations *)
  | MOV : arm_reg -> operand2 -> arm_instr
  | MOVW : arm_reg -> I32.int -> arm_instr  (* Move 16-bit immediate *)
  | MOVT : arm_reg -> I32.int -> arm_instr  (* Move top 16 bits *)

  (* Conditional move operations *)
  | MOVEQ : arm_reg -> operand2 -> arm_instr  (* Move if equal (Z=1) *)
  | MOVNE : arm_reg -> operand2 -> arm_instr  (* Move if not equal (Z=0) *)
  | MOVLT : arm_reg -> operand2 -> arm_instr  (* Move if less than (signed) *)
  | MOVLE : arm_reg -> operand2 -> arm_instr  (* Move if less or equal (signed) *)
  | MOVGT : arm_reg -> operand2 -> arm_instr  (* Move if greater than (signed) *)
  | MOVGE : arm_reg -> operand2 -> arm_instr  (* Move if greater or equal (signed) *)
  | MOVLO : arm_reg -> operand2 -> arm_instr  (* Move if lower (unsigned) *)
  | MOVLS : arm_reg -> operand2 -> arm_instr  (* Move if lower or same (unsigned) *)
  | MOVHI : arm_reg -> operand2 -> arm_instr  (* Move if higher (unsigned) *)
  | MOVHS : arm_reg -> operand2 -> arm_instr  (* Move if higher or same (unsigned) *)

  (* Comparison operations *)
  | CMP : arm_reg -> operand2 -> arm_instr

  (* Bit manipulation *)
  | CLZ : arm_reg -> arm_reg -> arm_instr     (* Count leading zeros *)
  | RBIT : arm_reg -> arm_reg -> arm_instr    (* Reverse bits *)
  | POPCNT : arm_reg -> arm_reg -> arm_instr  (* Population count *)

  (* Memory operations *)
  | LDR : arm_reg -> arm_reg -> Z -> arm_instr   (* Load register *)
  | STR : arm_reg -> arm_reg -> Z -> arm_instr   (* Store register *)

  (* Trap *)
  | UDF : Z -> arm_instr        (* Undefined instruction — trap *)

  (* Compare Negated *)
  | CMN : arm_reg -> operand2 -> arm_instr  (* Compare Negated — sets flags for rn + op2 *)

  (* Control flow *)
  | B : Z -> arm_instr          (* Branch *)
  | BL : Z -> arm_instr         (* Branch with link *)
  | BX : arm_reg -> arm_instr   (* Branch and exchange *)
  | BCondOffset : condition -> Z -> arm_instr  (* Conditional branch with PC-relative offset *)

  (* VFP (Floating-point) operations *)
  | VADD_F32 : vfp_reg -> vfp_reg -> vfp_reg -> arm_instr
  | VSUB_F32 : vfp_reg -> vfp_reg -> vfp_reg -> arm_instr
  | VMUL_F32 : vfp_reg -> vfp_reg -> vfp_reg -> arm_instr
  | VDIV_F32 : vfp_reg -> vfp_reg -> vfp_reg -> arm_instr
  | VSQRT_F32 : vfp_reg -> vfp_reg -> arm_instr
  | VABS_F32 : vfp_reg -> vfp_reg -> arm_instr
  | VNEG_F32 : vfp_reg -> vfp_reg -> arm_instr

  | VADD_F64 : vfp_reg -> vfp_reg -> vfp_reg -> arm_instr
  | VSUB_F64 : vfp_reg -> vfp_reg -> vfp_reg -> arm_instr
  | VMUL_F64 : vfp_reg -> vfp_reg -> vfp_reg -> arm_instr
  | VDIV_F64 : vfp_reg -> vfp_reg -> vfp_reg -> arm_instr
  | VSQRT_F64 : vfp_reg -> vfp_reg -> arm_instr
  | VABS_F64 : vfp_reg -> vfp_reg -> arm_instr
  | VNEG_F64 : vfp_reg -> vfp_reg -> arm_instr

  (* VFP comparison and conversion *)
  | VCMP_F32 : vfp_reg -> vfp_reg -> arm_instr
  | VCMP_F64 : vfp_reg -> vfp_reg -> arm_instr
  | VCVT_F32_F64 : vfp_reg -> vfp_reg -> arm_instr
  | VCVT_F64_F32 : vfp_reg -> vfp_reg -> arm_instr
  | VCVT_S32_F32 : vfp_reg -> vfp_reg -> arm_instr
  | VCVT_F32_S32 : vfp_reg -> vfp_reg -> arm_instr

  (* VFP move operations *)
  | VMOV : vfp_reg -> vfp_reg -> arm_instr
  | VMOV_ARM_TO_VFP : vfp_reg -> arm_reg -> arm_instr
  | VMOV_VFP_TO_ARM : arm_reg -> vfp_reg -> arm_instr

  (* VFP memory operations *)
  | VLDR_F32 : vfp_reg -> arm_reg -> Z -> arm_instr
  | VSTR_F32 : vfp_reg -> arm_reg -> Z -> arm_instr
  | VLDR_F64 : vfp_reg -> arm_reg -> Z -> arm_instr
  | VSTR_F64 : vfp_reg -> arm_reg -> Z -> arm_instr

  (* ===== i64 high-level pseudo-instructions =====
     These mirror the ArmOp::I64* opcodes in
     crates/synth-synthesis/src/instruction_selector.rs (lines 1393–1786).
     In Rust they are *opaque pseudo-ops* whose encoded behavior is defined by
     the encoder, not by any single ARM instruction. The Coq model treats them
     analogously: each pseudo-op has axiomatized semantics in ArmSemantics.v
     that reads/writes the documented register pair. This parallels how VFP
     ops are axiomatized (see f32_*_bits).

     Convention (Rust hard-codes the same):
       i64 operand 1 in (rnlo, rnhi)
       i64 operand 2 in (rmlo, rmhi)
       i64 result    in (rdlo, rdhi)
  *)

  (* Multiplication: rd_lo:rd_hi = (rn_lo:rn_hi) * (rm_lo:rm_hi) *)
  | I64MulPseudo : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr
        (* I64MulPseudo rdlo rdhi rnlo rnhi rmlo rmhi *)

  (* Shifts/rotates: shift amount in (rmlo, rmhi) for shifts, in single reg for rotates *)
  | I64ShlPseudo  : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr
  | I64ShrUPseudo : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr
  | I64ShrSPseudo : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr
  | I64RotlPseudo : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr
        (* I64RotlPseudo rdlo rdhi rnlo rnhi shift *)
  | I64RotrPseudo : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr

  (* Bit manipulation: rd is a single 32-bit count register (clz/ctz/popcnt of i64 fit in 32 bits) *)
  | I64ClzPseudo    : arm_reg -> arm_reg -> arm_reg -> arm_instr
        (* I64ClzPseudo rd rnlo rnhi *)
  | I64CtzPseudo    : arm_reg -> arm_reg -> arm_reg -> arm_instr
  | I64PopcntPseudo : arm_reg -> arm_reg -> arm_reg -> arm_instr

  (* Comparisons: rd receives 0/1; reads (rnlo, rnhi) vs (rmlo, rmhi).
     The condition field selects which i64 comparison (EQ/NE/LT/LE/GT/GE in signed and
     unsigned variants). For I64SetCondZ (unary i64.eqz) there is no rm pair. *)
  | I64SetCond  : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> condition -> arm_instr
        (* I64SetCond rd rnlo rnhi rmlo rmhi cond *)
  | I64SetCondZ : arm_reg -> arm_reg -> arm_reg -> arm_instr
        (* I64SetCondZ rd rnlo rnhi *)

  (* Division / remainder: trap semantics (returns None) on divide-by-zero / signed overflow.
     The Rust encoder lowers these to software helper calls (gale runtime
     __aeabi_ldivmod / __aeabi_uldivmod on Cortex-M); the Coq model treats them as
     opaque pseudo-ops with axiomatized result. *)
  | I64DivSPseudo : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr
  | I64DivUPseudo : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr
  | I64RemSPseudo : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr
  | I64RemUPseudo : arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_reg -> arm_instr

  (* Constants: I64Const loads both halves *)
  | I64ConstPseudo : arm_reg -> arm_reg -> I64.int -> arm_instr
        (* I64ConstPseudo rdlo rdhi value *)

  (* Conversions: sign/zero-extend i32 -> i64; wrap i64 -> i32 (drops high half) *)
  | I64ExtendI32SPseudo : arm_reg -> arm_reg -> arm_reg -> arm_instr
        (* I64ExtendI32SPseudo rdlo rdhi rn *)
  | I64ExtendI32UPseudo : arm_reg -> arm_reg -> arm_reg -> arm_instr
  | I32WrapI64Pseudo    : arm_reg -> arm_reg -> arm_instr
        (* I32WrapI64Pseudo rd rnlo — keeps low half, drops high half *)

  (* Memory: 8-byte load/store *)
  | I64LoadPseudo  : arm_reg -> arm_reg -> arm_reg -> Z -> arm_instr
        (* I64LoadPseudo rdlo rdhi addr offset *)
  | I64StorePseudo : arm_reg -> arm_reg -> arm_reg -> Z -> arm_instr.
        (* I64StorePseudo rnlo rnhi addr offset *)

(** ** Instruction Sequences *)

Definition arm_program := list arm_instr.

(** ** Helper Functions *)

(** Evaluate operand2 *)
Definition eval_operand2 (op2 : operand2) (s : arm_state) : I32.int :=
  match op2 with
  | Imm n => n
  | Reg r => get_reg s r
  | RegShift r shift =>
      (* Simplified: just return register value, ignoring shift for now *)
      get_reg s r
  end.

(** Evaluate a condition code against the current condition flags *)
Definition eval_condition (cond : condition) (f : condition_flags) : bool :=
  match cond with
  | Cond_EQ => f.(flag_z)
  | Cond_NE => negb f.(flag_z)
  | Cond_CS => f.(flag_c)
  | Cond_CC => negb f.(flag_c)
  | Cond_MI => f.(flag_n)
  | Cond_PL => negb f.(flag_n)
  | Cond_VS => f.(flag_v)
  | Cond_VC => negb f.(flag_v)
  | Cond_HI => f.(flag_c) && negb f.(flag_z)
  | Cond_LS => negb f.(flag_c) || f.(flag_z)
  | Cond_GE => Bool.eqb f.(flag_n) f.(flag_v)
  | Cond_LT => negb (Bool.eqb f.(flag_n) f.(flag_v))
  | Cond_GT => negb f.(flag_z) && Bool.eqb f.(flag_n) f.(flag_v)
  | Cond_LE => f.(flag_z) || negb (Bool.eqb f.(flag_n) f.(flag_v))
  | Cond_AL => true
  end.

(** ** Examples of Common Instructions *)

(** ADD R0, R1, R2: R0 = R1 + R2 *)
Definition ex_add_regs : arm_instr := ADD R0 R1 (Reg R2).

(** ADD R0, R0, #1: R0 = R0 + 1 *)
Definition ex_add_imm : arm_instr := ADD R0 R0 (Imm I32.one).

(** SUB R0, R0, R1: R0 = R0 - R1 *)
Definition ex_sub_regs : arm_instr := SUB R0 R0 (Reg R1).

(** AND R0, R1, R2: R0 = R1 & R2 *)
Definition ex_and_regs : arm_instr := AND R0 R1 (Reg R2).

(** MOV R0, R1: R0 = R1 *)
Definition ex_mov_reg : arm_instr := MOV R0 (Reg R1).

(** LSL R0, R1, #4: R0 = R1 << 4 *)
Definition ex_lsl : arm_instr := LSL R0 R1 4.
