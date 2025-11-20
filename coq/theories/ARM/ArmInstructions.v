(** * ARM Instructions

    This file defines the ARM instruction set that Synth targets.
    Based on synth-synthesis/src/rules.rs
*)

From Stdlib Require Import ZArith.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.

Open Scope Z_scope.

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

  (* Bitwise operations *)
  | AND : arm_reg -> arm_reg -> operand2 -> arm_instr
  | ORR : arm_reg -> arm_reg -> operand2 -> arm_instr
  | EOR : arm_reg -> arm_reg -> operand2 -> arm_instr
  | MVN : arm_reg -> operand2 -> arm_instr

  (* Shift and rotate operations *)
  | LSL : arm_reg -> arm_reg -> nat -> arm_instr  (* Logical shift left *)
  | LSR : arm_reg -> arm_reg -> nat -> arm_instr  (* Logical shift right *)
  | ASR : arm_reg -> arm_reg -> nat -> arm_instr  (* Arithmetic shift right *)
  | ROR : arm_reg -> arm_reg -> nat -> arm_instr  (* Rotate right *)

  (* Move operations *)
  | MOV : arm_reg -> operand2 -> arm_instr
  | MOVW : arm_reg -> I32.int -> arm_instr  (* Move 16-bit immediate *)
  | MOVT : arm_reg -> I32.int -> arm_instr  (* Move top 16 bits *)

  (* Conditional move operations *)
  | MOVEQ : arm_reg -> operand2 -> arm_instr  (* Move if equal (Z=1) *)
  | MOVNE : arm_reg -> operand2 -> arm_instr  (* Move if not equal (Z=0) *)

  (* Comparison operations *)
  | CMP : arm_reg -> operand2 -> arm_instr

  (* Bit manipulation *)
  | CLZ : arm_reg -> arm_reg -> arm_instr     (* Count leading zeros *)
  | RBIT : arm_reg -> arm_reg -> arm_instr    (* Reverse bits *)
  | POPCNT : arm_reg -> arm_reg -> arm_instr  (* Population count *)

  (* Memory operations *)
  | LDR : arm_reg -> arm_reg -> Z -> arm_instr   (* Load register *)
  | STR : arm_reg -> arm_reg -> Z -> arm_instr   (* Store register *)

  (* Control flow *)
  | B : Z -> arm_instr          (* Branch *)
  | BL : Z -> arm_instr         (* Branch with link *)
  | BX : arm_reg -> arm_instr   (* Branch and exchange *)

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
  | VSTR_F64 : vfp_reg -> arm_reg -> Z -> arm_instr.

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
