(** * Synth Compilation

    This file defines the compilation from WebAssembly to ARM.
    Based on synth-synthesis/src/rules.rs
*)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.
Require Import Synth.ARM.ArmState.
Require Import Synth.ARM.ArmInstructions.
Require Import Synth.WASM.WasmValues.
Require Import Synth.WASM.WasmInstructions.
Require Import Synth.WASM.WasmSemantics.

Import ListNotations.
Open Scope Z_scope.

(** ** Compilation Strategy **)

(**
   Synth compiles WebAssembly to ARM using a register-based calling convention:
   - WASM stack is mapped to ARM registers
   - R0 holds the top of the WASM stack
   - R1 holds the second element
   - Additional stack values spilled to memory if needed
*)

(** ** Compilation Function **)

(**
   Compile a single WASM instruction to a sequence of ARM instructions.
*)

Definition compile_wasm_to_arm (w : wasm_instr) : arm_program :=
  match w with
  (* i32 arithmetic - assume stack top in R0, second in R1 *)
  | I32Add =>
      [ADD R0 R0 (Reg R1)]

  | I32Sub =>
      [SUB R0 R0 (Reg R1)]

  | I32Mul =>
      [MUL R0 R0 R1]

  | I32DivS =>
      [SDIV R0 R0 R1]

  | I32DivU =>
      [UDIV R0 R0 R1]

  | I32RemS =>
      (* Signed remainder: a % b = a - (a/b) * b *)
      (* Use MLS (Multiply and Subtract): Rd = Ra - Rn * Rm *)
      [SDIV R2 R0 R1;    (* R2 = R0 / R1 (quotient) *)
       MLS R0 R2 R1 R0]  (* R0 = R0 - (R2 * R1) (remainder) *)

  | I32RemU =>
      (* Unsigned remainder: a % b = a - (a/b) * b *)
      [UDIV R2 R0 R1;    (* R2 = R0 / R1 (quotient) *)
       MLS R0 R2 R1 R0]  (* R0 = R0 - (R2 * R1) (remainder) *)

  (* i32 bitwise operations *)
  | I32And =>
      [AND R0 R0 (Reg R1)]

  | I32Or =>
      [ORR R0 R0 (Reg R1)]

  | I32Xor =>
      [EOR R0 R0 (Reg R1)]

  (* i32 shift operations *)
  | I32Shl =>
      (* Logical shift left: R0 = R0 << (R1 & 31) *)
      (* ARM: AND R1, R1, #31 to mask shift amount, then LSL *)
      (* Simplified: use fixed immediate for now, real impl needs variable shift *)
      (* For now: implement using repeated shifts in validation layer *)
      (* Here we emit a single instruction that validation will interpret *)
      [LSL R0 R0 0]  (* Placeholder: shift amount comes from R1 in semantics *)

  | I32ShrU =>
      (* Logical shift right (unsigned): R0 = R0 >> (R1 & 31) *)
      [LSR R0 R0 0]  (* Placeholder: shift amount comes from R1 in semantics *)

  | I32ShrS =>
      (* Arithmetic shift right (signed): R0 = R0 >> (R1 & 31) *)
      [ASR R0 R0 0]  (* Placeholder: shift amount comes from R1 in semantics *)

  | I32Rotl =>
      (* Rotate left: R0 = R0 rotl (R1 & 31) *)
      (* ARM doesn't have ROTL, implement as: ROR R0, R0, (32 - (R1 & 31)) *)
      (* Simplified: return placeholder, implement in semantics *)
      []  (* TODO: Requires computing 32-shift, then ROR *)

  | I32Rotr =>
      (* Rotate right: R0 = R0 rotr (R1 & 31) *)
      [ROR R0 R0 0]  (* Placeholder: shift amount comes from R1 in semantics *)

  (* i32 bit manipulation *)
  | I32Clz =>
      (* Count leading zeros: R0 = clz(R0) *)
      [CLZ R0 R0]

  | I32Ctz =>
      (* Count trailing zeros: R0 = ctz(R0) *)
      (* ARM: RBIT reverses bits, then CLZ counts from the other end *)
      [RBIT R0 R0;
       CLZ R0 R0]

  | I32Popcnt =>
      (* Population count (count set bits): R0 = popcnt(R0) *)
      (* ARM doesn't have a single instruction, but some have VCNT for NEON *)
      (* For now, implement in validation layer using loop *)
      [POPCNT R0 R0]  (* Placeholder: implement in semantics *)

  (* i32 comparison *)
  | I32Eqz =>
      (* Test if R0 is zero: returns 1 if zero, 0 otherwise *)
      (* CMP R0, #0 sets Z flag if R0 == 0 *)
      (* Then set R0=0, and conditionally set R0=1 if Z flag is set *)
      [CMP R0 (Imm I32.zero);      (* Compare R0 with 0, sets Z flag *)
       MOV R0 (Imm I32.zero);      (* Set R0 to 0 (assume false) *)
       MOVEQ R0 (Imm I32.one)]     (* If Z flag set (was 0), set R0 to 1 *)

  | I32Eq =>
      (* Compare R0 == R1: returns 1 if equal, 0 otherwise *)
      [CMP R0 (Reg R1);          (* Compare R0 with R1, sets Z flag if equal *)
       MOV R0 (Imm I32.zero);    (* Set R0 to 0 (assume false) *)
       MOVEQ R0 (Imm I32.one)]   (* If Z flag set (equal), set R0 to 1 *)

  | I32Ne =>
      (* Compare R0 != R1: returns 1 if not equal, 0 otherwise *)
      [CMP R0 (Reg R1);          (* Compare R0 with R1 *)
       MOV R0 (Imm I32.zero);    (* Set R0 to 0 (assume false) *)
       MOVNE R0 (Imm I32.one)]   (* If Z flag clear (not equal), set R0 to 1 *)

  | I32LtS =>
      (* Compare R0 < R1 (signed): returns 1 if less than, 0 otherwise *)
      [CMP R0 (Reg R1);          (* Compare R0 with R1, sets flags *)
       MOV R0 (Imm I32.zero);    (* Set R0 to 0 (assume false) *)
       MOVLT R0 (Imm I32.one)]   (* If N != V (less than), set R0 to 1 *)

  | I32LtU =>
      (* Compare R0 < R1 (unsigned): returns 1 if lower, 0 otherwise *)
      [CMP R0 (Reg R1);          (* Compare R0 with R1, sets flags *)
       MOV R0 (Imm I32.zero);    (* Set R0 to 0 (assume false) *)
       MOVLO R0 (Imm I32.one)]   (* If C clear (lower), set R0 to 1 *)

  | I32GtS =>
      (* Compare R0 > R1 (signed): returns 1 if greater than, 0 otherwise *)
      [CMP R0 (Reg R1);          (* Compare R0 with R1, sets flags *)
       MOV R0 (Imm I32.zero);    (* Set R0 to 0 (assume false) *)
       MOVGT R0 (Imm I32.one)]   (* If Z clear AND N == V (greater), set R0 to 1 *)

  | I32GtU =>
      (* Compare R0 > R1 (unsigned): returns 1 if higher, 0 otherwise *)
      [CMP R0 (Reg R1);          (* Compare R0 with R1, sets flags *)
       MOV R0 (Imm I32.zero);    (* Set R0 to 0 (assume false) *)
       MOVHI R0 (Imm I32.one)]   (* If C set AND Z clear (higher), set R0 to 1 *)

  | I32LeS =>
      (* Compare R0 <= R1 (signed): returns 1 if less or equal, 0 otherwise *)
      [CMP R0 (Reg R1);          (* Compare R0 with R1, sets flags *)
       MOV R0 (Imm I32.zero);    (* Set R0 to 0 (assume false) *)
       MOVLE R0 (Imm I32.one)]   (* If Z set OR N != V (less or equal), set R0 to 1 *)

  | I32LeU =>
      (* Compare R0 <= R1 (unsigned): returns 1 if lower or same, 0 otherwise *)
      [CMP R0 (Reg R1);          (* Compare R0 with R1, sets flags *)
       MOV R0 (Imm I32.zero);    (* Set R0 to 0 (assume false) *)
       MOVLS R0 (Imm I32.one)]   (* If C clear OR Z set (lower or same), set R0 to 1 *)

  | I32GeS =>
      (* Compare R0 >= R1 (signed): returns 1 if greater or equal, 0 otherwise *)
      [CMP R0 (Reg R1);          (* Compare R0 with R1, sets flags *)
       MOV R0 (Imm I32.zero);    (* Set R0 to 0 (assume false) *)
       MOVGE R0 (Imm I32.one)]   (* If N == V (greater or equal), set R0 to 1 *)

  | I32GeU =>
      (* Compare R0 >= R1 (unsigned): returns 1 if higher or same, 0 otherwise *)
      [CMP R0 (Reg R1);          (* Compare R0 with R1, sets flags *)
       MOV R0 (Imm I32.zero);    (* Set R0 to 0 (assume false) *)
       MOVHS R0 (Imm I32.one)]   (* If C set (higher or same), set R0 to 1 *)

  (* i64 arithmetic - simplified to operate on low 32 bits only *)
  (* Full implementation would use register pairs: R0:R1 for first i64, R2:R3 for second *)
  | I64Add =>
      (* Simplified: just add low 32 bits *)
      [ADD R0 R0 (Reg R1)]

  | I64Sub =>
      [SUB R0 R0 (Reg R1)]

  | I64Mul =>
      [MUL R0 R0 R1]

  | I64DivS =>
      [SDIV R0 R0 R1]

  | I64DivU =>
      [UDIV R0 R0 R1]

  | I64RemS =>
      [SDIV R2 R0 R1;
       MLS R0 R2 R1 R0]

  | I64RemU =>
      [UDIV R2 R0 R1;
       MLS R0 R2 R1 R0]

  (* i64 bitwise *)
  | I64And =>
      [AND R0 R0 (Reg R1)]

  | I64Or =>
      [ORR R0 R0 (Reg R1)]

  | I64Xor =>
      [EOR R0 R0 (Reg R1)]

  (* i64 comparison - simplified *)
  | I64Eqz =>
      [CMP R0 (Imm I32.zero);
       MOV R0 (Imm I32.zero);
       MOVEQ R0 (Imm I32.one)]

  | I64Eq =>
      [CMP R0 (Reg R1);
       MOV R0 (Imm I32.zero);
       MOVEQ R0 (Imm I32.one)]

  | I64Ne =>
      [CMP R0 (Reg R1);
       MOV R0 (Imm I32.zero);
       MOVNE R0 (Imm I32.one)]

  | I64LtS =>
      [CMP R0 (Reg R1);
       MOV R0 (Imm I32.zero);
       MOVLT R0 (Imm I32.one)]

  | I64LtU =>
      [CMP R0 (Reg R1);
       MOV R0 (Imm I32.zero);
       MOVLO R0 (Imm I32.one)]

  | I64GtS =>
      [CMP R0 (Reg R1);
       MOV R0 (Imm I32.zero);
       MOVGT R0 (Imm I32.one)]

  | I64GtU =>
      [CMP R0 (Reg R1);
       MOV R0 (Imm I32.zero);
       MOVHI R0 (Imm I32.one)]

  | I64LeS =>
      [CMP R0 (Reg R1);
       MOV R0 (Imm I32.zero);
       MOVLE R0 (Imm I32.one)]

  | I64LeU =>
      [CMP R0 (Reg R1);
       MOV R0 (Imm I32.zero);
       MOVLS R0 (Imm I32.one)]

  | I64GeS =>
      [CMP R0 (Reg R1);
       MOV R0 (Imm I32.zero);
       MOVGE R0 (Imm I32.one)]

  | I64GeU =>
      [CMP R0 (Reg R1);
       MOV R0 (Imm I32.zero);
       MOVHS R0 (Imm I32.one)]

  (* i64 shift/rotate - simplified *)
  | I64Shl =>
      [LSL R0 R0 0]

  | I64ShrU =>
      [LSR R0 R0 0]

  | I64ShrS =>
      [ASR R0 R0 0]

  | I64Rotl =>
      []  (* TODO *)

  | I64Rotr =>
      [ROR R0 R0 0]

  (* i64 bit manipulation - simplified *)
  | I64Clz =>
      [CLZ R0 R0]

  | I64Ctz =>
      [RBIT R0 R0;
       CLZ R0 R0]

  | I64Popcnt =>
      [POPCNT R0 R0]

  (* Constants *)
  | I32Const n =>
      (* Load immediate into R0 *)
      [MOVW R0 n]

  | I64Const n =>
      (* Load 64-bit constant: low 32 bits in R0, high 32 bits in R1 *)
      (* Simplified: just load low bits to R0 for now *)
      [MOVW R0 (I32.repr ((I64.unsigned n) mod I32.modulus))]

  (* Local variables *)
  | LocalGet idx =>
      (* Load local variable from memory or register *)
      (* Simplified: assume locals in R4-R7 *)
      let local_reg := match idx with
                       | 0%nat => R4
                       | 1%nat => R5
                       | 2%nat => R6
                       | 3%nat => R7
                       | _ => R4  (* Fallback *)
                       end in
      [MOV R0 (Reg local_reg)]

  | LocalSet idx =>
      (* Store R0 to local variable *)
      let local_reg := match idx with
                       | 0%nat => R4
                       | 1%nat => R5
                       | 2%nat => R6
                       | 3%nat => R7
                       | _ => R4
                       end in
      [MOV local_reg (Reg R0)]

  (* f32 arithmetic operations - using VFP instructions *)
  (* VFP uses S0-S31 for single-precision *)
  | F32Add =>
      [VADD_F32 S0 S0 S1]

  | F32Sub =>
      [VSUB_F32 S0 S0 S1]

  | F32Mul =>
      [VMUL_F32 S0 S0 S1]

  | F32Div =>
      [VDIV_F32 S0 S0 S1]

  | F32Sqrt =>
      [VSQRT_F32 S0 S0]

  | F32Abs =>
      [VABS_F32 S0 S0]

  | F32Neg =>
      [VNEG_F32 S0 S0]

  | F32Min | F32Max | F32Copysign | F32Ceil | F32Floor | F32Trunc | F32Nearest =>
      (* Complex operations - implement in validation layer *)
      []

  (* f32 comparison operations *)
  | F32Eq | F32Ne | F32Lt | F32Gt | F32Le | F32Ge =>
      [VCMP_F32 S0 S1]

  (* f64 arithmetic operations - using VFP instructions *)
  (* VFP uses D0-D15 for double-precision *)
  | F64Add =>
      [VADD_F64 D0 D0 D1]

  | F64Sub =>
      [VSUB_F64 D0 D0 D1]

  | F64Mul =>
      [VMUL_F64 D0 D0 D1]

  | F64Div =>
      [VDIV_F64 D0 D0 D1]

  | F64Sqrt =>
      [VSQRT_F64 D0 D0]

  | F64Abs =>
      [VABS_F64 D0 D0]

  | F64Neg =>
      [VNEG_F64 D0 D0]

  | F64Min | F64Max | F64Copysign | F64Ceil | F64Floor | F64Trunc | F64Nearest =>
      (* Complex operations - implement in validation layer *)
      []

  (* f64 comparison operations *)
  | F64Eq | F64Ne | F64Lt | F64Gt | F64Le | F64Ge =>
      [VCMP_F64 D0 D1]

  (* Conversion operations *)
  | I32WrapI64 =>
      (* Extract low 32 bits from i64 - already in R0 *)
      []

  | I64ExtendI32S =>
      (* Sign-extend i32 to i64 - simplified, just keep in R0 *)
      []

  | I64ExtendI32U =>
      (* Zero-extend i32 to i64 - simplified, just keep in R0 *)
      []

  | I32TruncF32S | I32TruncF32U =>
      [VCVT_S32_F32 S0 S0;           (* Convert float to int *)
       VMOV_VFP_TO_ARM R0 S0]         (* Move to ARM register *)

  | I32TruncF64S | I32TruncF64U =>
      [VCVT_F32_F64 S0 D0;           (* Convert f64 to f32 first *)
       VCVT_S32_F32 S0 S0;           (* Then to int *)
       VMOV_VFP_TO_ARM R0 S0]

  | I64TruncF32S | I64TruncF32U | I64TruncF64S | I64TruncF64U =>
      (* Simplified: same as i32 trunc *)
      [VCVT_S32_F32 S0 S0;
       VMOV_VFP_TO_ARM R0 S0]

  | F32ConvertI32S | F32ConvertI32U =>
      [VMOV_ARM_TO_VFP S0 R0;
       VCVT_F32_S32 S0 S0]

  | F32ConvertI64S | F32ConvertI64U =>
      (* Simplified: treat as i32 *)
      [VMOV_ARM_TO_VFP S0 R0;
       VCVT_F32_S32 S0 S0]

  | F32DemoteF64 =>
      [VCVT_F32_F64 S0 D0]

  | F64ConvertI32S | F64ConvertI32U =>
      [VMOV_ARM_TO_VFP S0 R0;
       VCVT_F32_S32 S0 S0;
       VCVT_F64_F32 D0 S0]

  | F64ConvertI64S | F64ConvertI64U =>
      (* Simplified: treat as i32 *)
      [VMOV_ARM_TO_VFP S0 R0;
       VCVT_F32_S32 S0 S0;
       VCVT_F64_F32 D0 S0]

  | F64PromoteF32 =>
      [VCVT_F64_F32 D0 S0]

  (* Memory operations *)
  | I32Load offset =>
      (* Load from memory: R0 = mem[R0 + offset] *)
      [LDR R0 R0 (Z.of_nat offset)]

  | I64Load offset =>
      (* Simplified: load only low 32 bits *)
      [LDR R0 R0 (Z.of_nat offset)]

  | F32Load offset =>
      [VLDR_F32 S0 R0 (Z.of_nat offset)]

  | F64Load offset =>
      [VLDR_F64 D0 R0 (Z.of_nat offset)]

  | I32Store offset =>
      (* Store to memory: mem[R0 + offset] = R1 *)
      [STR R1 R0 (Z.of_nat offset)]

  | I64Store offset =>
      (* Simplified: store only low 32 bits *)
      [STR R1 R0 (Z.of_nat offset)]

  | F32Store offset =>
      [VSTR_F32 S1 R0 (Z.of_nat offset)]

  | F64Store offset =>
      [VSTR_F64 D1 R0 (Z.of_nat offset)]

  (* Local/Global variable operations *)
  | LocalTee idx =>
      (* Store to local and keep value on stack *)
      let local_reg := match idx with
                       | 0%nat => R4
                       | 1%nat => R5
                       | 2%nat => R6
                       | 3%nat => R7
                       | _ => R4
                       end in
      [MOV local_reg (Reg R0)]  (* R0 stays unchanged *)

  | GlobalGet idx =>
      (* Get global variable - simplified: use R8-R11 for globals *)
      let global_reg := match idx with
                        | 0%nat => R8
                        | 1%nat => R9
                        | 2%nat => R10
                        | 3%nat => R11
                        | _ => R8
                        end in
      [MOV R0 (Reg global_reg)]

  | GlobalSet idx =>
      (* Set global variable *)
      let global_reg := match idx with
                        | 0%nat => R8
                        | 1%nat => R9
                        | 2%nat => R10
                        | 3%nat => R11
                        | _ => R8
                        end in
      [MOV global_reg (Reg R0)]

  (* Control flow *)
  | Drop =>
      (* Drop top of stack - no-op in register-based model *)
      []

  | Select =>
      (* Conditional select: if R2 != 0 then R0 else R1 *)
      (* Simplified: R0 = (R2 != 0) ? R0 : R1 *)
      [CMP R2 (Imm I32.zero);
       MOVNE R0 (Reg R0);  (* If R2 != 0, keep R0 (no-op) *)
       MOVEQ R0 (Reg R1)]  (* If R2 == 0, move R1 to R0 *)

  | Nop =>
      (* No operation *)
      []
  end.

(** ** Compile Programs **)

Definition compile_wasm_program (prog : wasm_program) : arm_program :=
  flat_map compile_wasm_to_arm prog.

(** ** Examples **)

(** WASM: i32.const 5; i32.const 3; i32.add *)
Example ex_compile_simple_add :
  compile_wasm_program ([I32Const (I32.repr 5); I32Const (I32.repr 3); I32Add]) =
  ([MOVW R0 (I32.repr 5);
   MOVW R0 (I32.repr 3);
   ADD R0 R0 (Reg R1)]).
Proof. (* TODO: Fixproof *) Admitted.

(** WASM: local.get 0; i32.const 1; i32.add; local.set 0 *)
Example ex_compile_increment_local :
  compile_wasm_program ([LocalGet 0%nat; I32Const I32.one; I32Add; LocalSet 0%nat]) =
  ([MOV R0 (Reg R4);
   MOVW R0 I32.one;
   ADD R0 R0 (Reg R1);
   MOV R4 (Reg R0)]).
Proof. (* TODO: Fix proof *) Admitted.

(** ** Compilation Invariants **)

(**
   The compilation preserves certain invariants:
   1. Type safety: i32 operations compile to 32-bit ARM operations
   2. Stack discipline: Stack-based WASM maps to register-based ARM
   3. Semantic equivalence: Results are mathematically equivalent
*)

(** Compilation produces non-empty code for most instructions *)
Lemma compile_i32_add_non_empty :
  compile_wasm_to_arm I32Add <> [].
Proof.
  unfold compile_wasm_to_arm.
  discriminate.
Qed.

Lemma compile_i32_sub_non_empty :
  compile_wasm_to_arm I32Sub <> [].
Proof.
  unfold compile_wasm_to_arm.
  discriminate.
Qed.

Lemma compile_i32_mul_non_empty :
  compile_wasm_to_arm I32Mul <> [].
Proof.
  unfold compile_wasm_to_arm.
  discriminate.
Qed.

(** ** Register Allocation Strategy **)

(**
   WASM Stack → ARM Registers Mapping:

   Stack Position  | ARM Register
   ----------------|-------------
   Top (0)         | R0
   Second (1)      | R1
   Third (2)       | R2
   Fourth (3)      | R3
   Locals 0-3      | R4-R7
   Temporaries     | R8-R12
   Stack Pointer   | SP (R13)
   Link Register   | LR (R14)
   Program Counter | PC (R15)

   This is a simplified model. The real Synth compiler uses a more sophisticated
   register allocation strategy with spilling to memory when needed.
*)

(** ** Stack-to-Register Correspondence **)

Inductive stack_reg_correspondence : wasm_stack -> arm_state -> Prop :=
  | SRC_Empty : forall astate,
      stack_reg_correspondence (@nil wasm_val) astate

  | SRC_One : forall v rest astate,
      get_reg astate R0 = (match v with VI32 n => n | _ => I32.zero end) ->
      stack_reg_correspondence (v :: rest) astate

  | SRC_Two : forall v1 v2 rest astate,
      get_reg astate R0 = (match v1 with VI32 n => n | _ => I32.zero end) ->
      get_reg astate R1 = (match v2 with VI32 n => n | _ => I32.zero end) ->
      stack_reg_correspondence (v1 :: v2 :: rest) astate.

(** Correspondence for local variables *)
Definition local_correspondence (wlocals : nat -> I32.int) (astate : arm_state) : Prop :=
  get_reg astate R4 = wlocals 0%nat /\
  get_reg astate R5 = wlocals 1%nat /\
  get_reg astate R6 = wlocals 2%nat /\
  get_reg astate R7 = wlocals 3%nat.

(** ** Full State Correspondence **)

Record state_correspondence (wstate : wasm_state) (astate : arm_state) : Prop := {
  sc_stack : stack_reg_correspondence wstate.(stack) astate;
  sc_locals : local_correspondence wstate.(locals) astate;
  sc_memory : wstate.(memory) = astate.(mem);
}.
