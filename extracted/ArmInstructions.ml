open ArmState
open Integers

type operand2 =
| Imm of I32.int
| Reg of arm_reg
| RegShift of arm_reg * int

type arm_instr =
| ADD of arm_reg * arm_reg * operand2
| SUB of arm_reg * arm_reg * operand2
| MUL of arm_reg * arm_reg * arm_reg
| SDIV of arm_reg * arm_reg * arm_reg
| UDIV of arm_reg * arm_reg * arm_reg
| MLS of arm_reg * arm_reg * arm_reg * arm_reg
| AND of arm_reg * arm_reg * operand2
| ORR of arm_reg * arm_reg * operand2
| EOR of arm_reg * arm_reg * operand2
| MVN of arm_reg * operand2
| LSL of arm_reg * arm_reg * int
| LSR of arm_reg * arm_reg * int
| ASR of arm_reg * arm_reg * int
| ROR of arm_reg * arm_reg * int
| MOV of arm_reg * operand2
| MOVW of arm_reg * I32.int
| MOVT of arm_reg * I32.int
| CMP of arm_reg * operand2
| CLZ of arm_reg * arm_reg
| RBIT of arm_reg * arm_reg
| POPCNT of arm_reg * arm_reg
| LDR of arm_reg * arm_reg * int
| STR of arm_reg * arm_reg * int
| B of int
| BL of int
| BX of arm_reg
| VADD_F32 of vfp_reg * vfp_reg * vfp_reg
| VSUB_F32 of vfp_reg * vfp_reg * vfp_reg
| VMUL_F32 of vfp_reg * vfp_reg * vfp_reg
| VDIV_F32 of vfp_reg * vfp_reg * vfp_reg
| VSQRT_F32 of vfp_reg * vfp_reg
| VABS_F32 of vfp_reg * vfp_reg
| VNEG_F32 of vfp_reg * vfp_reg
| VADD_F64 of vfp_reg * vfp_reg * vfp_reg
| VSUB_F64 of vfp_reg * vfp_reg * vfp_reg
| VMUL_F64 of vfp_reg * vfp_reg * vfp_reg
| VDIV_F64 of vfp_reg * vfp_reg * vfp_reg
| VSQRT_F64 of vfp_reg * vfp_reg
| VABS_F64 of vfp_reg * vfp_reg
| VNEG_F64 of vfp_reg * vfp_reg
| VCMP_F32 of vfp_reg * vfp_reg
| VCMP_F64 of vfp_reg * vfp_reg
| VCVT_F32_F64 of vfp_reg * vfp_reg
| VCVT_F64_F32 of vfp_reg * vfp_reg
| VCVT_S32_F32 of vfp_reg * vfp_reg
| VCVT_F32_S32 of vfp_reg * vfp_reg
| VMOV of vfp_reg * vfp_reg
| VMOV_ARM_TO_VFP of vfp_reg * arm_reg
| VMOV_VFP_TO_ARM of arm_reg * vfp_reg
| VLDR_F32 of vfp_reg * arm_reg * int
| VSTR_F32 of vfp_reg * arm_reg * int
| VLDR_F64 of vfp_reg * arm_reg * int
| VSTR_F64 of vfp_reg * arm_reg * int

type arm_program = arm_instr list

(** val eval_operand2 : operand2 -> arm_state -> I32.int **)

let eval_operand2 op2 s =
  match op2 with
  | Imm n -> n
  | Reg r -> get_reg s r
  | RegShift (r, _) -> get_reg s r
