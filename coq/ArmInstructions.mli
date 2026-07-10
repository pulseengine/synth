open ArmState
open Bool
open Datatypes
open Integers

type operand2 =
| Imm of I32.int
| Reg of arm_reg
| RegShift of arm_reg * int

type condition =
| Cond_EQ
| Cond_NE
| Cond_CS
| Cond_CC
| Cond_MI
| Cond_PL
| Cond_VS
| Cond_VC
| Cond_HI
| Cond_LS
| Cond_GE
| Cond_LT
| Cond_GT
| Cond_LE
| Cond_AL

type arm_instr =
| ADD of arm_reg * arm_reg * operand2
| SUB of arm_reg * arm_reg * operand2
| MUL of arm_reg * arm_reg * arm_reg
| SDIV of arm_reg * arm_reg * arm_reg
| UDIV of arm_reg * arm_reg * arm_reg
| MLS of arm_reg * arm_reg * arm_reg * arm_reg
| ADDS of arm_reg * arm_reg * operand2
| ADC of arm_reg * arm_reg * operand2
| SUBS of arm_reg * arm_reg * operand2
| SBC of arm_reg * arm_reg * operand2
| SBCS of arm_reg * arm_reg * operand2
| AND of arm_reg * arm_reg * operand2
| ORR of arm_reg * arm_reg * operand2
| EOR of arm_reg * arm_reg * operand2
| MVN of arm_reg * operand2
| LSL of arm_reg * arm_reg * int
| LSR of arm_reg * arm_reg * int
| ASR of arm_reg * arm_reg * int
| ROR of arm_reg * arm_reg * int
| LSL_reg of arm_reg * arm_reg * arm_reg
| LSR_reg of arm_reg * arm_reg * arm_reg
| ASR_reg of arm_reg * arm_reg * arm_reg
| ROR_reg of arm_reg * arm_reg * arm_reg
| RSB of arm_reg * arm_reg * operand2
| MOV of arm_reg * operand2
| MOVW of arm_reg * I32.int
| MOVT of arm_reg * I32.int
| MOVEQ of arm_reg * operand2
| MOVNE of arm_reg * operand2
| MOVLT of arm_reg * operand2
| MOVLE of arm_reg * operand2
| MOVGT of arm_reg * operand2
| MOVGE of arm_reg * operand2
| MOVLO of arm_reg * operand2
| MOVLS of arm_reg * operand2
| MOVHI of arm_reg * operand2
| MOVHS of arm_reg * operand2
| CMP of arm_reg * operand2
| CMPCond of condition * arm_reg * operand2
| CLZ of arm_reg * arm_reg
| RBIT of arm_reg * arm_reg
| POPCNT of arm_reg * arm_reg
| LDR of arm_reg * arm_reg * int
| STR of arm_reg * arm_reg * int
| UDF of int
| CMN of arm_reg * operand2
| B of int
| BL of int
| BX of arm_reg
| BCondOffset of condition * int
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
| I64MulPseudo of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg * arm_reg
| I64ShlPseudo of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg * arm_reg
| I64ShrUPseudo of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg * arm_reg
| I64ShrSPseudo of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg * arm_reg
| I64RotlPseudo of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg
| I64RotrPseudo of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg
| I64ClzPseudo of arm_reg * arm_reg * arm_reg
| I64CtzPseudo of arm_reg * arm_reg * arm_reg
| I64PopcntPseudo of arm_reg * arm_reg * arm_reg
| I64SetCond of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg * condition
| I64SetCondZ of arm_reg * arm_reg * arm_reg
| I64DivSPseudo of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg * arm_reg
| I64DivUPseudo of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg * arm_reg
| I64RemSPseudo of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg * arm_reg
| I64RemUPseudo of arm_reg * arm_reg * arm_reg * arm_reg * arm_reg * arm_reg
| I64ConstPseudo of arm_reg * arm_reg * I64.int
| I64ExtendI32SPseudo of arm_reg * arm_reg * arm_reg
| I64ExtendI32UPseudo of arm_reg * arm_reg * arm_reg
| I32WrapI64Pseudo of arm_reg * arm_reg
| I64LoadPseudo of arm_reg * arm_reg * arm_reg * int
| I64StorePseudo of arm_reg * arm_reg * arm_reg * int

type arm_program = arm_instr list

val eval_operand2 : operand2 -> arm_state -> I32.int

val eval_condition : condition -> condition_flags -> bool
