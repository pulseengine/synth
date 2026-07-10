open ArmInstructions
open ArmState
open BinInt
open Integers
open List0
open WasmInstructions

(** val compile_wasm_to_arm : wasm_instr -> arm_program **)

let compile_wasm_to_arm = function
| I32Const n ->
  if Z.leb (I32.unsigned n) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
       1)))))))))))))))
  then (MOVW (R0, n))::[]
  else (MOVW (R0,
         (I32.repr
           (Z.coq_land (I32.unsigned n) ((fun p->1+2*p) ((fun p->1+2*p)
             ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
             ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
             ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
             ((fun p->1+2*p) 1)))))))))))))))))))::((MOVT
         (R0,
         (I32.repr
           (Z.shiftr (I32.unsigned n) ((fun p->2*p) ((fun p->2*p)
             ((fun p->2*p) ((fun p->2*p) 1))))))))::[])
| I64Const n -> (I64ConstPseudo (R0, R1, n))::[]
| I32Add -> (ADD (R0, R0, (Reg R1)))::[]
| I32Sub -> (SUB (R0, R0, (Reg R1)))::[]
| I32Mul -> (MUL (R0, R0, R1))::[]
| I32DivS ->
  (CMP (R1, (Imm I32.zero)))::((BCondOffset (Cond_NE, 1))::((UDF 0)::((MOVW
    (R2, (I32.repr 0)))::((MOVT (R2,
    (I32.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) 1))))))))))))))))))::((CMP
    (R0, (Reg R2)))::((BCondOffset (Cond_NE, ((fun p->2*p) 1)))::((CMN (R1,
    (Imm I32.one)))::((BCondOffset (Cond_NE, 0))::((UDF 1)::((SDIV (R0, R0,
    R1))::[]))))))))))
| I32DivU ->
  (CMP (R1, (Imm I32.zero)))::((BCondOffset (Cond_NE, 1))::((UDF 0)::((UDIV
    (R0, R0, R1))::[])))
| I32RemS ->
  (CMP (R1, (Imm I32.zero)))::((BCondOffset (Cond_NE, 1))::((UDF 0)::((SDIV
    (R2, R0, R1))::((MLS (R0, R2, R1, R0))::[]))))
| I32RemU ->
  (CMP (R1, (Imm I32.zero)))::((BCondOffset (Cond_NE, 1))::((UDF 0)::((UDIV
    (R2, R0, R1))::((MLS (R0, R2, R1, R0))::[]))))
| I32And -> (AND (R0, R0, (Reg R1)))::[]
| I32Or -> (ORR (R0, R0, (Reg R1)))::[]
| I32Xor -> (EOR (R0, R0, (Reg R1)))::[]
| I32Shl -> (LSL_reg (R0, R0, R1))::[]
| I32ShrS -> (ASR_reg (R0, R0, R1))::[]
| I32ShrU -> (LSR_reg (R0, R0, R1))::[]
| I32Rotl ->
  (RSB (R2, R1, (Imm
    (I32.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) 1)))))))))::((ROR_reg
    (R0, R0, R2))::[])
| I32Rotr -> (ROR_reg (R0, R0, R1))::[]
| I32Eqz ->
  (CMP (R0, (Imm I32.zero)))::((MOV (R0, (Imm I32.zero)))::((MOVEQ (R0, (Imm
    I32.one)))::[]))
| I32Eq ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVEQ (R0, (Imm
    I32.one)))::[]))
| I32Ne ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVNE (R0, (Imm
    I32.one)))::[]))
| I32LtS ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVLT (R0, (Imm
    I32.one)))::[]))
| I32LtU ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVLO (R0, (Imm
    I32.one)))::[]))
| I32GtS ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVGT (R0, (Imm
    I32.one)))::[]))
| I32GtU ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVHI (R0, (Imm
    I32.one)))::[]))
| I32LeS ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVLE (R0, (Imm
    I32.one)))::[]))
| I32LeU ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVLS (R0, (Imm
    I32.one)))::[]))
| I32GeS ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVGE (R0, (Imm
    I32.one)))::[]))
| I32GeU ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVHS (R0, (Imm
    I32.one)))::[]))
| I32Clz -> (CLZ (R0, R0))::[]
| I32Ctz -> (RBIT (R0, R0))::((CLZ (R0, R0))::[])
| I32Popcnt -> (POPCNT (R0, R0))::[]
| I64Add -> (ADDS (R0, R0, (Reg R2)))::((ADC (R1, R1, (Reg R3)))::[])
| I64Sub -> (SUBS (R0, R0, (Reg R2)))::((SBC (R1, R1, (Reg R3)))::[])
| I64Mul -> (I64MulPseudo (R0, R1, R0, R1, R2, R3))::[]
| I64DivS -> (I64DivSPseudo (R0, R1, R0, R1, R2, R3))::[]
| I64DivU -> (I64DivUPseudo (R0, R1, R0, R1, R2, R3))::[]
| I64RemS -> (I64RemSPseudo (R0, R1, R0, R1, R2, R3))::[]
| I64RemU -> (I64RemUPseudo (R0, R1, R0, R1, R2, R3))::[]
| I64And -> (AND (R0, R0, (Reg R2)))::((AND (R1, R1, (Reg R3)))::[])
| I64Or -> (ORR (R0, R0, (Reg R2)))::((ORR (R1, R1, (Reg R3)))::[])
| I64Xor -> (EOR (R0, R0, (Reg R2)))::((EOR (R1, R1, (Reg R3)))::[])
| I64Shl -> (I64ShlPseudo (R0, R1, R0, R1, R2, R3))::[]
| I64ShrS -> (I64ShrSPseudo (R0, R1, R0, R1, R2, R3))::[]
| I64ShrU -> (I64ShrUPseudo (R0, R1, R0, R1, R2, R3))::[]
| I64Rotl -> (I64RotlPseudo (R0, R1, R0, R1, R2))::[]
| I64Rotr -> (I64RotrPseudo (R0, R1, R0, R1, R2))::[]
| I64Eqz -> (I64SetCondZ (R0, R0, R1))::[]
| I64Eq -> (I64SetCond (R0, R0, R1, R2, R3, Cond_EQ))::[]
| I64Ne -> (I64SetCond (R0, R0, R1, R2, R3, Cond_NE))::[]
| I64LtS -> (I64SetCond (R0, R0, R1, R2, R3, Cond_LT))::[]
| I64LtU -> (I64SetCond (R0, R0, R1, R2, R3, Cond_CC))::[]
| I64GtS -> (I64SetCond (R0, R0, R1, R2, R3, Cond_GT))::[]
| I64GtU -> (I64SetCond (R0, R0, R1, R2, R3, Cond_HI))::[]
| I64LeS -> (I64SetCond (R0, R0, R1, R2, R3, Cond_LE))::[]
| I64LeU -> (I64SetCond (R0, R0, R1, R2, R3, Cond_LS))::[]
| I64GeS -> (I64SetCond (R0, R0, R1, R2, R3, Cond_GE))::[]
| I64GeU -> (I64SetCond (R0, R0, R1, R2, R3, Cond_CS))::[]
| I64Clz -> (I64ClzPseudo (R0, R0, R1))::[]
| I64Ctz -> (I64CtzPseudo (R0, R0, R1))::[]
| I64Popcnt -> (I64PopcntPseudo (R0, R0, R1))::[]
| F32Add -> (VADD_F32 (S0, S0, S1))::[]
| F32Sub -> (VSUB_F32 (S0, S0, S1))::[]
| F32Mul -> (VMUL_F32 (S0, S0, S1))::[]
| F32Div -> (VDIV_F32 (S0, S0, S1))::[]
| F32Sqrt -> (VSQRT_F32 (S0, S0))::[]
| F32Abs -> (VABS_F32 (S0, S0))::[]
| F32Neg -> (VNEG_F32 (S0, S0))::[]
| F32Eq -> (VCMP_F32 (S0, S1))::[]
| F32Ne -> (VCMP_F32 (S0, S1))::[]
| F32Lt -> (VCMP_F32 (S0, S1))::[]
| F32Gt -> (VCMP_F32 (S0, S1))::[]
| F32Le -> (VCMP_F32 (S0, S1))::[]
| F32Ge -> (VCMP_F32 (S0, S1))::[]
| F64Add -> (VADD_F64 (D0, D0, D1))::[]
| F64Sub -> (VSUB_F64 (D0, D0, D1))::[]
| F64Mul -> (VMUL_F64 (D0, D0, D1))::[]
| F64Div -> (VDIV_F64 (D0, D0, D1))::[]
| F64Sqrt -> (VSQRT_F64 (D0, D0))::[]
| F64Abs -> (VABS_F64 (D0, D0))::[]
| F64Neg -> (VNEG_F64 (D0, D0))::[]
| F64Eq -> (VCMP_F64 (D0, D1))::[]
| F64Ne -> (VCMP_F64 (D0, D1))::[]
| F64Lt -> (VCMP_F64 (D0, D1))::[]
| F64Gt -> (VCMP_F64 (D0, D1))::[]
| F64Le -> (VCMP_F64 (D0, D1))::[]
| F64Ge -> (VCMP_F64 (D0, D1))::[]
| I32WrapI64 -> (I32WrapI64Pseudo (R0, R0))::[]
| I64ExtendI32S -> (I64ExtendI32SPseudo (R0, R1, R0))::[]
| I64ExtendI32U -> (I64ExtendI32UPseudo (R0, R1, R0))::[]
| I32TruncF32S -> (VCVT_S32_F32 (S0, S0))::((VMOV_VFP_TO_ARM (R0, S0))::[])
| I32TruncF32U -> (VCVT_S32_F32 (S0, S0))::((VMOV_VFP_TO_ARM (R0, S0))::[])
| I32TruncF64S ->
  (VCVT_F32_F64 (S0, D0))::((VCVT_S32_F32 (S0, S0))::((VMOV_VFP_TO_ARM (R0,
    S0))::[]))
| I32TruncF64U ->
  (VCVT_F32_F64 (S0, D0))::((VCVT_S32_F32 (S0, S0))::((VMOV_VFP_TO_ARM (R0,
    S0))::[]))
| I64TruncF32S -> (VCVT_S32_F32 (S0, S0))::((VMOV_VFP_TO_ARM (R0, S0))::[])
| I64TruncF32U -> (VCVT_S32_F32 (S0, S0))::((VMOV_VFP_TO_ARM (R0, S0))::[])
| I64TruncF64S -> (VCVT_S32_F32 (S0, S0))::((VMOV_VFP_TO_ARM (R0, S0))::[])
| I64TruncF64U -> (VCVT_S32_F32 (S0, S0))::((VMOV_VFP_TO_ARM (R0, S0))::[])
| F32ConvertI32S -> (VMOV_ARM_TO_VFP (S0, R0))::((VCVT_F32_S32 (S0, S0))::[])
| F32ConvertI32U -> (VMOV_ARM_TO_VFP (S0, R0))::((VCVT_F32_S32 (S0, S0))::[])
| F32ConvertI64S -> (VMOV_ARM_TO_VFP (S0, R0))::((VCVT_F32_S32 (S0, S0))::[])
| F32ConvertI64U -> (VMOV_ARM_TO_VFP (S0, R0))::((VCVT_F32_S32 (S0, S0))::[])
| F32DemoteF64 -> (VCVT_F32_F64 (S0, D0))::[]
| F64ConvertI32S ->
  (VMOV_ARM_TO_VFP (S0, R0))::((VCVT_F32_S32 (S0, S0))::((VCVT_F64_F32 (D0,
    S0))::[]))
| F64ConvertI32U ->
  (VMOV_ARM_TO_VFP (S0, R0))::((VCVT_F32_S32 (S0, S0))::((VCVT_F64_F32 (D0,
    S0))::[]))
| F64ConvertI64S ->
  (VMOV_ARM_TO_VFP (S0, R0))::((VCVT_F32_S32 (S0, S0))::((VCVT_F64_F32 (D0,
    S0))::[]))
| F64ConvertI64U ->
  (VMOV_ARM_TO_VFP (S0, R0))::((VCVT_F32_S32 (S0, S0))::((VCVT_F64_F32 (D0,
    S0))::[]))
| F64PromoteF32 -> (VCVT_F64_F32 (D0, S0))::[]
| I32Load offset -> (LDR (R0, R0, (Z.of_nat offset)))::[]
| I64Load offset -> (I64LoadPseudo (R0, R1, R0, (Z.of_nat offset)))::[]
| F32Load offset -> (VLDR_F32 (S0, R0, (Z.of_nat offset)))::[]
| F64Load offset -> (VLDR_F64 (D0, R0, (Z.of_nat offset)))::[]
| I32Store offset -> (STR (R1, R0, (Z.of_nat offset)))::[]
| I64Store offset -> (I64StorePseudo (R0, R1, R2, (Z.of_nat offset)))::[]
| F32Store offset -> (VSTR_F32 (S1, R0, (Z.of_nat offset)))::[]
| F64Store offset -> (VSTR_F64 (D1, R0, (Z.of_nat offset)))::[]
| LocalGet idx ->
  let local_reg =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> R4)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> R5)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> R6)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> R7)
            (fun _ -> R4)
            n1)
          n0)
        n)
      idx
  in
  (MOV (R0, (Reg local_reg)))::[]
| LocalSet idx ->
  let local_reg =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> R4)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> R5)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> R6)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> R7)
            (fun _ -> R4)
            n1)
          n0)
        n)
      idx
  in
  (MOV (local_reg, (Reg R0)))::[]
| LocalTee idx ->
  let local_reg =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> R4)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> R5)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> R6)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> R7)
            (fun _ -> R4)
            n1)
          n0)
        n)
      idx
  in
  (MOV (local_reg, (Reg R0)))::[]
| GlobalGet idx ->
  let global_reg =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> R8)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> R9)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> R10)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> R11)
            (fun _ -> R8)
            n1)
          n0)
        n)
      idx
  in
  (MOV (R0, (Reg global_reg)))::[]
| GlobalSet idx ->
  let global_reg =
    (fun fO fS n -> if n=0 then fO () else fS (n-1))
      (fun _ -> R8)
      (fun n ->
      (fun fO fS n -> if n=0 then fO () else fS (n-1))
        (fun _ -> R9)
        (fun n0 ->
        (fun fO fS n -> if n=0 then fO () else fS (n-1))
          (fun _ -> R10)
          (fun n1 ->
          (fun fO fS n -> if n=0 then fO () else fS (n-1))
            (fun _ -> R11)
            (fun _ -> R8)
            n1)
          n0)
        n)
      idx
  in
  (MOV (global_reg, (Reg R0)))::[]
| Select ->
  (CMP (R2, (Imm I32.zero)))::((MOVNE (R0, (Reg R0)))::((MOVEQ (R0, (Reg
    R1)))::[]))
| _ -> []

(** val compile_wasm_program : wasm_program -> arm_program **)

let compile_wasm_program prog =
  flat_map compile_wasm_to_arm prog
