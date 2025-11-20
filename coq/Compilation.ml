open ArmInstructions
open ArmState
open BinInt
open Integers
open List0
open WasmInstructions

(** val compile_wasm_to_arm : wasm_instr -> arm_program **)

let compile_wasm_to_arm = function
| I32Const n -> (MOVW (R0, n))::[]
| I64Const n ->
  (MOVW (R0, (I32.repr (Z.modulo (I64.unsigned n) I32.modulus))))::[]
| I32Add -> (ADD (R0, R0, (Reg R1)))::[]
| I32Sub -> (SUB (R0, R0, (Reg R1)))::[]
| I32Mul -> (MUL (R0, R0, R1))::[]
| I32DivS -> (SDIV (R0, R0, R1))::[]
| I32DivU -> (UDIV (R0, R0, R1))::[]
| I32RemS -> (SDIV (R2, R0, R1))::((MLS (R0, R2, R1, R0))::[])
| I32RemU -> (UDIV (R2, R0, R1))::((MLS (R0, R2, R1, R0))::[])
| I32And -> (AND (R0, R0, (Reg R1)))::[]
| I32Or -> (ORR (R0, R0, (Reg R1)))::[]
| I32Xor -> (EOR (R0, R0, (Reg R1)))::[]
| I32Shl -> (LSL (R0, R0, 0))::[]
| I32ShrS -> (ASR (R0, R0, 0))::[]
| I32ShrU -> (LSR (R0, R0, 0))::[]
| I32Rotr -> (ROR (R0, R0, 0))::[]
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
| I64Add -> (ADD (R0, R0, (Reg R1)))::[]
| I64Sub -> (SUB (R0, R0, (Reg R1)))::[]
| I64Mul -> (MUL (R0, R0, R1))::[]
| I64DivS -> (SDIV (R0, R0, R1))::[]
| I64DivU -> (UDIV (R0, R0, R1))::[]
| I64RemS -> (SDIV (R2, R0, R1))::((MLS (R0, R2, R1, R0))::[])
| I64RemU -> (UDIV (R2, R0, R1))::((MLS (R0, R2, R1, R0))::[])
| I64And -> (AND (R0, R0, (Reg R1)))::[]
| I64Or -> (ORR (R0, R0, (Reg R1)))::[]
| I64Xor -> (EOR (R0, R0, (Reg R1)))::[]
| I64Shl -> (LSL (R0, R0, 0))::[]
| I64ShrS -> (ASR (R0, R0, 0))::[]
| I64ShrU -> (LSR (R0, R0, 0))::[]
| I64Rotr -> (ROR (R0, R0, 0))::[]
| I64Eqz ->
  (CMP (R0, (Imm I32.zero)))::((MOV (R0, (Imm I32.zero)))::((MOVEQ (R0, (Imm
    I32.one)))::[]))
| I64Eq ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVEQ (R0, (Imm
    I32.one)))::[]))
| I64Ne ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVNE (R0, (Imm
    I32.one)))::[]))
| I64LtS ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVLT (R0, (Imm
    I32.one)))::[]))
| I64LtU ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVLO (R0, (Imm
    I32.one)))::[]))
| I64GtS ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVGT (R0, (Imm
    I32.one)))::[]))
| I64GtU ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVHI (R0, (Imm
    I32.one)))::[]))
| I64LeS ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVLE (R0, (Imm
    I32.one)))::[]))
| I64LeU ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVLS (R0, (Imm
    I32.one)))::[]))
| I64GeS ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVGE (R0, (Imm
    I32.one)))::[]))
| I64GeU ->
  (CMP (R0, (Reg R1)))::((MOV (R0, (Imm I32.zero)))::((MOVHS (R0, (Imm
    I32.one)))::[]))
| I64Clz -> (CLZ (R0, R0))::[]
| I64Ctz -> (RBIT (R0, R0))::((CLZ (R0, R0))::[])
| I64Popcnt -> (POPCNT (R0, R0))::[]
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
| I64Load offset -> (LDR (R0, R0, (Z.of_nat offset)))::[]
| F32Load offset -> (VLDR_F32 (S0, R0, (Z.of_nat offset)))::[]
| F64Load offset -> (VLDR_F64 (D0, R0, (Z.of_nat offset)))::[]
| I32Store offset -> (STR (R1, R0, (Z.of_nat offset)))::[]
| I64Store offset -> (STR (R1, R0, (Z.of_nat offset)))::[]
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
