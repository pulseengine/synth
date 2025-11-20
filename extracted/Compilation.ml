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
| I32Eqz ->
  (CMP (R0, (Imm I32.zero)))::((MOV (R0, (Imm I32.zero)))::((MOVEQ (R0, (Imm
    I32.one)))::[]))
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
| _ -> []

(** val compile_wasm_program : wasm_program -> arm_program **)

let compile_wasm_program prog =
  flat_map compile_wasm_to_arm prog
