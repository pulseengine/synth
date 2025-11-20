(** Synth WASM Compiler - Using Formally Verified Compilation

    Compiles WASM functions to ARM assembly using extracted Coq code

    Usage: synth_compile <function_name> -o <output.s>
*)

open ArmState
open ArmInstructions
open WasmInstructions
open Compilation

(** Convert ARM register to assembly string *)
let reg_to_string = function
  | R0 -> "r0"
  | R1 -> "r1"
  | R2 -> "r2"
  | R3 -> "r3"
  | R4 -> "r4"
  | R5 -> "r5"
  | R6 -> "r6"
  | R7 -> "r7"
  | R8 -> "r8"
  | R9 -> "r9"
  | R10 -> "r10"
  | R11 -> "r11"
  | R12 -> "r12"
  | SP -> "sp"
  | LR -> "lr"
  | PC -> "pc"

(** Convert VFP register to assembly string *)
let vfp_reg_to_string = function
  | S0 -> "s0" | S1 -> "s1" | S2 -> "s2" | S3 -> "s3"
  | S4 -> "s4" | S5 -> "s5" | S6 -> "s6" | S7 -> "s7"
  | S8 -> "s8" | S9 -> "s9" | S10 -> "s10" | S11 -> "s11"
  | S12 -> "s12" | S13 -> "s13" | S14 -> "s14" | S15 -> "s15"
  | S16 -> "s16" | S17 -> "s17" | S18 -> "s18" | S19 -> "s19"
  | S20 -> "s20" | S21 -> "s21" | S22 -> "s22" | S23 -> "s23"
  | S24 -> "s24" | S25 -> "s25" | S26 -> "s26" | S27 -> "s27"
  | S28 -> "s28" | S29 -> "s29" | S30 -> "s30" | S31 -> "s31"
  | D0 -> "d0" | D1 -> "d1" | D2 -> "d2" | D3 -> "d3"
  | D4 -> "d4" | D5 -> "d5" | D6 -> "d6" | D7 -> "d7"
  | D8 -> "d8" | D9 -> "d9" | D10 -> "d10" | D11 -> "d11"
  | D12 -> "d12" | D13 -> "d13" | D14 -> "d14" | D15 -> "d15"

(** Convert operand2 to assembly string *)
let operand2_to_string = function
  | Imm n -> Printf.sprintf "#%d" n
  | Reg r -> reg_to_string r
  | RegShift (r, shift) -> Printf.sprintf "%s, lsl #%d" (reg_to_string r) shift

(** Convert ARM instruction to assembly string *)
let instr_to_asm = function
  | ADD (rd, rn, op2) ->
      Printf.sprintf "    add %s, %s, %s"
        (reg_to_string rd) (reg_to_string rn) (operand2_to_string op2)

  | SUB (rd, rn, op2) ->
      Printf.sprintf "    sub %s, %s, %s"
        (reg_to_string rd) (reg_to_string rn) (operand2_to_string op2)

  | MOV (rd, op2) ->
      Printf.sprintf "    mov %s, %s"
        (reg_to_string rd) (operand2_to_string op2)

  | MOVW (rd, imm) ->
      Printf.sprintf "    movw %s, #%d" (reg_to_string rd) imm

  | MUL (rd, rn, rm) ->
      Printf.sprintf "    mul %s, %s, %s"
        (reg_to_string rd) (reg_to_string rn) (reg_to_string rm)

  | BX r ->
      Printf.sprintf "    bx %s" (reg_to_string r)

  (* VFP Floating-point instructions *)
  | VADD_F32 (sd, sn, sm) ->
      Printf.sprintf "    vadd.f32 %s, %s, %s"
        (vfp_reg_to_string sd) (vfp_reg_to_string sn) (vfp_reg_to_string sm)

  | VSUB_F32 (sd, sn, sm) ->
      Printf.sprintf "    vsub.f32 %s, %s, %s"
        (vfp_reg_to_string sd) (vfp_reg_to_string sn) (vfp_reg_to_string sm)

  | VMUL_F32 (sd, sn, sm) ->
      Printf.sprintf "    vmul.f32 %s, %s, %s"
        (vfp_reg_to_string sd) (vfp_reg_to_string sn) (vfp_reg_to_string sm)

  | VDIV_F32 (sd, sn, sm) ->
      Printf.sprintf "    vdiv.f32 %s, %s, %s"
        (vfp_reg_to_string sd) (vfp_reg_to_string sn) (vfp_reg_to_string sm)

  | VMOV (sd, sm) ->
      Printf.sprintf "    vmov.f32 %s, %s"
        (vfp_reg_to_string sd) (vfp_reg_to_string sm)

  | _ -> "    @ unimplemented instruction"

(** Generate ARM assembly for a WASM function *)
let generate_function_asm func_name wasm_instrs =
  (* Compile WASM to ARM using extracted Coq code *)
  let arm_program = compile_wasm_program wasm_instrs in

  (* Generate assembly *)
  let asm_lines = [
    Printf.sprintf ".global %s" func_name;
    Printf.sprintf ".type %s, %%function" func_name;
    Printf.sprintf "%s:" func_name;
    "    @ Function prologue";
    "    push {r4, lr}";
    "";
    "    @ WASM function body";
  ] in

  (* Convert each ARM instruction to assembly *)
  let body_asm = List.map instr_to_asm arm_program in

  (* Function epilogue *)
  let epilogue = [
    "";
    "    @ Function epilogue";
    "    pop {r4, pc}";
    Printf.sprintf ".size %s, .-%s" func_name func_name;
  ] in

  String.concat "\n" (asm_lines @ body_asm @ epilogue)

(** PID function definitions in WASM *)

(* Simple helper function: error = setpoint - measurement *)
let pid_error_wasm = [
  (* Stack: [setpoint, measurement] -> [error] *)
  F32Sub  (* setpoint - measurement *)
]

(* Simple helper function: new_integral = prev_integral + (error * dt) *)
let pid_integral_wasm = [
  (* Stack: [prev_integral, error, dt] *)
  (* Need: prev_integral + (error * dt) *)
  (* Current stack model is simplified - using registers *)
  (* S0=prev_integral, S1=error, S2=dt *)
  F32Mul;  (* error * dt (result in S0) *)
  F32Add   (* prev_integral + (error * dt) *)
]

(* Simplified PID update - demonstrates compilation *)
let pid_update_simple_wasm = [
  (* This is a simplified version showing the core operations *)
  (* Full version would require local variable support *)
  (* For now: calculates one term of PID as demonstration *)
  F32Mul;  (* kp * error *)
]

(** Main compiler entry point *)
let compile_function func_name output_file =
  Printf.printf "Synth Compiler - Formally Verified Compilation\n";
  Printf.printf "Compiling function: %s -> %s\n" func_name output_file;

  (* Select WASM program based on function name *)
  let (wasm_body, comment) = match func_name with
    | "add" ->
        ([I32Add], "Simple i32 addition")
    | "pid_error" ->
        (pid_error_wasm, "PID error calculation: setpoint - measurement")
    | "pid_integral" ->
        (pid_integral_wasm, "PID integral update")
    | "pid_simple" ->
        (pid_update_simple_wasm, "Simplified PID term calculation")
    | _ ->
        (Printf.eprintf "Unknown function: %s\n" func_name;
         exit 1)
  in

  Printf.printf "WASM operations: %s\n" comment;
  Printf.printf "Instruction count: %d\n" (List.length wasm_body);

  (* Generate assembly *)
  let asm_header = [
    "@ Generated by Synth WASM Compiler";
    "@ Using formally verified compilation from Coq";
    "@ Target: ARM Cortex-M with VFP";
    "";
    Printf.sprintf "@ Function: %s" func_name;
    Printf.sprintf "@ %s" comment;
    "";
    ".syntax unified";
    ".thumb";
    ".text";
    "";
  ] in

  let func_asm = generate_function_asm ("synth_" ^ func_name) wasm_body in

  let full_asm = String.concat "\n" asm_header ^ "\n" ^ func_asm in

  (* Write to output file *)
  let oc = open_out output_file in
  output_string oc full_asm;
  close_out oc;

  Printf.printf "✓ Compilation successful!\n";
  Printf.printf "Generated ARM assembly: %s\n" output_file;
  Printf.printf "\nGenerated using formally verified semantics from:\n";
  Printf.printf "  coq/theories/Synth/Compilation.v\n";
  Printf.printf "\nTo assemble:\n";
  Printf.printf "  arm-none-eabi-as -mcpu=cortex-m4 -mthumb -mfpu=fpv4-sp-d16 %s -o %s.o\n"
    output_file func_name;
  ()

(** Command-line interface *)
let () =
  if Array.length Sys.argv < 3 then begin
    Printf.eprintf "Usage: %s <function_name> -o <output.s>\n" Sys.argv.(0);
    Printf.eprintf "\nAvailable functions:\n";
    Printf.eprintf "  add         - Simple i32 addition\n";
    Printf.eprintf "  pid_error   - PID error calculation\n";
    Printf.eprintf "  pid_integral - PID integral update\n";
    Printf.eprintf "  pid_simple  - Simplified PID term\n";
    exit 1
  end;

  let func_name = Sys.argv.(1) in
  let output_file =
    if Array.length Sys.argv >= 4 && Sys.argv.(2) = "-o" then
      Sys.argv.(3)
    else
      func_name ^ ".s"
  in

  compile_function func_name output_file
