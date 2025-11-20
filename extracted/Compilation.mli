open ArmInstructions
open ArmState
open BinInt
open Integers
open List0
open WasmInstructions

val compile_wasm_to_arm : wasm_instr -> arm_program

val compile_wasm_program : wasm_program -> arm_program
