open Base
open Integers
open WasmInstructions
open WasmValues

type wasm_state = { stack : wasm_stack; locals : (int -> I32.int);
                    globals : (int -> I32.int); memory : (int -> I32.int) }

val push_value : wasm_val -> wasm_state -> wasm_state

val pop_value : wasm_state -> (wasm_val*wasm_state) option

val pop_i32 : wasm_state -> (I32.int*wasm_state) option

val pop_i64 : wasm_state -> (I64.int*wasm_state) option

val pop2_i32 : wasm_state -> ((I32.int*I32.int)*wasm_state) option

val pop2_i64 : wasm_state -> ((I64.int*I64.int)*wasm_state) option

val exec_wasm_instr : wasm_instr -> wasm_state -> wasm_state option

val exec_wasm_program : wasm_instr list -> wasm_state -> wasm_state option
