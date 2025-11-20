open Integers

type wasm_val =
| VI32 of I32.int
| VI64 of I64.int
| VF32 of I32.int
| VF64 of I64.int

type wasm_stack = wasm_val list

val push : wasm_val -> wasm_stack -> wasm_stack

val pop : wasm_stack -> (wasm_val*wasm_stack) option

val pop2 : wasm_stack -> ((wasm_val*wasm_val)*wasm_stack) option
