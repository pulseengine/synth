open Integers

type wasm_val =
| VI32 of int
| VI64 of int
| VF32 of int
| VF64 of int

type wasm_stack = wasm_val list

(** val push : wasm_val -> wasm_stack -> wasm_stack **)

let push v stack =
  v::stack

(** val pop : wasm_stack -> (wasm_val*wasm_stack) option **)

let pop = function
| [] -> None
| v::rest -> Some (v,rest)

(** val pop2 : wasm_stack -> ((wasm_val*wasm_val)*wasm_stack) option **)

let pop2 = function
| [] -> None
| v2::l -> (match l with
            | [] -> None
            | v1::rest -> Some ((v1,v2),rest))
