open Base
open Integers
open WasmInstructions
open WasmValues

type wasm_state = { stack : wasm_stack; locals : (int -> int);
                    globals : (int -> int); memory : (int -> int) }

(** val push_value : wasm_val -> wasm_state -> wasm_state **)

let push_value v s =
  { stack = (push v s.stack); locals = s.locals; globals = s.globals;
    memory = s.memory }

(** val pop_value : wasm_state -> (wasm_val*wasm_state) option **)

let pop_value s =
  match pop s.stack with
  | Some p ->
    let v,stack' = p in
    Some (v,{ stack = stack'; locals = s.locals; globals = s.globals;
    memory = s.memory })
  | None -> None

(** val pop_i32 : wasm_state -> (int*wasm_state) option **)

let pop_i32 s =
  match pop_value s with
  | Some p -> let w,s' = p in (match w with
                               | VI32 n -> Some (n,s')
                               | _ -> None)
  | None -> None

(** val pop_i64 : wasm_state -> (int*wasm_state) option **)

let pop_i64 s =
  match pop_value s with
  | Some p -> let w,s' = p in (match w with
                               | VI64 n -> Some (n,s')
                               | _ -> None)
  | None -> None

(** val pop2_i32 : wasm_state -> ((int*int)*wasm_state) option **)

let pop2_i32 s =
  match pop2 s.stack with
  | Some p ->
    let p0,stack' = p in
    let w,w0 = p0 in
    (match w with
     | VI32 v1 ->
       (match w0 with
        | VI32 v2 ->
          Some ((v1,v2),{ stack = stack'; locals = s.locals; globals =
            s.globals; memory = s.memory })
        | _ -> None)
     | _ -> None)
  | None -> None

(** val pop2_i64 : wasm_state -> ((int*int)*wasm_state) option **)

let pop2_i64 s =
  match pop2 s.stack with
  | Some p ->
    let p0,stack' = p in
    let w,w0 = p0 in
    (match w with
     | VI64 v1 ->
       (match w0 with
        | VI64 v2 ->
          Some ((v1,v2),{ stack = stack'; locals = s.locals; globals =
            s.globals; memory = s.memory })
        | _ -> None)
     | _ -> None)
  | None -> None

(** val exec_wasm_instr : wasm_instr -> wasm_state -> wasm_state option **)

let exec_wasm_instr i s =
  match i with
  | I32Const n -> Some (push_value (VI32 n) s)
  | I64Const n -> Some (push_value (VI64 n) s)
  | I32Add ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.add v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32Sub ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.sub v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32Mul ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.mul v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32DivS ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       (match I32.divs v1 v2 with
        | Some result -> Some (push_value (VI32 result) s')
        | None -> None)
     | None -> None)
  | I32DivU ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       (match I32.divu v1 v2 with
        | Some result -> Some (push_value (VI32 result) s')
        | None -> None)
     | None -> None)
  | I32RemS ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       (match I32.rems v1 v2 with
        | Some result -> Some (push_value (VI32 result) s')
        | None -> None)
     | None -> None)
  | I32RemU ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       (match I32.remu v1 v2 with
        | Some result -> Some (push_value (VI32 result) s')
        | None -> None)
     | None -> None)
  | I32And ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.coq_and v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32Or ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.coq_or v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32Xor ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.xor v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32Shl ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.shl v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32ShrS ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.shrs v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32ShrU ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.shru v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32Rotl ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.rotl v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32Rotr ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I32.rotr v1 v2 in Some (push_value (VI32 result) s')
     | None -> None)
  | I32Eqz ->
    (match pop_i32 s with
     | Some p ->
       let v,s' = p in
       let result = if I32.eq v I32.zero then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32Eq ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I32.eq v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32Ne ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I32.ne v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32LtS ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I32.lts v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32LtU ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I32.ltu v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32GtS ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I32.gts v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32GtU ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I32.gtu v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32LeS ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I32.les v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32LeU ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I32.leu v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32GeS ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I32.ges v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32GeU ->
    (match pop2_i32 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I32.geu v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I32Clz ->
    (match pop_i32 s with
     | Some p ->
       let v,s' = p in
       let result = I32.clz v in Some (push_value (VI32 result) s')
     | None -> None)
  | I32Ctz ->
    (match pop_i32 s with
     | Some p ->
       let v,s' = p in
       let result = I32.ctz v in Some (push_value (VI32 result) s')
     | None -> None)
  | I32Popcnt ->
    (match pop_i32 s with
     | Some p ->
       let v,s' = p in
       let result = I32.popcnt v in Some (push_value (VI32 result) s')
     | None -> None)
  | I64Shl ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I64.shl v1 v2 in Some (push_value (VI64 result) s')
     | None -> None)
  | I64ShrS ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I64.shrs v1 v2 in Some (push_value (VI64 result) s')
     | None -> None)
  | I64ShrU ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I64.shru v1 v2 in Some (push_value (VI64 result) s')
     | None -> None)
  | I64Rotl ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I64.rotl v1 v2 in Some (push_value (VI64 result) s')
     | None -> None)
  | I64Rotr ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = I64.rotr v1 v2 in Some (push_value (VI64 result) s')
     | None -> None)
  | I64Eqz ->
    (match pop_i64 s with
     | Some p ->
       let v,s' = p in
       let result = if I64.eq v I64.zero then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64Eq ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I64.eq v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64Ne ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I64.ne v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64LtS ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I64.lts v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64LtU ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I64.ltu v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64GtS ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I64.gts v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64GtU ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I64.gtu v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64LeS ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I64.les v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64LeU ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I64.leu v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64GeS ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I64.ges v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64GeU ->
    (match pop2_i64 s with
     | Some p ->
       let p0,s' = p in
       let v1,v2 = p0 in
       let result = if I64.geu v1 v2 then I32.one else I32.zero in
       Some (push_value (VI32 result) s')
     | None -> None)
  | I64Clz ->
    (match pop_i64 s with
     | Some p ->
       let v,s' = p in
       let result = I64.clz v in Some (push_value (VI64 result) s')
     | None -> None)
  | I64Ctz ->
    (match pop_i64 s with
     | Some p ->
       let v,s' = p in
       let result = I64.ctz v in Some (push_value (VI64 result) s')
     | None -> None)
  | I64Popcnt ->
    (match pop_i64 s with
     | Some p ->
       let v,s' = p in
       let result = I64.popcnt v in Some (push_value (VI64 result) s')
     | None -> None)
  | LocalGet idx ->
    let value = s.locals idx in Some (push_value (VI32 value) s)
  | LocalSet idx ->
    (match pop_i32 s with
     | Some p ->
       let value,s' = p in
       Some { stack = s'.stack; locals =
       (update nat_eq_dec s'.locals idx value); globals = s'.globals;
       memory = s'.memory }
     | None -> None)
  | LocalTee idx ->
    (match pop_i32 s with
     | Some p ->
       let value,s' = p in
       let s'' = { stack = s'.stack; locals =
         (update nat_eq_dec s'.locals idx value); globals = s'.globals;
         memory = s'.memory }
       in
       Some (push_value (VI32 value) s'')
     | None -> None)
  | GlobalGet idx ->
    let value = s.globals idx in Some (push_value (VI32 value) s)
  | GlobalSet idx ->
    (match pop_i32 s with
     | Some p ->
       let value,s' = p in
       Some { stack = s'.stack; locals = s'.locals; globals =
       (update nat_eq_dec s'.globals idx value); memory = s'.memory }
     | None -> None)
  | Drop ->
    (match pop_value s with
     | Some p -> let _,s' = p in Some s'
     | None -> None)
  | Select ->
    (match pop_i32 s with
     | Some p ->
       let cond,s' = p in
       (match pop_value s' with
        | Some p0 ->
          let val2,s'' = p0 in
          (match pop_value s'' with
           | Some p1 ->
             let val1,s''' = p1 in
             if I32.eq cond I32.zero
             then Some (push_value val2 s''')
             else Some (push_value val1 s''')
           | None -> None)
        | None -> None)
     | None -> None)
  | _ -> Some s

(** val exec_wasm_program :
    wasm_instr list -> wasm_state -> wasm_state option **)

let rec exec_wasm_program prog s =
  match prog with
  | [] -> Some s
  | i::rest ->
    (match exec_wasm_instr i s with
     | Some s' -> exec_wasm_program rest s'
     | None -> None)
