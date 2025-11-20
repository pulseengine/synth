open ArmInstructions
open ArmState
open BinInt
open Integers

(** val compute_n_flag : int -> bool **)

let compute_n_flag result =
  Z.ltb (I32.signed result) 0

(** val compute_z_flag : int -> bool **)

let compute_z_flag result =
  I32.eq result I32.zero

(** val compute_c_flag_add : int -> int -> bool **)

let compute_c_flag_add x y =
  let ux = I32.unsigned x in
  let uy = I32.unsigned y in Z.ltb I32.max_unsigned (Z.add ux uy)

(** val compute_v_flag_add : int -> int -> int -> bool **)

let compute_v_flag_add x y result =
  let sx = I32.signed x in
  let sy = I32.signed y in
  let sr = I32.signed result in
  (||) ((&&) ((&&) (Z.leb 0 sx) (Z.leb 0 sy)) (Z.ltb sr 0))
    ((&&) ((&&) (Z.ltb sx 0) (Z.ltb sy 0)) (Z.leb 0 sr))

(** val update_flags_arith : int -> bool -> bool -> condition_flags **)

let update_flags_arith result c v =
  { flag_n = (compute_n_flag result); flag_z = (compute_z_flag result);
    flag_c = c; flag_v = v }

(** val exec_instr : arm_instr -> arm_state -> arm_state option **)

let exec_instr i s =
  match i with
  | ADD (rd, rn, op2) ->
    let v1 = get_reg s rn in
    let v2 = eval_operand2 op2 s in
    let result = I32.add v1 v2 in Some (set_reg s rd result)
  | SUB (rd, rn, op2) ->
    let v1 = get_reg s rn in
    let v2 = eval_operand2 op2 s in
    let result = I32.sub v1 v2 in Some (set_reg s rd result)
  | MUL (rd, rn, rm) ->
    let v1 = get_reg s rn in
    let v2 = get_reg s rm in
    let result = I32.mul v1 v2 in Some (set_reg s rd result)
  | SDIV (rd, rn, rm) ->
    let v1 = get_reg s rn in
    let v2 = get_reg s rm in
    (match I32.divs v1 v2 with
     | Some result -> Some (set_reg s rd result)
     | None -> None)
  | UDIV (rd, rn, rm) ->
    let v1 = get_reg s rn in
    let v2 = get_reg s rm in
    (match I32.divu v1 v2 with
     | Some result -> Some (set_reg s rd result)
     | None -> None)
  | MLS (rd, rn, rm, ra) ->
    let vn = get_reg s rn in
    let vm = get_reg s rm in
    let va = get_reg s ra in
    let product = I32.mul vn vm in
    let result = I32.sub va product in Some (set_reg s rd result)
  | AND (rd, rn, op2) ->
    let v1 = get_reg s rn in
    let v2 = eval_operand2 op2 s in
    let result = I32.coq_and v1 v2 in Some (set_reg s rd result)
  | ORR (rd, rn, op2) ->
    let v1 = get_reg s rn in
    let v2 = eval_operand2 op2 s in
    let result = I32.coq_or v1 v2 in Some (set_reg s rd result)
  | EOR (rd, rn, op2) ->
    let v1 = get_reg s rn in
    let v2 = eval_operand2 op2 s in
    let result = I32.xor v1 v2 in Some (set_reg s rd result)
  | MVN (rd, op2) ->
    let v = eval_operand2 op2 s in
    let result = I32.repr (Z.lnot (I32.unsigned v)) in
    Some (set_reg s rd result)
  | LSL (rd, rn, shift) ->
    let v = get_reg s rn in
    let shift_amt = I32.repr (Z.of_nat shift) in
    let result = I32.shl v shift_amt in Some (set_reg s rd result)
  | LSR (rd, rn, shift) ->
    let v = get_reg s rn in
    let shift_amt = I32.repr (Z.of_nat shift) in
    let result = I32.shru v shift_amt in Some (set_reg s rd result)
  | ASR (rd, rn, shift) ->
    let v = get_reg s rn in
    let shift_amt = I32.repr (Z.of_nat shift) in
    let result = I32.shrs v shift_amt in Some (set_reg s rd result)
  | ROR (rd, rn, shift) ->
    let v = get_reg s rn in
    let shift_amt = I32.repr (Z.of_nat shift) in
    let result = I32.rotr v shift_amt in Some (set_reg s rd result)
  | MOV (rd, op2) -> let v = eval_operand2 op2 s in Some (set_reg s rd v)
  | MOVW (rd, imm) -> Some (set_reg s rd imm)
  | MOVT (rd, imm) ->
    let current = get_reg s rd in
    let lower =
      I32.coq_and current
        (I32.repr ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
          1))))))))))))))))
    in
    let upper =
      I32.shl imm
        (I32.repr ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          1)))))
    in
    let result = I32.coq_or lower upper in Some (set_reg s rd result)
  | CMP (rn, op2) ->
    let v1 = get_reg s rn in
    let v2 = eval_operand2 op2 s in
    let result = I32.sub v1 v2 in
    let c = compute_c_flag_add v1 (I32.sub I32.zero v2) in
    let v = compute_v_flag_add v1 (I32.sub I32.zero v2) result in
    let new_flags = update_flags_arith result c v in
    Some (set_flags s new_flags)
  | CLZ (rd, _) -> Some (set_reg s rd I32.zero)
  | RBIT (rd, rm) -> let v = get_reg s rm in Some (set_reg s rd v)
  | POPCNT (rd, _) -> Some (set_reg s rd I32.zero)
  | LDR (rd, rn, offset) ->
    let base = get_reg s rn in
    let addr = I32.add base (I32.repr offset) in
    let value = load_mem s (I32.signed addr) in Some (set_reg s rd value)
  | STR (rd, rn, offset) ->
    let base = get_reg s rn in
    let addr = I32.add base (I32.repr offset) in
    let value = get_reg s rd in Some (store_mem s (I32.signed addr) value)
  | B offset ->
    let current_pc = get_reg s PC in
    let new_pc = I32.add current_pc (I32.repr offset) in
    Some (set_reg s PC new_pc)
  | BL offset ->
    let current_pc = get_reg s PC in
    let return_addr =
      I32.add current_pc (I32.repr ((fun p->2*p) ((fun p->2*p) 1)))
    in
    let s' = set_reg s LR return_addr in
    let new_pc = I32.add current_pc (I32.repr offset) in
    Some (set_reg s' PC new_pc)
  | BX rm -> let target = get_reg s rm in Some (set_reg s PC target)
  | _ -> Some s

(** val exec_program : arm_instr list -> arm_state -> arm_state option **)

let rec exec_program prog s =
  match prog with
  | [] -> Some s
  | i::rest ->
    (match exec_instr i s with
     | Some s' -> exec_program rest s'
     | None -> None)
