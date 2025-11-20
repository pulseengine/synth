open Base
open Integers

type arm_reg =
| R0
| R1
| R2
| R3
| R4
| R5
| R6
| R7
| R8
| R9
| R10
| R11
| R12
| SP
| LR
| PC

(** val arm_reg_eq_dec : arm_reg -> arm_reg -> bool **)

let arm_reg_eq_dec r1 r2 =
  match r1 with
  | R0 -> (match r2 with
           | R0 -> true
           | _ -> false)
  | R1 -> (match r2 with
           | R1 -> true
           | _ -> false)
  | R2 -> (match r2 with
           | R2 -> true
           | _ -> false)
  | R3 -> (match r2 with
           | R3 -> true
           | _ -> false)
  | R4 -> (match r2 with
           | R4 -> true
           | _ -> false)
  | R5 -> (match r2 with
           | R5 -> true
           | _ -> false)
  | R6 -> (match r2 with
           | R6 -> true
           | _ -> false)
  | R7 -> (match r2 with
           | R7 -> true
           | _ -> false)
  | R8 -> (match r2 with
           | R8 -> true
           | _ -> false)
  | R9 -> (match r2 with
           | R9 -> true
           | _ -> false)
  | R10 -> (match r2 with
            | R10 -> true
            | _ -> false)
  | R11 -> (match r2 with
            | R11 -> true
            | _ -> false)
  | R12 -> (match r2 with
            | R12 -> true
            | _ -> false)
  | SP -> (match r2 with
           | SP -> true
           | _ -> false)
  | LR -> (match r2 with
           | LR -> true
           | _ -> false)
  | PC -> (match r2 with
           | PC -> true
           | _ -> false)

(** val arm_reg_EqDec : arm_reg coq_EqDec **)

let arm_reg_EqDec =
  arm_reg_eq_dec

type vfp_reg =
| S0
| S1
| S2
| S3
| S4
| S5
| S6
| S7
| S8
| S9
| S10
| S11
| S12
| S13
| S14
| S15
| S16
| S17
| S18
| S19
| S20
| S21
| S22
| S23
| S24
| S25
| S26
| S27
| S28
| S29
| S30
| S31
| D0
| D1
| D2
| D3
| D4
| D5
| D6
| D7
| D8
| D9
| D10
| D11
| D12
| D13
| D14
| D15

type condition_flags = { flag_n : bool; flag_z : bool; flag_c : bool;
                         flag_v : bool }

type regfile = arm_reg -> I32.int

type vfp_regfile = vfp_reg -> I32.int

type memory = int -> I32.int

type arm_state = { regs : regfile; flags : condition_flags;
                   vfp_regs : vfp_regfile; mem : memory;
                   locals : (int -> I32.int); globals : (int -> I32.int) }

(** val get_reg : arm_state -> arm_reg -> I32.int **)

let get_reg s r =
  s.regs r

(** val set_reg : arm_state -> arm_reg -> I32.int -> arm_state **)

let set_reg s r v =
  { regs = (update arm_reg_EqDec s.regs r v); flags = s.flags; vfp_regs =
    s.vfp_regs; mem = s.mem; locals = s.locals; globals = s.globals }

(** val set_flags : arm_state -> condition_flags -> arm_state **)

let set_flags s f =
  { regs = s.regs; flags = f; vfp_regs = s.vfp_regs; mem = s.mem; locals =
    s.locals; globals = s.globals }

(** val load_mem : arm_state -> int -> I32.int **)

let load_mem s addr =
  s.mem addr

(** val store_mem : arm_state -> int -> I32.int -> arm_state **)

let store_mem s addr v =
  { regs = s.regs; flags = s.flags; vfp_regs = s.vfp_regs; mem =
    (update coq_Z_eq_dec s.mem addr v); locals = s.locals; globals =
    s.globals }

(** val get_local : arm_state -> int -> I32.int **)

let get_local s idx =
  s.locals idx

(** val set_local : arm_state -> int -> I32.int -> arm_state **)

let set_local s idx v =
  { regs = s.regs; flags = s.flags; vfp_regs = s.vfp_regs; mem = s.mem;
    locals = (update nat_eq_dec s.locals idx v); globals = s.globals }
