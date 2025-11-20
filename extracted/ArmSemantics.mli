open ArmInstructions
open ArmState
open BinInt
open Integers

val compute_n_flag : int -> bool

val compute_z_flag : int -> bool

val compute_c_flag_add : int -> int -> bool

val compute_v_flag_add : int -> int -> int -> bool

val update_flags_arith : int -> bool -> bool -> condition_flags

val exec_instr : arm_instr -> arm_state -> arm_state option

val exec_program : arm_instr list -> arm_state -> arm_state option
