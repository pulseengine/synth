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

val arm_reg_eq_dec : arm_reg -> arm_reg -> bool

val arm_reg_EqDec : arm_reg coq_EqDec

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

type regfile = arm_reg -> int

type vfp_regfile = vfp_reg -> int

type memory = int -> int

type arm_state = { regs : regfile; flags : condition_flags;
                   vfp_regs : vfp_regfile; mem : memory;
                   locals : (int -> int); globals : (int -> int) }

val get_reg : arm_state -> arm_reg -> int

val set_reg : arm_state -> arm_reg -> int -> arm_state

val set_flags : arm_state -> condition_flags -> arm_state

val load_mem : arm_state -> int -> int

val store_mem : arm_state -> int -> int -> arm_state

val get_local : arm_state -> int -> int

val set_local : arm_state -> int -> int -> arm_state
