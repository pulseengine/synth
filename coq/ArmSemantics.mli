open ArmInstructions
open ArmState
open BinInt
open Bool
open Datatypes
open Integers

val f32_add_bits : I32.int -> I32.int -> I32.int

val f32_sub_bits : I32.int -> I32.int -> I32.int

val f32_mul_bits : I32.int -> I32.int -> I32.int

val f32_div_bits : I32.int -> I32.int -> I32.int

val f32_sqrt_bits : I32.int -> I32.int

val f32_abs_bits : I32.int -> I32.int

val f32_neg_bits : I32.int -> I32.int

val f64_add_bits : I32.int -> I32.int -> I32.int

val f64_sub_bits : I32.int -> I32.int -> I32.int

val f64_mul_bits : I32.int -> I32.int -> I32.int

val f64_div_bits : I32.int -> I32.int -> I32.int

val f64_sqrt_bits : I32.int -> I32.int

val f64_abs_bits : I32.int -> I32.int

val f64_neg_bits : I32.int -> I32.int

val f32_compare_flags : I32.int -> I32.int -> condition_flags

val f64_compare_flags : I32.int -> I32.int -> condition_flags

val cvt_f32_to_f64_bits : I32.int -> I32.int

val cvt_f64_to_f32_bits : I32.int -> I32.int

val cvt_s32_to_f32_bits : I32.int -> I32.int

val cvt_f32_to_s32_bits : I32.int -> I32.int

val i64_mul_lo_bits : I32.int -> I32.int -> I32.int -> I32.int -> I32.int

val i64_mul_hi_bits : I32.int -> I32.int -> I32.int -> I32.int -> I32.int

val i64_shl_lo_bits : I32.int -> I32.int -> I32.int -> I32.int

val i64_shl_hi_bits : I32.int -> I32.int -> I32.int -> I32.int

val i64_shru_lo_bits : I32.int -> I32.int -> I32.int -> I32.int

val i64_shru_hi_bits : I32.int -> I32.int -> I32.int -> I32.int

val i64_shrs_lo_bits : I32.int -> I32.int -> I32.int -> I32.int

val i64_shrs_hi_bits : I32.int -> I32.int -> I32.int -> I32.int

val i64_rotl_lo_bits : I32.int -> I32.int -> I32.int -> I32.int

val i64_rotl_hi_bits : I32.int -> I32.int -> I32.int -> I32.int

val i64_rotr_lo_bits : I32.int -> I32.int -> I32.int -> I32.int

val i64_rotr_hi_bits : I32.int -> I32.int -> I32.int -> I32.int

val i64_clz_bits : I32.int -> I32.int -> I32.int

val i64_ctz_bits : I32.int -> I32.int -> I32.int

val i64_popcnt_bits : I32.int -> I32.int -> I32.int

val i64_setcond_bits :
  I32.int -> I32.int -> I32.int -> I32.int -> condition -> I32.int

val i64_setcondz_bits : I32.int -> I32.int -> I32.int

val i64_divs_pair :
  I32.int -> I32.int -> I32.int -> I32.int -> (I32.int*I32.int) option

val i64_divu_pair :
  I32.int -> I32.int -> I32.int -> I32.int -> (I32.int*I32.int) option

val i64_rems_pair :
  I32.int -> I32.int -> I32.int -> I32.int -> (I32.int*I32.int) option

val i64_remu_pair :
  I32.int -> I32.int -> I32.int -> I32.int -> (I32.int*I32.int) option

val i64_const_lo : I64.int -> I32.int

val i64_const_hi : I64.int -> I32.int

val i64_extend_s_hi : I32.int -> I32.int

val i64_load_lo : memory -> int -> I32.int

val i64_load_hi : memory -> int -> I32.int

val compute_n_flag : I32.int -> bool

val compute_z_flag : I32.int -> bool

val compute_c_flag_add : I32.int -> I32.int -> bool

val compute_v_flag_add : I32.int -> I32.int -> I32.int -> bool

val compute_c_flag_sub : I32.int -> I32.int -> bool

val compute_v_flag_sub : I32.int -> I32.int -> bool

val compute_c_flag_sbc : I32.int -> I32.int -> bool -> bool

val compute_v_flag_sbc : I32.int -> I32.int -> bool -> bool

val update_flags_arith : I32.int -> bool -> bool -> condition_flags

val exec_instr : arm_instr -> arm_state -> arm_state option

val exec_program : arm_instr list -> arm_state -> arm_state option
