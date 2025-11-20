open BinPos
open Datatypes
open NatDef
open PosDef

module Z :
 sig
  val double : int -> int

  val succ_double : int -> int

  val pred_double : int -> int

  val pos_sub : int -> int -> int

  val add : int -> int -> int

  val opp : int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val pow_pos : int -> int -> int

  val pow : int -> int -> int

  val compare : int -> int -> comparison

  val leb : int -> int -> bool

  val ltb : int -> int -> bool

  val eqb : int -> int -> bool

  val of_nat : int -> int

  val of_N : int -> int

  val pos_div_eucl : int -> int -> int*int

  val div_eucl : int -> int -> int*int

  val div : int -> int -> int

  val modulo : int -> int -> int

  val div2 : int -> int

  val shiftl : int -> int -> int

  val shiftr : int -> int -> int

  val coq_lor : int -> int -> int

  val coq_land : int -> int -> int

  val coq_lxor : int -> int -> int

  val pred : int -> int

  val geb : int -> int -> bool

  val gtb : int -> int -> bool

  val eq_dec : int -> int -> bool

  val lnot : int -> int
 end
