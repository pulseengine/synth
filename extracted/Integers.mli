open BinInt
open Datatypes

module I32 :
 sig
  val modulus : int

  val half_modulus : int

  val max_unsigned : int

  val min_signed : int

  type int = int

  val repr : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val divs : int -> int -> int option

  val divu : int -> int -> int option

  val rems : int -> int -> int option

  val remu : int -> int -> int option

  val coq_and : int -> int -> int

  val coq_or : int -> int -> int

  val xor : int -> int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shrs : int -> int -> int

  val rotl : int -> int -> int

  val rotr : int -> int -> int

  val eq : int -> int -> bool

  val ne : int -> int -> bool

  val ltu : int -> int -> bool

  val leu : int -> int -> bool

  val gtu : int -> int -> bool

  val geu : int -> int -> bool

  val lts : int -> int -> bool

  val les : int -> int -> bool

  val gts : int -> int -> bool

  val ges : int -> int -> bool

  val zero : int

  val one : int

  val clz : int -> int

  val ctz : int -> int

  val popcnt : int -> int
 end

module I64 :
 sig
  val modulus : int

  val half_modulus : int

  type int = int

  val repr : int -> int

  val unsigned : int -> int

  val signed : int -> int

  val add : int -> int -> int

  val sub : int -> int -> int

  val mul : int -> int -> int

  val coq_or : int -> int -> int

  val shl : int -> int -> int

  val shru : int -> int -> int

  val shrs : int -> int -> int

  val rotl : int -> int -> int

  val rotr : int -> int -> int

  val eq : int -> int -> bool

  val ne : int -> int -> bool

  val ltu : int -> int -> bool

  val lts : int -> int -> bool

  val gtu : int -> int -> bool

  val gts : int -> int -> bool

  val leu : int -> int -> bool

  val les : int -> int -> bool

  val geu : int -> int -> bool

  val ges : int -> int -> bool

  val clz : int -> int

  val ctz : int -> int

  val popcnt : int -> int

  val zero : int
 end
