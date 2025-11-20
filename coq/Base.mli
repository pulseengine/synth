open BinInt

type 'a coq_EqDec =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_EqDec *)

val nat_eq_dec : int coq_EqDec

val coq_Z_eq_dec : int coq_EqDec

val update : 'a1 coq_EqDec -> ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a1 -> 'a2
