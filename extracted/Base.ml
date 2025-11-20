open BinInt

type 'a coq_EqDec =
  'a -> 'a -> bool
  (* singleton inductive, whose constructor was Build_EqDec *)

(** val nat_eq_dec : int coq_EqDec **)

let nat_eq_dec =
  (=)

(** val coq_Z_eq_dec : int coq_EqDec **)

let coq_Z_eq_dec =
  Z.eq_dec

(** val update : 'a1 coq_EqDec -> ('a1 -> 'a2) -> 'a1 -> 'a2 -> 'a1 -> 'a2 **)

let update h f x v y =
  if h x y then v else f y
