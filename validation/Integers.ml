open BinInt
open Datatypes

module I32 =
 struct
  (** val modulus : int **)

  let modulus =
    Z.pow ((fun p->2*p) 1) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) 1)))))

  (** val half_modulus : int **)

  let half_modulus =
    Z.pow ((fun p->2*p) 1) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) 1))))

  (** val max_unsigned : int **)

  let max_unsigned =
    Z.sub modulus 1

  (** val min_signed : int **)

  let min_signed =
    Z.opp half_modulus


  (** val repr : int -> int **)

  let repr n =
    Z.modulo n modulus

  (** val unsigned : int -> int **)

  let unsigned n =
    Z.modulo n modulus

  (** val signed : int -> int **)

  let signed n =
    let u = unsigned n in if Z.ltb u half_modulus then u else Z.sub u modulus

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add x y)

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub x y)

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul x y)

  (** val divs : int -> int -> int option **)

  let divs x y =
    if Z.eqb y 0
    then None
    else if (&&) (Z.eqb x min_signed) (Z.eqb y ((~-) 1))
         then None
         else Some (repr (Z.div (signed x) (signed y)))

  (** val divu : int -> int -> int option **)

  let divu x y =
    if Z.eqb y 0 then None else Some (repr (Z.div (unsigned x) (unsigned y)))

  (** val rems : int -> int -> int option **)

  let rems x y =
    if Z.eqb y 0 then None else Some (repr (Z.modulo (signed x) (signed y)))

  (** val remu : int -> int -> int option **)

  let remu x y =
    if Z.eqb y 0
    then None
    else Some (repr (Z.modulo (unsigned x) (unsigned y)))

  (** val coq_and : int -> int -> int **)

  let coq_and x y =
    repr (Z.coq_land x y)

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor x y)

  (** val xor : int -> int -> int **)

  let xor x y =
    repr (Z.coq_lxor x y)

  (** val shl : int -> int -> int **)

  let shl x y =
    repr
      (Z.shiftl x
        (Z.modulo (unsigned y) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr
      (Z.shiftr (unsigned x)
        (Z.modulo (unsigned y) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))))

  (** val shrs : int -> int -> int **)

  let shrs x y =
    repr
      (Z.shiftr (signed x)
        (Z.modulo (unsigned y) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) 1)))))))

  (** val rotl : int -> int -> int **)

  let rotl x y =
    let n =
      Z.modulo (unsigned y) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) 1)))))
    in
    coq_or (shl x (repr n))
      (shru x
        (repr
          (Z.sub ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
            ((fun p->2*p) 1))))) n)))

  (** val rotr : int -> int -> int **)

  let rotr x y =
    let n =
      Z.modulo (unsigned y) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) 1)))))
    in
    coq_or (shru x (repr n))
      (shl x
        (repr
          (Z.sub ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
            ((fun p->2*p) 1))))) n)))

  (** val eq : int -> int -> bool **)

  let eq x y =
    Z.eqb (unsigned x) (unsigned y)

  (** val ne : int -> int -> bool **)

  let ne x y =
    negb (eq x y)

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    Z.ltb (unsigned x) (unsigned y)

  (** val leu : int -> int -> bool **)

  let leu x y =
    Z.leb (unsigned x) (unsigned y)

  (** val gtu : int -> int -> bool **)

  let gtu x y =
    Z.gtb (unsigned x) (unsigned y)

  (** val geu : int -> int -> bool **)

  let geu x y =
    Z.geb (unsigned x) (unsigned y)

  (** val lts : int -> int -> bool **)

  let lts x y =
    Z.ltb (signed x) (signed y)

  (** val les : int -> int -> bool **)

  let les x y =
    Z.leb (signed x) (signed y)

  (** val gts : int -> int -> bool **)

  let gts x y =
    Z.gtb (signed x) (signed y)

  (** val ges : int -> int -> bool **)

  let ges x y =
    Z.geb (signed x) (signed y)

  (** val zero : int **)

  let zero =
    repr 0

  (** val one : int **)

  let one =
    repr 1

  (** val clz : int -> int **)

  let clz =
  let rec count_leading_zeros n acc =
    if acc >= 32 then 32
    else if (n land (1 lsl (31 - acc))) <> 0 then acc
    else count_leading_zeros n (acc + 1)
  in count_leading_zeros

  (** val ctz : int -> int **)

  let ctz =
  let rec count_trailing_zeros n acc =
    if acc >= 32 then 32
    else if (n land (1 lsl acc)) <> 0 then acc
    else count_trailing_zeros n (acc + 1)
  in count_trailing_zeros

  (** val popcnt : int -> int **)

  let popcnt =
  let rec count_bits n acc =
    if n = 0 then acc
    else count_bits (n lsr 1) (acc + (n land 1))
  in count_bits
 end

module I64 =
 struct
  (** val modulus : int **)

  let modulus =
    Z.pow ((fun p->2*p) 1) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
      ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))

  (** val half_modulus : int **)

  let half_modulus =
    Z.pow ((fun p->2*p) 1) ((fun p->1+2*p) ((fun p->1+2*p) ((fun p->1+2*p)
      ((fun p->1+2*p) ((fun p->1+2*p) 1)))))


  (** val repr : int -> int **)

  let repr n =
    Z.modulo n modulus

  (** val unsigned : int -> int **)

  let unsigned n =
    Z.modulo n modulus

  (** val signed : int -> int **)

  let signed n =
    let u = unsigned n in if Z.ltb u half_modulus then u else Z.sub u modulus

  (** val add : int -> int -> int **)

  let add x y =
    repr (Z.add x y)

  (** val sub : int -> int -> int **)

  let sub x y =
    repr (Z.sub x y)

  (** val mul : int -> int -> int **)

  let mul x y =
    repr (Z.mul x y)

  (** val coq_or : int -> int -> int **)

  let coq_or x y =
    repr (Z.coq_lor x y)

  (** val shl : int -> int -> int **)

  let shl x y =
    repr
      (Z.shiftl x
        (Z.modulo (unsigned y) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))))

  (** val shru : int -> int -> int **)

  let shru x y =
    repr
      (Z.shiftr (unsigned x)
        (Z.modulo (unsigned y) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))))

  (** val shrs : int -> int -> int **)

  let shrs x y =
    repr
      (Z.shiftr (signed x)
        (Z.modulo (unsigned y) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
          ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))))

  (** val rotl : int -> int -> int **)

  let rotl x y =
    let n =
      Z.modulo (unsigned y) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
    in
    coq_or (shl x (repr n))
      (shru x
        (repr
          (Z.sub ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
            ((fun p->2*p) ((fun p->2*p) 1)))))) n)))

  (** val rotr : int -> int -> int **)

  let rotr x y =
    let n =
      Z.modulo (unsigned y) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
        ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) 1))))))
    in
    coq_or (shru x (repr n))
      (shl x
        (repr
          (Z.sub ((fun p->2*p) ((fun p->2*p) ((fun p->2*p) ((fun p->2*p)
            ((fun p->2*p) ((fun p->2*p) 1)))))) n)))

  (** val eq : int -> int -> bool **)

  let eq x y =
    Z.eqb (unsigned x) (unsigned y)

  (** val ne : int -> int -> bool **)

  let ne x y =
    negb (eq x y)

  (** val ltu : int -> int -> bool **)

  let ltu x y =
    Z.ltb (unsigned x) (unsigned y)

  (** val lts : int -> int -> bool **)

  let lts x y =
    Z.ltb (signed x) (signed y)

  (** val gtu : int -> int -> bool **)

  let gtu x y =
    Z.gtb (unsigned x) (unsigned y)

  (** val gts : int -> int -> bool **)

  let gts x y =
    Z.gtb (signed x) (signed y)

  (** val leu : int -> int -> bool **)

  let leu x y =
    Z.leb (unsigned x) (unsigned y)

  (** val les : int -> int -> bool **)

  let les x y =
    Z.leb (signed x) (signed y)

  (** val geu : int -> int -> bool **)

  let geu x y =
    Z.geb (unsigned x) (unsigned y)

  (** val ges : int -> int -> bool **)

  let ges x y =
    Z.geb (signed x) (signed y)

  (** val clz : int -> int **)

  let clz =
  let rec count_leading_zeros n acc =
    if acc >= 64 then 64
    else if (n land (1 lsl (63 - acc))) <> 0 then acc
    else count_leading_zeros n (acc + 1)
  in count_leading_zeros

  (** val ctz : int -> int **)

  let ctz =
  let rec count_trailing_zeros n acc =
    if acc >= 64 then 64
    else if (n land (1 lsl acc)) <> 0 then acc
    else count_trailing_zeros n (acc + 1)
  in count_trailing_zeros

  (** val popcnt : int -> int **)

  let popcnt =
  let rec count_bits n acc =
    if n = 0 then acc
    else count_bits (n lsr 1) (acc + (n land 1))
  in count_bits

  (** val zero : int **)

  let zero =
    repr 0
 end

(* Implement the axioms that were left undefined *)
let clz x =
  let rec count_leading_zeros n acc =
    if acc >= 32 then 32
    else if (n land (1 lsl (31 - acc))) <> 0 then acc
    else count_leading_zeros n (acc + 1)
  in
  count_leading_zeros x 0

let ctz x =
  let rec count_trailing_zeros n acc =
    if acc >= 32 then 32
    else if (n land (1 lsl acc)) <> 0 then acc
    else count_trailing_zeros n (acc + 1)
  in
  count_trailing_zeros x 0

let popcnt x =
  let rec count_bits n acc =
    if n = 0 then acc
    else count_bits (n lsr 1) (acc + (n land 1))
  in
  count_bits x 0
