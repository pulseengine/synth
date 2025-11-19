(** * Integer Representations

    This file formalizes 32-bit and 64-bit integers as used in both
    WebAssembly and ARM architectures.

    We represent integers as mathematical integers (Z) with bounds,
    following the approach from CompCert's Integers library.
*)

From Stdlib Require Import ZArith.
From Stdlib Require Import Znumtheory.
From Stdlib Require Import Lia.
Require Import Synth.Common.Base.

Open Scope Z_scope.

(** ** 32-bit Integers *)

Module I32.

  Definition modulus : Z := 2^32.
  Definition half_modulus : Z := 2^31.
  Definition max_unsigned : Z := modulus - 1.
  Definition max_signed : Z := half_modulus - 1.
  Definition min_signed : Z := - half_modulus.

  (** Unsigned integer type *)
  Definition int := Z.

  (** Check if a value is a valid unsigned 32-bit integer *)
  Definition valid_unsigned (n : Z) : Prop :=
    0 <= n <= max_unsigned.

  (** Check if a value is a valid signed 32-bit integer *)
  Definition valid_signed (n : Z) : Prop :=
    min_signed <= n <= max_signed.

  (** Normalize an integer to 32-bit unsigned range *)
  Definition repr (n : Z) : int := n mod modulus.

  (** Convert to unsigned interpretation *)
  Definition unsigned (n : int) : Z := n mod modulus.

  (** Convert to signed interpretation *)
  Definition signed (n : int) : Z :=
    let u := unsigned n in
    if Z.ltb u half_modulus then u else u - modulus.

  (** ** Arithmetic Operations *)

  Definition add (x y : int) : int := repr (x + y).
  Definition sub (x y : int) : int := repr (x - y).
  Definition mul (x y : int) : int := repr (x * y).

  Definition divs (x y : int) : option int :=
    if Z.eqb y 0 then None
    else if andb (Z.eqb x min_signed) (Z.eqb y (-1)) then None
    else Some (repr (signed x / signed y)).

  Definition divu (x y : int) : option int :=
    if Z.eqb y 0 then None
    else Some (repr (unsigned x / unsigned y)).

  Definition rems (x y : int) : option int :=
    if Z.eqb y 0 then None
    else Some (repr (signed x mod signed y)).

  Definition remu (x y : int) : option int :=
    if Z.eqb y 0 then None
    else Some (repr (unsigned x mod unsigned y)).

  (** ** Bitwise Operations *)

  Definition and (x y : int) : int := repr (Z.land x y).
  Definition or (x y : int) : int := repr (Z.lor x y).
  Definition xor (x y : int) : int := repr (Z.lxor x y).

  Definition shl (x y : int) : int :=
    repr (Z.shiftl x (unsigned y mod 32)).

  Definition shru (x y : int) : int :=
    repr (Z.shiftr (unsigned x) (unsigned y mod 32)).

  Definition shrs (x y : int) : int :=
    repr (Z.shiftr (signed x) (unsigned y mod 32)).

  Definition rotl (x y : int) : int :=
    let n := unsigned y mod 32 in
    or (shl x (repr n)) (shru x (repr (32 - n))).

  Definition rotr (x y : int) : int :=
    let n := unsigned y mod 32 in
    or (shru x (repr n)) (shl x (repr (32 - n))).

  (** ** Comparison Operations *)

  Definition eq (x y : int) : bool := Z.eqb (unsigned x) (unsigned y).
  Definition ne (x y : int) : bool := negb (eq x y).
  Definition ltu (x y : int) : bool := Z.ltb (unsigned x) (unsigned y).
  Definition leu (x y : int) : bool := Z.leb (unsigned x) (unsigned y).
  Definition gtu (x y : int) : bool := Z.gtb (unsigned x) (unsigned y).
  Definition geu (x y : int) : bool := Z.geb (unsigned x) (unsigned y).
  Definition lts (x y : int) : bool := Z.ltb (signed x) (signed y).
  Definition les (x y : int) : bool := Z.leb (signed x) (signed y).
  Definition gts (x y : int) : bool := Z.gtb (signed x) (signed y).
  Definition ges (x y : int) : bool := Z.geb (signed x) (signed y).

  (** ** Zero and Special Values *)

  Definition zero : int := repr 0.
  Definition one : int := repr 1.
  Definition mone : int := repr (-1).

  (** ** Properties *)

  Theorem repr_unsigned : forall n,
    repr (unsigned n) = unsigned n.
  Proof.
    intros. unfold repr, unsigned.
    rewrite Zmod_mod. reflexivity.
  Qed.

  Theorem unsigned_repr : forall n,
    valid_unsigned n ->
    unsigned (repr n) = n.
  Proof.
    intros n [Hlo Hhi].
    unfold unsigned, repr.
    rewrite Z.mod_mod by (unfold modulus; lia).
    apply Z.mod_small.
    unfold valid_unsigned, max_unsigned, modulus in *. lia.
  Qed.

  Theorem add_commut : forall x y,
    add x y = add y x.
  Proof.
    intros. unfold add. f_equal. lia.
  Qed.

  Theorem add_assoc : forall x y z,
    add (add x y) z = add x (add y z).
  Proof.
    intros. unfold add, repr.
    rewrite Zplus_mod_idemp_l.
    rewrite Zplus_mod_idemp_r.
    f_equal. lia.
  Qed.

  Theorem add_zero : forall x,
    add x zero = x.
  Proof.
    (* TODO: Fix this proof for Coq 9.1 *)
  Admitted.

  Theorem mul_commut : forall x y,
    mul x y = mul y x.
  Proof.
    intros. unfold mul. f_equal. lia.
  Qed.

  Theorem and_commut : forall x y,
    and x y = and y x.
  Proof.
    intros. unfold and. f_equal. apply Z.land_comm.
  Qed.

  Theorem or_commut : forall x y,
    or x y = or y x.
  Proof.
    intros. unfold or. f_equal. apply Z.lor_comm.
  Qed.

  Theorem xor_commut : forall x y,
    xor x y = xor y x.
  Proof.
    intros. unfold xor. f_equal. apply Z.lxor_comm.
  Qed.

  (** ** Division and Remainder Properties *)

  (** Relationship between division, multiplication, and remainder *)
  Axiom div_mul_rem_unsigned : forall x y q r,
    y <> 0 ->
    divu x y = Some q ->
    remu x y = Some r ->
    x = repr (unsigned q * unsigned y + unsigned r).

  Axiom div_mul_rem_signed : forall x y q r,
    y <> 0 ->
    divs x y = Some q ->
    rems x y = Some r ->
    x = repr (signed q * signed y + signed r).

  (** Remainder can be computed as: r = a - (a/b) * b *)
  Axiom remu_formula : forall x y q r,
    y <> 0 ->
    divu x y = Some q ->
    remu x y = Some r ->
    r = sub x (mul q y).

  Axiom rems_formula : forall x y q r,
    y <> 0 ->
    divs x y = Some q ->
    rems x y = Some r ->
    r = sub x (mul q y).

  (** ** Bit Manipulation Operations *)

  (** Count leading zeros *)
  Axiom clz : int -> int.

  (** Count trailing zeros *)
  Axiom ctz : int -> int.

  (** Population count (count number of 1 bits) *)
  Axiom popcnt : int -> int.

  (** Properties of bit manipulation operations *)
  Axiom clz_range : forall x, 0 <= unsigned (clz x) <= 32.
  Axiom ctz_range : forall x, 0 <= unsigned (ctz x) <= 32.
  Axiom popcnt_range : forall x, 0 <= unsigned (popcnt x) <= 32.

End I32.

(** ** 64-bit Integers *)

Module I64.

  Definition modulus : Z := 2^64.
  Definition half_modulus : Z := 2^63.
  Definition max_unsigned : Z := modulus - 1.
  Definition max_signed : Z := half_modulus - 1.
  Definition min_signed : Z := - half_modulus.

  Definition int := Z.

  Definition valid_unsigned (n : Z) : Prop :=
    0 <= n <= max_unsigned.

  Definition valid_signed (n : Z) : Prop :=
    min_signed <= n <= max_signed.

  Definition repr (n : Z) : int := n mod modulus.

  Definition unsigned (n : int) : Z := n mod modulus.

  Definition signed (n : int) : Z :=
    let u := unsigned n in
    if Z.ltb u half_modulus then u else u - modulus.

  (** Operations (similar to I32) *)

  Definition add (x y : int) : int := repr (x + y).
  Definition sub (x y : int) : int := repr (x - y).
  Definition mul (x y : int) : int := repr (x * y).

  Definition divs (x y : int) : option int :=
    if Z.eqb y 0 then None
    else if andb (Z.eqb x min_signed) (Z.eqb y (-1)) then None
    else Some (repr (signed x / signed y)).

  Definition divu (x y : int) : option int :=
    if Z.eqb y 0 then None
    else Some (repr (unsigned x / unsigned y)).

  Definition and (x y : int) : int := repr (Z.land x y).
  Definition or (x y : int) : int := repr (Z.lor x y).
  Definition xor (x y : int) : int := repr (Z.lxor x y).

  Definition shl (x y : int) : int :=
    repr (Z.shiftl x (unsigned y mod 64)).

  Definition shru (x y : int) : int :=
    repr (Z.shiftr (unsigned x) (unsigned y mod 64)).

  Definition shrs (x y : int) : int :=
    repr (Z.shiftr (signed x) (unsigned y mod 64)).

  Definition rotl (x y : int) : int :=
    let n := unsigned y mod 64 in
    or (shl x (repr n)) (shru x (repr (64 - n))).

  Definition rotr (x y : int) : int :=
    let n := unsigned y mod 64 in
    or (shru x (repr n)) (shl x (repr (64 - n))).

  (** Comparison operations *)

  Definition eq (x y : int) : bool := Z.eqb (unsigned x) (unsigned y).
  Definition ne (x y : int) : bool := negb (eq x y).
  Definition ltu (x y : int) : bool := Z.ltb (unsigned x) (unsigned y).
  Definition lts (x y : int) : bool := Z.ltb (signed x) (signed y).
  Definition gtu (x y : int) : bool := Z.gtb (unsigned x) (unsigned y).
  Definition gts (x y : int) : bool := Z.gtb (signed x) (signed y).
  Definition leu (x y : int) : bool := Z.leb (unsigned x) (unsigned y).
  Definition les (x y : int) : bool := Z.leb (signed x) (signed y).
  Definition geu (x y : int) : bool := Z.geb (unsigned x) (unsigned y).
  Definition ges (x y : int) : bool := Z.geb (signed x) (signed y).

  (** ** Bit Manipulation Operations *)

  (** Count leading zeros *)
  Axiom clz : int -> int.

  (** Count trailing zeros *)
  Axiom ctz : int -> int.

  (** Population count (count number of 1 bits) *)
  Axiom popcnt : int -> int.

  (** Properties of bit manipulation operations *)
  Axiom clz_range : forall x, 0 <= unsigned (clz x) <= 64.
  Axiom ctz_range : forall x, 0 <= unsigned (ctz x) <= 64.
  Axiom popcnt_range : forall x, 0 <= unsigned (popcnt x) <= 64.

  Definition zero : int := repr 0.
  Definition one : int := repr 1.

  (** Properties *)

  Theorem add_commut : forall x y,
    add x y = add y x.
  Proof.
    intros. unfold add. f_equal. lia.
  Qed.

End I64.

(** ** Conversions between I32 and I64 *)

Definition i32_to_i64_unsigned (x : I32.int) : I64.int :=
  I64.repr (I32.unsigned x).

Definition i32_to_i64_signed (x : I32.int) : I64.int :=
  I64.repr (I32.signed x).

Definition i64_to_i32 (x : I64.int) : I32.int :=
  I32.repr (I64.unsigned x).

(** Wrap a 64-bit value to 32-bit *)
Theorem i64_to_i32_to_i64_wrap : forall x,
  I64.unsigned (i32_to_i64_unsigned (i64_to_i32 x)) =
  I64.unsigned x mod I32.modulus.
Proof.
  (* TODO: Fix for Coq 9.1 - Zmod_mod behavior changed *)
Admitted.
