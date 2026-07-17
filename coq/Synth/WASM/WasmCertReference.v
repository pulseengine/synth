(** * VCR-WASM-001 — WasmCert-Coq source-semantics reference (i32 + i64 batches)

    GOAL (epic #242, VCR-WASM-001, roadmap Track B). WasmSemantics.v is a
    HAND-WRITTEN stack-machine model: every source-side correctness statement
    in this suite is "consistent with our own model" — a modeling bug in
    [exec_wasm_instr] is invisible to the proofs. VCR-WASM-001 wants the WASM
    source semantics ANCHORED on an INDEPENDENTLY derived reference:
    WasmCert-Coq (Watt et al., FM'21), the community-standard mechanized
    WebAssembly 1.0 semantics. This mirrors, on the WASM side, what
    VCR-ISA-001 (#667 / SailArmBridge.v) does on the ARM/selector side:
    "anchor/generate, don't mirror".

    WHAT THIS FILE IS. Exactly as SailArmBridge transcribes the Sail [execute]
    clauses BY HAND with line-level provenance, this file TRANSCRIBES
    WasmCert-Coq's operational rules for the i32 integer fragment (arithmetic,
    bitwise, shifts, eqz, and the full comparison family — 19 ops) into
    synth's own [I32] value primitives, with verbatim provenance citations to
    the WasmCert-Coq / CompCert sources.

    *** TRANSCRIPTION — to be replaced by a real external dependency. ***
    PHASE-2 FEASIBILITY VERDICT (v0.47, see the VCR-WASM-001 entry in
    artifacts/verified-codegen-roadmap.yaml for the full evidence): the real
    dependency is NIX-FEASIBLE — [coqPackages.wasmcert] (coq9.0-wasm-2.2.0)
    exists in the exact nixpkgs commit the rules_rocq_rust toolchain pins
    (88d3861a) and nix-builds green against the same Rocq 9.0.1 — but
    bazel-wiring was DEFERRED on three named blockers: (1) rules_rocq_rust had
    no generic extra-coq-package hook (fork change required); (2) nixpkgs
    wasmcert 2.2.0 depends on CompCert 3.16, whose license (inria-compcert)
    is unfree — a policy decision, not a code change; (3) upstream WasmCert
    2.2.1 drops the CompCert dependency, so the next nixpkgs bump removes (2).

    PHASE-3 STATUS (v0.48, #242): blocker (1) is CLOSED — the generic
    extra-coq-package HOOK is LANDED (patches/rules_rocq_rust_extra_coq_pkg.patch,
    a `rocq.extra_coq_package(name=, attribute_path=)` bzlmod tag). Blockers
    (2)+(3) remain, so the REAL DEPENDENCY IS NOT YET WIRED and this file STAYS
    a hand transcription. Re-verified 2026-07-17 by nix eval against pin
    88d3861a: [coqPackages.wasmcert] is 2.2.0 (MIT) but PROPAGATES
    [coqPackages.compcert] 3.16 (license inria-compcert, meta.license.free =
    false, meta.unfree = true), which CI's no-unfree-dependency policy refuses;
    wasmcert >= 2.2.1 (which drops CompCert) is NOT yet in the pin. When a
    nixpkgs rev carrying wasmcert >= 2.2.1 lands, the migration is mechanical:
    declare the `extra_coq_package` tag, `Require` the real WasmCert
    numerics/operations modules from WasmCertBridge.v, and delete this file —
    at which point the "trusted transcription" caveat DIES. Until then it does
    NOT: the reference below remains a hand transcription pinned to the EXACT
    nix-built 2.2.0 sources.

    PROVENANCE (pinned). All citations below refer to:

      - WasmCert-Coq 2.2.0 as built by nixpkgs 88d3861a for Rocq 9.0.1
        (derivation coq9.0-wasm-2.2.0), file [Wasm/numerics.v] and
        [Wasm/operations.v] — line numbers from the installed sources.
        The i32 type is instantiated at numerics.v:1034-1035
        ([Module Int32. Include Make(Integers.Wordsize_32).]), so
        [wordsize = 32] throughout, and [Module Make] includes CompCert's
        [Integers.Make] (numerics.v:98-102): the primitive [add]/[sub]/…
        below ARE CompCert's.

      - CompCert 3.16, [lib/Integers.v] (functor [Make], shared by [Int]):
          135: Definition unsigned (n: int) : Z := intval n.
          137: Definition signed (n: int) : Z :=
          138:   let x := unsigned n in
          139:   if zlt x half_modulus then x else x - modulus.
          144: Definition repr (x: Z) : int :=
          145:   mkint (Z_mod_modulus x) (Z_mod_modulus_range' x).
          147: Definition zero := repr 0.
          148: Definition one  := repr 1.
        and [lib/Coqlib.v]:
          249: Definition zeq: forall (x y: Z), {x = y} + {x <> y} := Z.eq_dec.
          269: Definition zlt: forall (x y: Z), {x < y} + {x >= y} := Z_lt_dec.
        (so the transcriptions below use [Z.eq_dec] / [Z_lt_dec] verbatim).

    The salient, deliberately-preserved feature of the reference is that
    CompCert (hence WasmCert) NORMALIZES each operand with [unsigned] BEFORE
    operating, then [repr]s the result. Synth's [I32] operates on RAW
    representatives (its [int := Z] is unnormalized). The two agree mod 2^32
    but are DEFINITIONALLY DIFFERENT — so the bridge lemmas in
    WasmCertBridge.v are genuine proofs exercising the raw-vs-normalized gap
    (Zplus_mod/Zminus_mod/Zmult_mod for arithmetic, bit-level [Z.testbit]
    reasoning for the bitwise ops, shift-count double-normalization collapse
    for the shifts). For the comparisons the reference keeps CompCert's
    SUMBOOL decisions ([Z.eq_dec]/[Z_lt_dec] = Coqlib's zeq/zlt) and
    WasmCert's ORIENTATION (gt/le/ge are DERIVED from [ltu]/[lt] by argument
    swap and negation, numerics.v:974-979), whereas synth uses boolean
    [Z.gtb]/[Z.leb]/[Z.geb] directly — the bridge discharges both gaps.

    NON-VACUITY. Every reference rule is phrased ONLY in the value-encoding
    primitives [I32.repr] / [I32.unsigned] / [Z] operators and stdlib decision
    procedures — never in synth's [I32.add]/[I32.sub]/…/[I32.lts] operations
    and never in [exec_wasm_instr]. So the bridge lemmas are not synth
    agreeing with a copy of itself: a WRONG synth semantics (wrong operation,
    wrong operand order, wrong shift masking, wrong comparison signedness or
    orientation) FAILS the corresponding bridge theorem.
*)

From Stdlib Require Import ZArith.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.

Open Scope Z_scope.

(** ** Arithmetic (WasmCert numerics.v — Tmixin at 952-954)

    numerics.v:698  Definition iadd : T -> T -> T := add.
    numerics.v:701  Definition isub : T -> T -> T := sub.
    numerics.v:704  Definition imul : T -> T -> T := mul.
    CompCert Integers.v:
      186: Definition add (x y: int) : int := repr (unsigned x + unsigned y).
      188: Definition sub (x y: int) : int := repr (unsigned x - unsigned y).
      190: Definition mul (x y: int) : int := repr (unsigned x * unsigned y).

    NOTE the [I32.unsigned] on each operand — the CompCert/WasmCert
    normalize-then-operate form, distinct from synth's raw
    [I32.add x y := repr (x + y)] etc. *)
Definition wasmcert_i32_add (x y : I32.int) : I32.int :=
  I32.repr (I32.unsigned x + I32.unsigned y).

Definition wasmcert_i32_sub (x y : I32.int) : I32.int :=
  I32.repr (I32.unsigned x - I32.unsigned y).

Definition wasmcert_i32_mul (x y : I32.int) : I32.int :=
  I32.repr (I32.unsigned x * I32.unsigned y).

(** ** Bitwise (WasmCert numerics.v — Tmixin at 960-962)

    numerics.v:902  Definition iand : T -> T -> T := and.
    numerics.v:905  Definition ior  : T -> T -> T := or.
    numerics.v:908  Definition ixor : T -> T -> T := xor.
    CompCert Integers.v:
      205: Definition and (x y: int): int := repr (Z.land (unsigned x) (unsigned y)).
      206: Definition or  (x y: int): int := repr (Z.lor  (unsigned x) (unsigned y)).
      207: Definition xor (x y: int): int := repr (Z.lxor (unsigned x) (unsigned y)). *)
Definition wasmcert_i32_and (x y : I32.int) : I32.int :=
  I32.repr (Z.land (I32.unsigned x) (I32.unsigned y)).

Definition wasmcert_i32_or (x y : I32.int) : I32.int :=
  I32.repr (Z.lor (I32.unsigned x) (I32.unsigned y)).

Definition wasmcert_i32_xor (x y : I32.int) : I32.int :=
  I32.repr (Z.lxor (I32.unsigned x) (I32.unsigned y)).

(** ** Shifts (WasmCert numerics.v:911-922 — Tmixin at 963-965)

    numerics.v:911-913  Definition ishl (i1 i2 : T) : T :=
                          let k := repr (unsigned i2 mod wordsize)%Z in
                          shl i1 k.
    numerics.v:916-918  Definition ishr_u (i1 i2: T) : T :=
                          let k := repr (unsigned i2 mod wordsize)%Z in
                          shru i1 k.
    numerics.v:920-922  Definition ishr_s (i1 i2: T) : T :=
                          let k := repr (unsigned i2 mod wordsize)%Z in
                          shr i1 k.
    with [wordsize = 32] (Wordsize_32, numerics.v:1034-1035).
    CompCert Integers.v:
      213: Definition shl  (x y: int): int := repr (Z.shiftl (unsigned x) (unsigned y)).
      214: Definition shru (x y: int): int := repr (Z.shiftr (unsigned x) (unsigned y)).
      215: Definition shr  (x y: int): int := repr (Z.shiftr (signed x) (unsigned y)).

    The WasmCert shift count is DOUBLY normalized: [unsigned (repr (unsigned
    i2 mod 32))] — the transcription preserves that faithfully. *)
Definition wasmcert_i32_shl (x y : I32.int) : I32.int :=
  let k := I32.repr (I32.unsigned y mod 32) in
  I32.repr (Z.shiftl (I32.unsigned x) (I32.unsigned k)).

Definition wasmcert_i32_shr_u (x y : I32.int) : I32.int :=
  let k := I32.repr (I32.unsigned y mod 32) in
  I32.repr (Z.shiftr (I32.unsigned x) (I32.unsigned k)).

(** Transcription of CompCert [signed] (Integers.v:137-139), used by [shr]
    and the signed comparisons. [zlt] is [Z_lt_dec] (Coqlib.v:269). *)
Definition wasmcert_i32_signed (n : I32.int) : Z :=
  let x := I32.unsigned n in
  if Z_lt_dec x I32.half_modulus then x else x - I32.modulus.

Definition wasmcert_i32_shr_s (x y : I32.int) : I32.int :=
  let k := I32.repr (I32.unsigned y mod 32) in
  I32.repr (Z.shiftr (wasmcert_i32_signed x) (I32.unsigned k)).

(** ** Equality tests (WasmCert numerics.v — Tmixin at 969-970;
       operations.v:452-455 [app_testop_i] routes Eqz to [int_eqz])

    numerics.v:969  int_eq  := eq ;
    numerics.v:970  int_eqz := eq zero ;
    numerics.v:93-94 (generic, wired by operations.v:461)
                    Definition int_ne … := fun x y => negb (int_eq mx x y).
    CompCert Integers.v:
      177: Definition eq (x y: int) : bool :=
      178:   if zeq (unsigned x) (unsigned y) then true else false.
      147: Definition zero := repr 0.
    [zeq] is [Z.eq_dec] (Coqlib.v:249).

    NOTE [int_eqz := eq zero]: zero is the FIRST argument — the transcription
    preserves that orientation. *)
Definition wasmcert_i32_eq (x y : I32.int) : bool :=
  if Z.eq_dec (I32.unsigned x) (I32.unsigned y) then true else false.

Definition wasmcert_i32_eqz (v : I32.int) : bool :=
  wasmcert_i32_eq (I32.repr 0) v.

Definition wasmcert_i32_ne (x y : I32.int) : bool :=
  negb (wasmcert_i32_eq x y).

(** ** Order comparisons (WasmCert numerics.v — Tmixin at 972-979;
       operations.v:457-470 [app_relop_i] routes ROI_lt/gt/le/ge here)

    numerics.v:972  int_lt_u := ltu ;
    numerics.v:973  int_lt_s := lt ;
    numerics.v:974  int_gt_u x y := ltu y x ;
    numerics.v:975  int_gt_s x y := lt y x ;
    numerics.v:976  int_le_u x y := negb (ltu y x) ;
    numerics.v:977  int_le_s x y := negb (lt y x) ;
    numerics.v:978  int_ge_u x y := negb (ltu x y) ;
    numerics.v:979  int_ge_s x y := negb (lt x y) ;
    CompCert Integers.v:
      179: Definition lt (x y: int) : bool :=
      180:   if zlt (signed x) (signed y) then true else false.
      181: Definition ltu (x y: int) : bool :=
      182:   if zlt (unsigned x) (unsigned y) then true else false.

    gt/le/ge are DERIVED (argument swap + negation) — synth instead uses
    [Z.gtb]/[Z.leb]/[Z.geb] directly, so the bridge lemmas discharge a real
    orientation gap, not just an encoding one. *)
Definition wasmcert_i32_lt_u (x y : I32.int) : bool :=
  if Z_lt_dec (I32.unsigned x) (I32.unsigned y) then true else false.

Definition wasmcert_i32_lt_s (x y : I32.int) : bool :=
  if Z_lt_dec (wasmcert_i32_signed x) (wasmcert_i32_signed y) then true else false.

Definition wasmcert_i32_gt_u (x y : I32.int) : bool :=
  wasmcert_i32_lt_u y x.

Definition wasmcert_i32_gt_s (x y : I32.int) : bool :=
  wasmcert_i32_lt_s y x.

Definition wasmcert_i32_le_u (x y : I32.int) : bool :=
  negb (wasmcert_i32_lt_u y x).

Definition wasmcert_i32_le_s (x y : I32.int) : bool :=
  negb (wasmcert_i32_lt_s y x).

Definition wasmcert_i32_ge_u (x y : I32.int) : bool :=
  negb (wasmcert_i32_lt_u x y).

Definition wasmcert_i32_ge_s (x y : I32.int) : bool :=
  negb (wasmcert_i32_lt_s x y).

(** * VCR-WASM-001 — i64 integer fragment (phase 3 transcription batch)

    Same pinned sources, same functor. WasmCert's [Int64] is instantiated at
    numerics.v:1038-1039 ([Module Int64. Include Make(Integers.Wordsize_64).]),
    so [wordsize = 64] throughout, and [Module Make] includes CompCert's
    [Integers.Make] (numerics.v:98-102) EXACTLY as for i32 — the primitive
    [add]/[sub]/…/[rol]/[ror] below are the SAME CompCert definitions, now read
    at [zwordsize = 64].

    *** STILL A TRANSCRIPTION. *** This i64 fragment is transcribed by hand from
    the identical pinned coq9.0-wasm-2.2.0 sources (nix store derivation
    coq9.0-wasm-2.2.0, [Wasm/numerics.v]) and CompCert 3.16
    ([compcert/lib/Integers.v]) — NOT the real external dependency. The
    feasibility verdict, the unfree-CompCert-3.16 blocker, and the mechanical
    migration recipe are exactly as stated in the i32 header above; nothing in
    this batch retires the "trusted transcription" caveat. It dies only when a
    nixpkgs rev ships wasmcert >= 2.2.1.

    All arithmetic/bitwise/shift/comparison CITATIONS are the SAME functor lines
    as the i32 fragment (the generic [Make], read at wordsize 64):
      numerics.v:698/701/704  iadd/isub/imul := add/sub/mul
      numerics.v:902/905/908  iand/ior/ixor  := and/or/xor
      numerics.v:911-922      ishl/ishr_u/ishr_s (double-normalized count, wordsize 64)
      numerics.v:966-967      int_rotl := rol ; int_rotr := ror
      numerics.v:969-979      int_eq/eqz/ne/lt_*/gt_*/le_*/ge_* (as for i32)
      CompCert Integers.v:186/188/190  add/sub/mul   := repr (op (unsigned x) (unsigned y))
      CompCert Integers.v:205/206/207  and/or/xor
      CompCert Integers.v:213/214/215  shl/shru/shr
      CompCert Integers.v:177/179/181  eq/lt/ltu
    NEW citations for this batch (rotates, verbatim CompCert 3.16 Integers.v):
      217: Definition rol (x y: int) : int :=
      218:   let n := (unsigned y) mod zwordsize in
      219:   repr (Z.lor (Z.shiftl (unsigned x) n) (Z.shiftr (unsigned x) (zwordsize - n))).
      220: Definition ror (x y: int) : int :=
      221:   let n := (unsigned y) mod zwordsize in
      222:   repr (Z.lor (Z.shiftr (unsigned x) n) (Z.shiftl (unsigned x) (zwordsize - n))).
    with [zwordsize = 64] for [Int64]. *)

(** ** i64 Arithmetic (numerics.v:698/701/704 → CompCert 186/188/190) *)
Definition wasmcert_i64_add (x y : I64.int) : I64.int :=
  I64.repr (I64.unsigned x + I64.unsigned y).

Definition wasmcert_i64_sub (x y : I64.int) : I64.int :=
  I64.repr (I64.unsigned x - I64.unsigned y).

Definition wasmcert_i64_mul (x y : I64.int) : I64.int :=
  I64.repr (I64.unsigned x * I64.unsigned y).

(** ** i64 Bitwise (numerics.v:902/905/908 → CompCert 205/206/207) *)
Definition wasmcert_i64_and (x y : I64.int) : I64.int :=
  I64.repr (Z.land (I64.unsigned x) (I64.unsigned y)).

Definition wasmcert_i64_or (x y : I64.int) : I64.int :=
  I64.repr (Z.lor (I64.unsigned x) (I64.unsigned y)).

Definition wasmcert_i64_xor (x y : I64.int) : I64.int :=
  I64.repr (Z.lxor (I64.unsigned x) (I64.unsigned y)).

(** ** i64 Shifts (numerics.v:911-922 → CompCert 213/214/215, wordsize 64).
    Double-normalized shift count, exactly as i32 but mod 64. *)
Definition wasmcert_i64_shl (x y : I64.int) : I64.int :=
  let k := I64.repr (I64.unsigned y mod 64) in
  I64.repr (Z.shiftl (I64.unsigned x) (I64.unsigned k)).

Definition wasmcert_i64_shr_u (x y : I64.int) : I64.int :=
  let k := I64.repr (I64.unsigned y mod 64) in
  I64.repr (Z.shiftr (I64.unsigned x) (I64.unsigned k)).

(** Transcription of CompCert [signed] (Integers.v:137-139) at wordsize 64. *)
Definition wasmcert_i64_signed (n : I64.int) : Z :=
  let x := I64.unsigned n in
  if Z_lt_dec x I64.half_modulus then x else x - I64.modulus.

Definition wasmcert_i64_shr_s (x y : I64.int) : I64.int :=
  let k := I64.repr (I64.unsigned y mod 64) in
  I64.repr (Z.shiftr (wasmcert_i64_signed x) (I64.unsigned k)).

(** ** i64 Equality tests (numerics.v:969-970 → CompCert eq 177, zeq = Z.eq_dec) *)
Definition wasmcert_i64_eq (x y : I64.int) : bool :=
  if Z.eq_dec (I64.unsigned x) (I64.unsigned y) then true else false.

Definition wasmcert_i64_eqz (v : I64.int) : bool :=
  wasmcert_i64_eq (I64.repr 0) v.

Definition wasmcert_i64_ne (x y : I64.int) : bool :=
  negb (wasmcert_i64_eq x y).

(** ** i64 Order comparisons (numerics.v:972-979 → CompCert lt 179 / ltu 181).
    gt/le/ge DERIVED from lt/ltu by argument swap + negation, verbatim. *)
Definition wasmcert_i64_lt_u (x y : I64.int) : bool :=
  if Z_lt_dec (I64.unsigned x) (I64.unsigned y) then true else false.

Definition wasmcert_i64_lt_s (x y : I64.int) : bool :=
  if Z_lt_dec (wasmcert_i64_signed x) (wasmcert_i64_signed y) then true else false.

Definition wasmcert_i64_gt_u (x y : I64.int) : bool :=
  wasmcert_i64_lt_u y x.

Definition wasmcert_i64_gt_s (x y : I64.int) : bool :=
  wasmcert_i64_lt_s y x.

Definition wasmcert_i64_le_u (x y : I64.int) : bool :=
  negb (wasmcert_i64_lt_u y x).

Definition wasmcert_i64_le_s (x y : I64.int) : bool :=
  negb (wasmcert_i64_lt_s y x).

Definition wasmcert_i64_ge_u (x y : I64.int) : bool :=
  negb (wasmcert_i64_lt_u x y).

Definition wasmcert_i64_ge_s (x y : I64.int) : bool :=
  negb (wasmcert_i64_lt_s x y).

(** ** i64 Rotates (numerics.v:966-967 → CompCert rol 217-219 / ror 220-222,
    zwordsize = 64). The reference [repr]s ONCE over the whole [Z.lor], and
    the sub-shift count [zwordsize - n] is NOT re-normalized — distinct from
    synth's [I64.rotl] which composes [or (shl …) (shru …)] with each shift
    re-normalizing its count mod 64. The bridge (WasmCertBridge.v) discharges
    that gap, incl. the [n = 0] boundary where [zwordsize - n = 64]. *)
Definition wasmcert_i64_rotl (x y : I64.int) : I64.int :=
  let n := I64.unsigned y mod 64 in
  I64.repr (Z.lor (Z.shiftl (I64.unsigned x) n)
                  (Z.shiftr (I64.unsigned x) (64 - n))).

Definition wasmcert_i64_rotr (x y : I64.int) : I64.int :=
  let n := I64.unsigned y mod 64 in
  I64.repr (Z.lor (Z.shiftr (I64.unsigned x) n)
                  (Z.shiftl (I64.unsigned x) (64 - n))).
