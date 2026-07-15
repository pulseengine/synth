(** * VCR-WASM-001 — WasmCert-Coq source-semantics reference (BOUNDED first increment)

    GOAL (epic #242, VCR-WASM-001, roadmap Track B). WasmSemantics.v is a
    HAND-WRITTEN stack-machine model: every source-side correctness statement
    in this suite is "consistent with our own model" — a modeling bug in
    [exec_wasm_instr] is invisible to the proofs. VCR-WASM-001 wants the WASM
    source semantics ANCHORED on an INDEPENDENTLY derived reference:
    WasmCert-Coq (Watt et al., FM'21), the community-standard mechanized
    WebAssembly 1.0 semantics. This mirrors, on the WASM side, what
    VCR-ISA-001 (#667 / SailArmBridge.v) does on the ARM/selector side:
    "anchor/generate, don't mirror".

    WHAT THIS FILE IS. Per the SailArmBridge.v spike precedent, importing the
    external Rocq model WHOLESALE into synth's hermetic bazel/nix proof
    toolchain is a no-go at this stage: WasmCert-Coq drags in mathcomp +
    CompCert's Integers library as coq dependencies. So — exactly as
    SailArmBridge transcribes the Sail [execute] clause BY HAND with line-level
    provenance — this file TRANSCRIBES WasmCert-Coq's operational rule for ONE
    total op (i32.add) into synth's own [I32] value primitives, with a verbatim
    provenance citation to the WasmCert-Coq / CompCert source.

    *** TRANSCRIPTION — to be replaced by a real external dependency. ***
    This is a hand transcription, NOT the real WasmCert-Coq dependency. It is
    the bounded-first-increment scaffolding that establishes the refinement
    PATTERN for one op. Wiring the actual WasmCert-Coq/CompCert coq deps into
    the hermetic toolchain, and extending to the full integer/control-flow
    fragment, is the named follow-up (VCR-WASM-001 continuation).

    PROVENANCE. The rule below is transcribed from:

      - WasmCert/WasmCert-Coq @ master, theories/numerics.v:
          Definition i32 : Type := Wasm_int.Int32.T.
          (* within Wasm_int.Make, the Tmixin record: *)  int_add := iadd ;
          Definition iadd : T -> T -> T := add.          (* aliases CompCert add *)
        i.e. WasmCert's i32.add IS CompCert's Integers.Int.add.

      - AbsInt/CompCert @ master, lib/Integers.v (Module Int):
          Definition add (x y: int) : int := repr (unsigned x + unsigned y).
          Definition unsigned (n: int) : Z := intval n.
          Definition repr (x: Z) : int := mkint (Z_mod_modulus x) _.

    The salient, deliberately-preserved feature of the reference is that
    CompCert (hence WasmCert) NORMALIZES each operand with [unsigned] BEFORE
    adding, then [repr]s the sum. Synth's [I32.add x y := repr (x + y)] adds
    RAW representatives (its [int := Z] is unnormalized). The two are equal
    mod 2^32 but DEFINITIONALLY DIFFERENT — so the bridge lemma in
    WasmCertBridge.v is a genuine proof (not [reflexivity]), and it exercises
    the raw-vs-normalized gap.

    NON-VACUITY. [wasmcert_i32_add] is phrased ONLY in the value-encoding
    primitives [I32.repr] / [I32.unsigned] / [Z] — it never mentions
    [I32.add] or [exec_wasm_instr]. So the bridge lemma is not synth agreeing
    with a copy of itself. A WRONG synth semantics for i32.add (e.g. if
    [exec_wasm_instr I32Add] computed [I32.sub] or [I32.mul]) would FAIL to
    satisfy the bridge theorem: the reference pins the OPERATION (addition mod
    2^32), not merely the shape.
*)

From Stdlib Require Import ZArith.
Require Import Synth.Common.Base.
Require Import Synth.Common.Integers.

Open Scope Z_scope.

(** ** WasmCert-Coq reference rule for i32.add

    Transcription of [Wasm_int.Int32.int_add] = CompCert [Int.add]:
      [repr (unsigned x + unsigned y)].

    Stated in synth's [I32] primitives. NOTE the [I32.unsigned] on each
    operand — this is the CompCert/WasmCert normalize-then-add form, and is
    what distinguishes this reference from synth's raw [I32.add x y :=
    repr (x + y)]. *)
Definition wasmcert_i32_add (x y : I32.int) : I32.int :=
  I32.repr (I32.unsigned x + I32.unsigned y).
