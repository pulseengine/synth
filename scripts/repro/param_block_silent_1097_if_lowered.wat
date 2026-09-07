;; RQ-64-MVLOWER (#1093) — sub-shapes of `if (param ..)`, executed by the
;; #1097 oracle ONLY on a leg listed as LOWERED. One module per construct so
;; a still-declined construct can never block this one (#952). Every expected
;; value comes from wasmtime, live; nothing here is hand-pinned.
(module
  ;; THE #1093 REPRO: two params, an `else`. Pre-#1096 this PANICKED
  ;; ("`at` split index (is 2) should be <= len (is 1)", exit 101).
  ;; wasmtime: ipe2(nonzero) = 3, ipe2(0) = -1.
  (func (export "ipe2") (param i32) (result i32)
    (i32.const 1) (i32.const 2)
    (if (param i32 i32) (result i32) (local.get 0)
      (then (i32.add))
      (else (i32.sub))))
  ;; a VOID param-taking if with an else: [i32] -> [], both arms consume the
  ;; param. wasmtime: ipv(nonzero) = 7, ipv(0) = 0.
  (func (export "ipv") (param i32) (result i32)
    (local i32)
    (i32.const 7)
    (if (param i32) (local.get 0)
      (then (local.set 1))
      (else (drop)))
    (local.get 1))
  ;; a value BELOW the if params (100) must survive both arms and the join.
  ;; wasmtime: ipb(nonzero) = 149, ipb(0) = 107.
  (func (export "ipb") (param i32) (result i32)
    (i32.const 100) (i32.const 7)
    (if (param i32) (result i32) (local.get 0)
      (then (i32.const 42) (i32.add)))
    (i32.add))
  ;; else-less, the then-arm's result is derived from the param in place.
  ;; wasmtime: ipf(nonzero) = 14, ipf(0) = 7.
  (func (export "ipf") (param i32) (result i32)
    (i32.const 7)
    (if (param i32) (result i32) (local.get 0)
      (then (i32.const 1) (i32.shl))))
  ;; an `if (param ..)` NESTED in a `block (param ..)` (the increment-1 leg):
  ;; the block's param feeds the if's param.
  ;; wasmtime: ipl(nonzero) = 8, ipl(0) = 14.
  (func (export "ipl") (param i32) (result i32)
    (i32.const 7)
    (block (param i32) (result i32)
      (local.get 0)
      (if (param i32) (result i32)
        (then (i32.const 1) (i32.add))
        (else (i32.const 2) (i32.mul)))))
  ;; REGISTER-ALIAS CLOBBER, implicit else (found while lowering, RQ-64):
  ;; `local.get 0` pushes the param's HOME register (r0) by alias, so the
  ;; then-arm's result IS r0. The implicit-else join must not write r0 on
  ;; the false path — local 0 is read after the join.
  ;; wasmtime: ipa(nonzero) = 5+5 = 10 (for 5), ipa(0) = 7 + 0 = 7.
  (func (export "ipa") (param i32) (result i32)
    (i32.const 7)
    (if (param i32) (result i32) (local.get 0)
      (then (drop) (local.get 0)))
    (local.get 0) (i32.add))
  ;; the same clobber through an EXPLICIT else with params.
  ;; wasmtime: ipq(5) = 10, ipq(0) = (7+1) + 0 = 8.
  (func (export "ipq") (param i32) (result i32)
    (i32.const 7)
    (if (param i32) (result i32) (local.get 0)
      (then (drop) (local.get 0))
      (else (i32.const 1) (i32.add)))
    (local.get 0) (i32.add))
  ;; else-less with TWO params and TWO results ([i32 i32] -> [i32 i32]): the
  ;; implicit else passes both through; the join reconciles two positions.
  ;; wasmtime: ipn(nonzero) = 10 - 100 = -90, ipn(0) = 7 - 3 = 4.
  (func (export "ipn") (param i32) (result i32)
    (i32.const 7) (i32.const 3)
    (if (param i32 i32) (result i32 i32) (local.get 0)
      (then (i32.add) (i32.const 100)))
    (i32.sub)))
