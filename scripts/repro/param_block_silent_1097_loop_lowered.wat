;; RQ-64-MVLOWER (#1093) — sub-shapes of `loop (param ..)`, executed by the
;; #1097 oracle ONLY on a leg listed as LOWERED. One module per construct so
;; a still-declined construct can never block this one (#952). Every expected
;; value comes from wasmtime, live; nothing here is hand-pinned.
(module
  ;; TWO loop params (acc, i) carried around a conditional back-edge; the
  ;; loop yields both, the caller drops i. wasmtime: lp2(n) = n(n+1)/2 for
  ;; n > 0; lp2(0) = 0 (body runs once: acc = 0, i = -1, exit).
  (func (export "lp2") (param i32) (result i32)
    (local $acc i32) (local $i i32)
    (i32.const 0) (local.get 0)
    (loop $l (param i32 i32) (result i32 i32)
      (local.set $i) (local.set $acc)
      (local.set $acc (i32.add (local.get $acc) (local.get $i)))
      (local.set $i (i32.sub (local.get $i) (i32.const 1)))
      (local.get $acc) (local.get $i)
      (br_if $l (i32.gt_s (local.get $i) (i32.const 0))))
    (drop))
  ;; a value BELOW the loop param (100) must survive every back-edge.
  ;; wasmtime: lpd(n) = 100 + lpb(n) = 108 (n <= 1), 109 (2), 110 (3).
  (func (export "lpd") (param i32) (result i32)
    (local $n i32)
    (local.set $n (local.get 0))
    (i32.const 100) (i32.const 7)
    (loop $l (param i32) (result i32)
      (i32.const 1) (i32.add)
      (local.set $n (i32.sub (local.get $n) (i32.const 1)))
      (br_if $l (i32.gt_s (local.get $n) (i32.const 0))))
    (i32.add))
  ;; an UNCONDITIONAL back-edge (`br $l`) with a forward `br_if` OUT of the
  ;; loop carrying the accumulator to an enclosing `block (param ..)`; the
  ;; loop's fall-through is dead. wasmtime: lpx(n) = 8 (n <= 1), 9 (2), 10 (3).
  (func (export "lpx") (param i32) (result i32)
    (local $n i32)
    (local.set $n (local.get 0))
    (i32.const 7)
    (block $b (param i32) (result i32)
      (loop $l (param i32) (result i32)
        (i32.const 1) (i32.add)
        (local.set $n (i32.sub (local.get $n) (i32.const 1)))
        (br_if $b (i32.le_s (local.get $n) (i32.const 0)))
        (br $l))))
  ;; the loop PARAM is an aliased function-param register (local.get 0 pushes
  ;; r0 by alias): the back-edge must land in a private header register, and
  ;; local 0 must survive for the read after the loop.
  ;; wasmtime: lpa(n) = (n + iterations) + n, iterations = max(n,1):
  ;;   lpa(0) = 1 + 0 = 1 ; lpa(1) = 2 + 1 = 3 ; lpa(3) = 6 + 3 = 9.
  (func (export "lpa") (param i32) (result i32)
    (local $n i32)
    (local.set $n (local.get 0))
    (local.get 0)
    (loop $l (param i32) (result i32)
      (i32.const 1) (i32.add)
      (local.set $n (i32.sub (local.get $n) (i32.const 1)))
      (br_if $l (i32.gt_s (local.get $n) (i32.const 0))))
    (local.get 0) (i32.add)))
