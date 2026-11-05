;; #1639 / #1641 — A32 control-flow fixture. Every export takes two i32 params
;; and returns i32 so one harness drives all of them. Each function exercises a
;; distinct branch shape; see a32_control_flow_1639_differential.py.
(module
  ;; block + br_if forward (the #1639 minimal reproducer)
  (func $f (export "f") (param i32 i32) (result i32)
    (block
      (br_if 0 (local.get 0))
      (return (i32.const 0xdead)))
    (i32.const 5))
  ;; loop back-edge (br 0) with a br_if 1 exit
  (func $sum (export "sum") (param i32 i32) (result i32) (local i32)
    (block
      (loop
        (br_if 1 (i32.eqz (local.get 0)))
        (local.set 2 (i32.add (local.get 2) (local.get 0)))
        (local.set 0 (i32.sub (local.get 0) (i32.const 1)))
        (br 0)))
    (local.get 2))
  ;; br_table over three targets plus default
  (func $tbl (export "tbl") (param i32 i32) (result i32)
    (block (block (block
      (br_table 0 1 2 (local.get 0)))
      (return (i32.const 10)))
     (return (i32.const 20)))
    (i32.const 30))
  ;; if / else
  (func $ife (export "ife") (param i32 i32) (result i32) (local i32)
    (if (local.get 0)
      (then (local.set 2 (i32.mul (local.get 0) (i32.const 3))))
      (else (local.set 2 (i32.const 77))))
    (i32.add (local.get 2) (i32.const 1)))
  ;; nested loops: sum over i < a, j < b of (i xor j), bottom-tested back-edges
  (func $nest (export "nest") (param i32 i32) (result i32) (local i32 i32 i32)
    (local.set 2 (i32.const 0))
    (block $done
      (loop $outer
        (br_if $done (i32.ge_u (local.get 2) (local.get 0)))
        (local.set 3 (i32.const 0))
        (block $idone
          (loop $inner
            (br_if $idone (i32.ge_u (local.get 3) (local.get 1)))
            (local.set 4 (i32.add (local.get 4) (i32.xor (local.get 2) (local.get 3))))
            (local.set 3 (i32.add (local.get 3) (i32.const 1)))
            (br_if $inner (i32.lt_u (local.get 3) (local.get 1)))))
        (local.set 2 (i32.add (local.get 2) (i32.const 1)))
        (br $outer)))
    (local.get 4))
  ;; helper called from inside a loop
  (func $sq (param i32) (result i32)
    (i32.add (i32.mul (local.get 0) (local.get 0)) (i32.const 1)))
  (func $callsum (export "callsum") (param i32 i32) (result i32) (local i32)
    (block
      (loop
        (br_if 1 (i32.eqz (local.get 0)))
        (local.set 2 (i32.add (local.get 2) (call $sq (local.get 0))))
        (local.set 0 (i32.sub (local.get 0) (i32.const 1)))
        (br 0)))
    (local.get 2))
  ;; do-while: the only back-edge is a conditional br_if to the loop head
  (func $dowhile (export "dowhile") (param i32 i32) (result i32) (local i32)
    (loop $l
      (local.set 2 (i32.add (local.get 2) (i32.const 3)))
      (local.set 0 (i32.sub (local.get 0) (i32.const 1)))
      (br_if $l (i32.gt_s (local.get 0) (i32.const 0))))
    (local.get 2))
  ;; a value-carrying block and a select in the same function
  (func $blkval (export "blkval") (param i32 i32) (result i32)
    (i32.add
      (block (result i32)
        (br_if 0 (i32.const 100) (i32.gt_u (local.get 0) (local.get 1)))
        (drop)
        (i32.const 200))
      (select (local.get 0) (local.get 1) (i32.and (local.get 0) (i32.const 1)))))
  ;; params-only loop and br_if: shapes the OPTIMIZED path (optimizer_bridge,
  ;; numeric Thumb-unit branches) accepts on a non-relocatable build
  (func $optloop (export "optloop") (param i32 i32) (result i32) (local i32)
    (local.set 2 (local.get 0))
    (block
      (loop
        (br_if 1 (i32.eqz (local.get 2)))
        (local.set 2 (i32.sub (local.get 2) (i32.const 1)))
        (br 0)))
    (i32.add (local.get 2) (local.get 1)))
  (func $optif (export "optif") (param i32 i32) (result i32) (local i32)
    (local.set 2 (local.get 1))
    (block
      (br_if 0 (i32.lt_u (local.get 0) (local.get 1)))
      (local.set 2 (i32.sub (local.get 0) (local.get 1))))
    (i32.add (local.get 2) (i32.const 9)))
  ;; the div/rem trap guards (numeric Thumb-unit branches in the selector)
  (func $du (export "du") (param i32 i32) (result i32) (i32.div_u (local.get 0) (local.get 1)))
  (func $ds (export "ds") (param i32 i32) (result i32) (i32.div_s (local.get 0) (local.get 1)))
  (func $ru (export "ru") (param i32 i32) (result i32) (i32.rem_u (local.get 0) (local.get 1)))
  (func $rs (export "rs") (param i32 i32) (result i32) (i32.rem_s (local.get 0) (local.get 1)))
)
