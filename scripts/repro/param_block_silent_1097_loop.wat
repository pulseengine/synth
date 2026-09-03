;; #1097 — silent-miscompile shape 3: `loop (param i32)` + conditional
;; back-edge. The accumulator (starting at 7) is the loop PARAMETER, carried
;; around the back-edge; each iteration adds 1 while $n counts down.
;; wasmtime: lpb(0) = 8, lpb(1) = 8, lpb(3) = 10 (the loop body always runs
;; once; $n goes negative on lpb(0) and the signed guard exits).
(module
  (func (export "lpb") (param i32) (result i32)
    (local $n i32)
    (local.set $n (local.get 0))
    (i32.const 7)
    (loop $l (param i32) (result i32)
      (i32.const 1)
      (i32.add)
      (local.set $n (i32.sub (local.get $n) (i32.const 1)))
      (br_if $l (i32.gt_s (local.get $n) (i32.const 0))))))
