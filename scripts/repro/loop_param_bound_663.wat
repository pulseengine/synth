(module
  ;; #663 — parameter-bounded counting loop: sum of 0..n-1.
  ;; The bound n lives in a param register (r0) and is re-read by the loop
  ;; condition EVERY iteration; linear last-read liveness ended its
  ;; reservation at the first read, so the induction increment was
  ;; allocated into r0 and the loop exited after one iteration.
  (func (export "sum_below") (param i32 i32) (result i32)
    (local $i i32) (local $acc i32)
    (block $d (loop $l
      (br_if $d (i32.ge_s (local.get $i) (local.get 0)))
      (local.set $acc (i32.add (local.get $acc) (local.get $i)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (local.get $acc))

  ;; second param as the bound (param reg r1), first param as a stride —
  ;; both params live across the back-edge.
  (func (export "sum_stride") (param i32 i32) (result i32)
    (local $i i32) (local $acc i32)
    (block $d (loop $l
      (br_if $d (i32.ge_s (local.get $i) (local.get 1)))
      (local.set $acc (i32.add (local.get $acc) (local.get 0)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (local.get $acc))

  ;; nested loops, bound read only in the INNER loop — the OUTER back-edge
  ;; also re-executes the read, so the reservation must extend to the
  ;; outermost enclosing loop end.
  (func (export "sum_nested") (param i32 i32) (result i32)
    (local $i i32) (local $j i32) (local $acc i32)
    (block $do (loop $lo
      (br_if $do (i32.ge_s (local.get $i) (local.get 1)))
      (local.set $j (i32.const 0))
      (block $di (loop $li
        (br_if $di (i32.ge_s (local.get $j) (local.get 0)))
        (local.set $acc (i32.add (local.get $acc) (i32.const 1)))
        (local.set $j (i32.add (local.get $j) (i32.const 1)))
        (br $li)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $lo)))
    (local.get $acc))

  ;; constant-bound control: was already correct pre-fix (pins that the
  ;; loop lowering itself is fine).
  (func (export "sum_const") (param i32 i32) (result i32)
    (local $i i32) (local $acc i32)
    (block $d (loop $l
      (br_if $d (i32.ge_s (local.get $i) (i32.const 10)))
      (local.set $acc (i32.add (local.get $acc) (local.get $i)))
      (local.set $i (i32.add (local.get $i) (i32.const 1)))
      (br $l)))
    (local.get $acc))
)
