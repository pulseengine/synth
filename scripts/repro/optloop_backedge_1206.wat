;; #1206 — do-while `br_if` back-edges on the DEFAULT optimized Thumb-2 path.
;;
;; Every function here has a loop whose `br_if` condition is materialized by
;; `SetCond` + `cmp rX, #0`. When the allocator places that SetCond in a HIGH
;; register (R8: R4-R7 busy) the encoder emits `ite; mov.w r8,#1; mov.w r8,#0;
;; cmp.w r8,#0` (14 bytes) where the branch-size estimator assumed 8, so the
;; back-edge landed 6 bytes short — after the increment — and the loop hung.
;; Driven by scripts/repro/optloop_backedge_1206_differential.py.
(module
  (memory 1)
  ;; #1206's own countdown: non-param local set from the param, tee'd first.
  (func (export "countdown") (param i32) (result i32) (local i32)
    local.get 0  local.set 1
    loop (result i32)
      local.get 1  i32.const 1  i32.sub  local.tee 1
      local.get 1  i32.const 0  i32.gt_s
      br_if 0
    end)
  ;; count-up, const bound (the #1206 minimal reproducer `c`).
  (func (export "up_const") (param i32 i32) (result i32) (local i32)
    (local.set 2 (local.get 0))
    (loop $l
      (local.set 2 (i32.add (local.get 2) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get 2) (i32.const 10))))
    (local.get 2))
  ;; count-up, PARAM bound — `do { i++ } while (i < n)` (the g4 shape).
  (func (export "up_param") (param i32 i32) (result i32) (local i32)
    (local.set 2 (local.get 0))
    (loop $l
      (local.set 2 (i32.add (local.get 2) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get 2) (local.get 1))))
    (local.get 2))
  ;; count-down, PARAM bound, signed.
  (func (export "down_param") (param i32 i32) (result i32) (local i32)
    (local.set 2 (local.get 0))
    (loop $l
      (local.set 2 (i32.sub (local.get 2) (i32.const 1)))
      (br_if $l (i32.gt_s (local.get 2) (local.get 1))))
    (local.get 2))
  ;; count-down, const bound, step 3.
  (func (export "down_const") (param i32 i32) (result i32) (local i32)
    (local.set 2 (local.get 0))
    (loop $l
      (local.set 2 (i32.sub (local.get 2) (i32.const 3)))
      (br_if $l (i32.gt_s (local.get 2) (i32.const 0))))
    (local.get 2))
  ;; local initialised from a CONSTANT, param bound.
  (func (export "up_from_zero") (param i32 i32) (result i32) (local i32)
    (local.set 2 (i32.const 0))
    (loop $l
      (local.set 2 (i32.add (local.get 2) (i32.const 1)))
      (br_if $l (i32.lt_u (local.get 2) (local.get 0))))
    (local.get 2))
  ;; a second drift class in the span: `memory.size` is LSR.W rd, r10, #16
  ;; (4 bytes; the estimator had 2) — it lands the back-edge 2 bytes further.
  (func (export "msize_loop") (param i32 i32) (result i32) (local i32)
    (local.set 2 (local.get 0))
    (loop $l
      (local.set 2 (i32.add (local.get 2) (memory.size)))
      (br_if $l (i32.lt_u (local.get 2) (local.get 1))))
    (local.get 2))
  ;; CONTROL: #1206's countdown with a second param — the SetCond lands in R7
  ;; (16-bit forms), so it was correct before the fix too. If this ever hangs
  ;; the harness, not the estimator, is broken.
  (func (export "countdown_r7") (param i32 i32) (result i32) (local i32)
    local.get 0  local.set 2
    loop (result i32)
      local.get 2  i32.const 1  i32.sub  local.tee 2
      local.get 2  i32.const 0  i32.gt_s
      br_if 0
    end)
)
