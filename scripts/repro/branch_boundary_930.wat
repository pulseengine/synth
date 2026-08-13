(module
  ;; #930 — labels.wast `br_if2`: a `br_if` exiting an enclosing block FROM
  ;; INSIDE an `if`, whose value operand is itself a block that branches.
  ;; Pre-fix, the inner block's `End` was misattributed to the enclosing `if`
  ;; (the selector tested `if_labels` alone), so `.Lblock_end_N` was never
  ;; emitted and its `b` encoded as a `b #0` placeholder landing on the second
  ;; halfword of the following 32-bit `movw` — the br_if condition register
  ;; was never written and the branch silently fell through.
  (func (export "brif2") (result i32)
    (block $l0 (result i32)
      (if (i32.const 1)
        (then
          (drop
            (br_if $l0
              (block $l1 (result i32) (br $l1 (i32.const 1)))
              (i32.const 1)))))
      (i32.const 0)))

  ;; #930 — labels.wast `br`: the plain-`br` form of the same shape.
  (func (export "br") (result i32)
    (block $l0 (result i32)
      (if (i32.const 1)
        (then (br $l0 (block $l1 (result i32) (br $l1 (i32.const 1)))))
        (else (block (drop (block $l1 (result i32) (br $l1 (i32.const 1)))))))
      (i32.const 1)))

  ;; The if-condition as a parameter: exercises BOTH edges of the enclosing
  ;; `if`. The pre-fix miscompile also mis-placed the if's ELSE label at the
  ;; inner block's position (a boundary-valid but semantically wrong target),
  ;; so the condition-false path read an uninitialised register — invisible to
  ;; the const-1 shape above and to the boundary invariant alone.
  (func (export "brif2p") (param i32) (result i32)
    (block $l0 (result i32)
      (if (local.get 0)
        (then
          (drop
            (br_if $l0
              (block $l1 (result i32) (br $l1 (i32.const 1)))
              (i32.const 1)))))
      (i32.const 0)))

  ;; The br_if-condition as a parameter: both edges of the br_if itself
  ;; (taken -> block-value 1, not-taken -> fallthrough 0).
  (func (export "brifc") (param i32) (result i32)
    (block $l0 (result i32)
      (if (i32.const 1)
        (then
          (drop
            (br_if $l0
              (block $l1 (result i32) (br $l1 (i32.const 1)))
              (local.get 0)))))
      (i32.const 0))))
