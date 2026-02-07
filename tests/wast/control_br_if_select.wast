;; Control flow tests - br_if block to branchless select
;; Tests transformation of br_if early exit patterns to select instructions
;;
;; Pattern:
;;   block (result i32)
;;     val1
;;     cond
;;     br_if 0       ;; if cond, return val1
;;     drop
;;     val2          ;; else return val2
;;   end
;;
;; Becomes:
;;   select(val1, val2, cond)

(module
  ;; Basic br_if early exit pattern
  ;; Returns val1 if condition is true, else val2
  (func (export "br_if_select") (param i32) (result i32)
    block (result i32)
      i32.const 10     ;; val1 (early exit value)
      local.get 0      ;; condition
      br_if 0          ;; if cond, exit with val1
      drop             ;; drop val1
      i32.const 20     ;; val2 (fallthrough value)
    end)

  ;; br_if with local.get values
  (func (export "br_if_locals") (param i32 i32 i32) (result i32)
    block (result i32)
      local.get 1      ;; val1 (param 1)
      local.get 0      ;; condition (param 0)
      br_if 0          ;; if cond, return val1
      drop
      local.get 2      ;; val2 (param 2)
    end)

  ;; Early exit with comparison condition
  ;; Returns 100 if x > 0, else 0
  (func (export "br_if_compare") (param i32) (result i32)
    block (result i32)
      i32.const 100    ;; positive case value
      local.get 0
      i32.const 0
      i32.gt_s         ;; x > 0
      br_if 0          ;; if true, return 100
      drop
      i32.const 0      ;; non-positive case
    end)

  ;; Multiple sequential br_if blocks (each can be optimized separately)
  (func (export "sequential_br_if") (param i32 i32) (result i32)
    (local i32)  ;; local 2 for intermediate result

    ;; First block: check param 0
    block (result i32)
      i32.const 1      ;; val if p0 true
      local.get 0      ;; condition p0
      br_if 0
      drop
      i32.const 0      ;; val if p0 false
    end
    local.set 2        ;; store intermediate

    ;; Second block: combine with param 1
    block (result i32)
      local.get 2      ;; use intermediate
      local.get 1      ;; condition p1
      br_if 0
      drop
      i32.const 99     ;; fallback if p1 false
    end)

  ;; Equivalent to: cond ? val1 : val2 using explicit select
  ;; This is the expected output pattern
  (func (export "expected_select") (param i32) (result i32)
    i32.const 10       ;; val1
    i32.const 20       ;; val2
    local.get 0        ;; condition
    select)
)

;; br_if_select tests - basic pattern
(assert_return (invoke "br_if_select" (i32.const 1)) (i32.const 10))
(assert_return (invoke "br_if_select" (i32.const 0)) (i32.const 20))
(assert_return (invoke "br_if_select" (i32.const 42)) (i32.const 10))
(assert_return (invoke "br_if_select" (i32.const -1)) (i32.const 10))

;; br_if_locals tests - values from parameters
(assert_return (invoke "br_if_locals" (i32.const 1) (i32.const 100) (i32.const 200)) (i32.const 100))
(assert_return (invoke "br_if_locals" (i32.const 0) (i32.const 100) (i32.const 200)) (i32.const 200))

;; br_if_compare tests - with comparison
(assert_return (invoke "br_if_compare" (i32.const 5)) (i32.const 100))
(assert_return (invoke "br_if_compare" (i32.const 1)) (i32.const 100))
(assert_return (invoke "br_if_compare" (i32.const 0)) (i32.const 0))
(assert_return (invoke "br_if_compare" (i32.const -1)) (i32.const 0))
(assert_return (invoke "br_if_compare" (i32.const -100)) (i32.const 0))

;; sequential_br_if tests - two blocks in sequence
(assert_return (invoke "sequential_br_if" (i32.const 1) (i32.const 1)) (i32.const 1))
(assert_return (invoke "sequential_br_if" (i32.const 1) (i32.const 0)) (i32.const 99))
(assert_return (invoke "sequential_br_if" (i32.const 0) (i32.const 1)) (i32.const 0))
(assert_return (invoke "sequential_br_if" (i32.const 0) (i32.const 0)) (i32.const 99))

;; expected_select tests - verify select behavior matches br_if pattern
(assert_return (invoke "expected_select" (i32.const 1)) (i32.const 10))
(assert_return (invoke "expected_select" (i32.const 0)) (i32.const 20))
(assert_return (invoke "expected_select" (i32.const 42)) (i32.const 10))
