;; Control flow tests - Phase 3c: loop with backward branches
;; These test basic loop constructs with br_if

(module
  ;; Simple countdown loop
  ;; Counts down from param to 0, returns 0
  ;; This tests:
  ;; - loop instruction (label at start for backward branch)
  ;; - local.tee (store and keep value on stack)
  ;; - br_if (conditional backward branch)
  ;; - i32.gt_s comparison
  (func (export "countdown") (param i32) (result i32)
    (local i32)                    ;; local 1: accumulator
    local.get 0                    ;; init accumulator to param
    local.set 1
    loop (result i32)
      local.get 1                  ;; get current value
      i32.const 1
      i32.sub                      ;; decrement
      local.tee 1                  ;; save and keep on stack
      local.get 1
      i32.const 0
      i32.gt_s                     ;; if > 0
      br_if 0                      ;; continue loop (backward branch to loop start)
    end)                           ;; return final value (0)

  ;; Sum from 1 to N using a loop
  ;; sum = 0; while (n > 0) { sum += n; n--; } return sum;
  (func (export "sum_to_n") (param i32) (result i32)
    (local i32)                    ;; local 1: sum
    i32.const 0
    local.set 1                    ;; sum = 0
    loop (result i32)
      ;; sum += n
      local.get 1
      local.get 0
      i32.add
      local.set 1
      ;; n--
      local.get 0
      i32.const 1
      i32.sub
      local.tee 0                  ;; n = n - 1
      ;; if n > 0, continue
      i32.const 0
      i32.gt_s
      br_if 0
      ;; return sum
      local.get 1
    end)

  ;; Simple counter - counts iterations
  ;; Returns number of iterations to count down from n to 0
  (func (export "count_iters") (param i32) (result i32)
    (local i32)                    ;; local 1: iteration count
    i32.const 0
    local.set 1                    ;; count = 0
    loop (result i32)
      ;; count++
      local.get 1
      i32.const 1
      i32.add
      local.set 1
      ;; n--
      local.get 0
      i32.const 1
      i32.sub
      local.tee 0
      ;; if n > 0, continue
      i32.const 0
      i32.gt_s
      br_if 0
      ;; return count
      local.get 1
    end)
)

;; Countdown tests - should all return 0
(assert_return (invoke "countdown" (i32.const 1)) (i32.const 0))
(assert_return (invoke "countdown" (i32.const 5)) (i32.const 0))
(assert_return (invoke "countdown" (i32.const 10)) (i32.const 0))
(assert_return (invoke "countdown" (i32.const 0)) (i32.const -1))  ;; Edge case: 0-1 = -1, no loop

;; Sum tests
;; sum(1) = 1
;; sum(5) = 1+2+3+4+5 = 15
;; sum(10) = 1+2+...+10 = 55
(assert_return (invoke "sum_to_n" (i32.const 1)) (i32.const 1))
(assert_return (invoke "sum_to_n" (i32.const 5)) (i32.const 15))
(assert_return (invoke "sum_to_n" (i32.const 10)) (i32.const 55))

;; Count iterations tests
(assert_return (invoke "count_iters" (i32.const 1)) (i32.const 1))
(assert_return (invoke "count_iters" (i32.const 5)) (i32.const 5))
(assert_return (invoke "count_iters" (i32.const 10)) (i32.const 10))
