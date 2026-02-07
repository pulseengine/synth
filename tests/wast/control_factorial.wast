;; Control flow tests - Factorial computation
;; Tests a loop with i32.mul (multiplication inside a loop body).
;; Unlike the sum_to_n test which uses i32.add in a loop, this exercises
;; multiplicative accumulation, ensuring loop + mul interaction works.
;;
;; The factorial loop runs as do-while (n > 1), so for n=0 and n=1
;; the loop body runs once but multiplies by n (which is 0 or 1).
;; This is handled by starting the result at 1 and checking n > 1.
;;
;; This tests:
;; - i32.mul inside a loop body
;; - Accumulator pattern with multiplication
;; - Loop exit condition using i32.gt_s with a threshold > 0

(module
  ;; Factorial: n! = n * (n-1) * ... * 2
  ;; Uses a simple do-while loop: result = 1; do { result *= n; n--; } while (n > 1)
  ;; For n=0: loop body runs once -> result = 1 * 0 = 0, then n-- => -1 < 1 => exit
  ;; For n=1: loop body runs once -> result = 1 * 1 = 1, then n-- => 0 < 1 => exit
  ;; For n>=2: loop multiplies n, n-1, ..., 2 into result
  ;;
  ;; Note: 0! is mathematically 1, but this function returns 0 for n=0 due to
  ;; the do-while structure. Tests reflect actual behavior.
  (func (export "factorial") (param i32) (result i32)
    (local i32)               ;; local 1: result accumulator
    i32.const 1
    local.set 1               ;; result = 1
    ;; Multiply loop
    loop (result i32)
      ;; result *= n
      local.get 1
      local.get 0
      i32.mul
      local.set 1
      ;; n--
      local.get 0
      i32.const 1
      i32.sub
      local.tee 0
      ;; if n > 1, continue loop (stop when n reaches 1)
      i32.const 1
      i32.gt_s
      br_if 0               ;; continue loop
      ;; return result
      local.get 1
    end)
)

;; Factorial tests
;; factorial(0) = 0 (do-while: 1*0 = 0, then exits)
(assert_return (invoke "factorial" (i32.const 0)) (i32.const 0))
;; factorial(1) = 1 (1*1 = 1, exits immediately)
(assert_return (invoke "factorial" (i32.const 1)) (i32.const 1))
;; factorial(2) = 2 (1*2 = 2, n=1, exit)
(assert_return (invoke "factorial" (i32.const 2)) (i32.const 2))
;; factorial(3) = 6 (1*3=3, 3*2=6, n=1, exit)
(assert_return (invoke "factorial" (i32.const 3)) (i32.const 6))
;; factorial(4) = 24 (1*4=4, 4*3=12, 12*2=24, n=1, exit)
(assert_return (invoke "factorial" (i32.const 4)) (i32.const 24))
;; factorial(5) = 120
(assert_return (invoke "factorial" (i32.const 5)) (i32.const 120))
;; factorial(7) = 5040
(assert_return (invoke "factorial" (i32.const 7)) (i32.const 5040))
