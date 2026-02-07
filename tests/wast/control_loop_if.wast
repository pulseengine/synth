;; Control flow tests - Loop with conditional value selection
;; Tests select instruction used inside a loop body for conditional accumulation.
;;
;; This tests:
;; - select instruction (ternary operator) embedded inside a loop body
;; - Combining conditional value selection with loop accumulation
;; - Multiple locals updated per iteration (flag toggling via xor)
;; - i32.xor for boolean flag manipulation

(module
  ;; Alternating sum: counts down from n, adds +1 on odd steps, -1 on even steps
  ;; Uses a flag that alternates each iteration via xor.
  ;; sign_sum(n): sum of (+1, -1, +1, -1, ...) for n iterations
  ;; When n is even: result = 0; when n is odd: result = 1
  ;; Flag starts at 1 (first iteration adds)
  ;;
  ;; Implementation: accumulator starts at 0, flag starts at 1
  ;; Each iteration: accumulator += select(1, -1, flag), flag ^= 1, counter--
  (func (export "sign_sum") (param i32) (result i32)
    (local i32 i32)           ;; local 1: accumulator, local 2: flag (0 or 1)
    i32.const 0
    local.set 1               ;; accumulator = 0
    i32.const 1
    local.set 2               ;; flag = 1 (start by adding)
    loop (result i32)
      ;; Compute selected delta: select(1, -1, flag)
      ;; Puts +1 or -1 on stack depending on flag
      i32.const 1             ;; true value (flag=1 -> add)
      i32.const -1            ;; false value (flag=0 -> subtract)
      local.get 2             ;; condition (flag)
      select                  ;; -> 1 or -1
      ;; accumulator += delta
      local.get 1             ;; current accumulator
      i32.add                 ;; accumulator + delta
      local.set 1             ;; store updated accumulator
      ;; flip flag: flag ^= 1
      local.get 2
      i32.const 1
      i32.xor
      local.set 2
      ;; counter--
      local.get 0
      i32.const 1
      i32.sub
      local.tee 0
      i32.const 0
      i32.gt_s
      br_if 0                 ;; continue loop
      ;; return accumulator
      local.get 1
    end)

  ;; Max of two values using select with comparison
  ;; Directly uses select instead of if-else
  (func (export "max_val") (param i32 i32) (result i32)
    local.get 0               ;; true value (a)
    local.get 1               ;; false value (b)
    local.get 0               ;; first operand for comparison
    local.get 1               ;; second operand for comparison
    i32.gt_s                  ;; a > b?
    select)                   ;; a > b ? a : b
)

;; sign_sum tests
;; sign_sum(1) = 1 (just +1)
(assert_return (invoke "sign_sum" (i32.const 1)) (i32.const 1))
;; sign_sum(2) = 0 (+1, then -1)
(assert_return (invoke "sign_sum" (i32.const 2)) (i32.const 0))
;; sign_sum(3) = 1 (+1 -1 +1)
(assert_return (invoke "sign_sum" (i32.const 3)) (i32.const 1))
;; sign_sum(4) = 0 (+1 -1 +1 -1)
(assert_return (invoke "sign_sum" (i32.const 4)) (i32.const 0))
;; sign_sum(5) = 1
(assert_return (invoke "sign_sum" (i32.const 5)) (i32.const 1))
;; sign_sum(10) = 0
(assert_return (invoke "sign_sum" (i32.const 10)) (i32.const 0))

;; max_val tests
(assert_return (invoke "max_val" (i32.const 5) (i32.const 3)) (i32.const 5))
(assert_return (invoke "max_val" (i32.const 3) (i32.const 5)) (i32.const 5))
(assert_return (invoke "max_val" (i32.const 7) (i32.const 7)) (i32.const 7))
(assert_return (invoke "max_val" (i32.const -1) (i32.const -5)) (i32.const -1))
(assert_return (invoke "max_val" (i32.const 0) (i32.const 1)) (i32.const 1))
