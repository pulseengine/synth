;; Control flow tests - Nested loops
;; Tests loop-inside-loop, which exercises two levels of backward branches.
;;
;; Pattern: outer loop iterates b times, inner loop adds 1 to result a times.
;; Result = a * b (multiplication via nested repeated addition).
;;
;; This tests:
;; - loop inside loop (nested backward branch targets)
;; - br_if at depth 0 targeting the enclosing loop at each nesting level
;; - local.set/get across loop boundaries
;; - local.tee for loop counter decrement

(module
  ;; Multiply a * b using nested loops (repeated addition of 1)
  ;; Outer loop: runs b times
  ;; Inner loop: adds 1 to result, a times (so each outer iteration adds a to result)
  ;; Requires: a >= 1, b >= 1 (do-while pattern)
  (func (export "nested_multiply") (param i32 i32) (result i32)
    (local i32 i32)           ;; local 2: result, local 3: inner counter
    i32.const 0
    local.set 2               ;; result = 0
    ;; outer loop
    loop (result i32)
      ;; Reset inner counter to a (param 0)
      local.get 0
      local.set 3
      ;; inner loop: add 1 to result, a times
      loop
        local.get 2
        i32.const 1
        i32.add
        local.set 2           ;; result++
        ;; inner counter--
        local.get 3
        i32.const 1
        i32.sub
        local.tee 3
        i32.const 0
        i32.gt_s
        br_if 0               ;; continue inner loop (depth 0 = inner loop)
      end                     ;; end inner loop
      ;; outer: b--
      local.get 1
      i32.const 1
      i32.sub
      local.tee 1
      i32.const 0
      i32.gt_s
      br_if 0                 ;; continue outer loop (depth 0 = outer loop, inner has ended)
      ;; return result
      local.get 2
    end)                      ;; end outer loop
)

;; nested_multiply tests (a * b via nested loops)
;; 3 * 4 = 12
(assert_return (invoke "nested_multiply" (i32.const 3) (i32.const 4)) (i32.const 12))
;; 5 * 2 = 10
(assert_return (invoke "nested_multiply" (i32.const 5) (i32.const 2)) (i32.const 10))
;; 1 * 1 = 1
(assert_return (invoke "nested_multiply" (i32.const 1) (i32.const 1)) (i32.const 1))
;; 4 * 3 = 12 (commutative check)
(assert_return (invoke "nested_multiply" (i32.const 4) (i32.const 3)) (i32.const 12))
;; 7 * 1 = 7
(assert_return (invoke "nested_multiply" (i32.const 7) (i32.const 1)) (i32.const 7))
;; 1 * 7 = 7
(assert_return (invoke "nested_multiply" (i32.const 1) (i32.const 7)) (i32.const 7))
