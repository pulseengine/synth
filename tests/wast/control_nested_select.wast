;; Control flow tests - Nested if-else to branchless select
;; Tests transformation of nested if-else patterns to nested select instructions
;;
;; Pattern:
;;   if (outer_cond)
;;     if (inner_cond) val1 else val2
;;   else
;;     val3
;;
;; Becomes:
;;   select(select(val1, val2, inner_cond), val3, outer_cond)

(module
  ;; Nested if-else with simple values
  ;; Returns: val1 if both conds true, val2 if outer true but inner false, val3 if outer false
  (func (export "nested_if_else") (param i32 i32) (result i32)
    local.get 0      ;; outer condition
    if (result i32)
      local.get 1    ;; inner condition
      if (result i32)
        i32.const 10 ;; val1: both conditions true
      else
        i32.const 20 ;; val2: outer true, inner false
      end
    else
      i32.const 30   ;; val3: outer false
    end)

  ;; Another nested pattern with constants as conditions
  (func (export "nested_const_conds") (param i32 i32 i32 i32) (result i32)
    local.get 0      ;; outer condition
    if (result i32)
      local.get 1    ;; inner condition
      if (result i32)
        local.get 2  ;; true-true value
      else
        local.get 3  ;; true-false value
      end
    else
      i32.const 0    ;; false value
    end)

  ;; Triple nested (outer two can be optimized to select chain)
  (func (export "triple_select") (param i32 i32 i32) (result i32)
    local.get 0
    if (result i32)
      local.get 1
      if (result i32)
        local.get 2
        if (result i32)
          i32.const 1  ;; all true
        else
          i32.const 2  ;; outer+mid true, inner false
        end
      else
        i32.const 3    ;; outer true, mid false
      end
    else
      i32.const 4      ;; outer false
    end)
)

;; nested_if_else tests
;; outer=1, inner=1 -> 10
(assert_return (invoke "nested_if_else" (i32.const 1) (i32.const 1)) (i32.const 10))
;; outer=1, inner=0 -> 20
(assert_return (invoke "nested_if_else" (i32.const 1) (i32.const 0)) (i32.const 20))
;; outer=0, inner=1 -> 30 (inner doesn't matter)
(assert_return (invoke "nested_if_else" (i32.const 0) (i32.const 1)) (i32.const 30))
;; outer=0, inner=0 -> 30
(assert_return (invoke "nested_if_else" (i32.const 0) (i32.const 0)) (i32.const 30))

;; nested_const_conds tests - passes through param values
(assert_return (invoke "nested_const_conds" (i32.const 1) (i32.const 1) (i32.const 100) (i32.const 200)) (i32.const 100))
(assert_return (invoke "nested_const_conds" (i32.const 1) (i32.const 0) (i32.const 100) (i32.const 200)) (i32.const 200))
(assert_return (invoke "nested_const_conds" (i32.const 0) (i32.const 1) (i32.const 100) (i32.const 200)) (i32.const 0))
(assert_return (invoke "nested_const_conds" (i32.const 0) (i32.const 0) (i32.const 100) (i32.const 200)) (i32.const 0))

;; triple_select tests
(assert_return (invoke "triple_select" (i32.const 1) (i32.const 1) (i32.const 1)) (i32.const 1))
(assert_return (invoke "triple_select" (i32.const 1) (i32.const 1) (i32.const 0)) (i32.const 2))
(assert_return (invoke "triple_select" (i32.const 1) (i32.const 0) (i32.const 1)) (i32.const 3))
(assert_return (invoke "triple_select" (i32.const 1) (i32.const 0) (i32.const 0)) (i32.const 3))
(assert_return (invoke "triple_select" (i32.const 0) (i32.const 1) (i32.const 1)) (i32.const 4))
(assert_return (invoke "triple_select" (i32.const 0) (i32.const 0) (i32.const 0)) (i32.const 4))
