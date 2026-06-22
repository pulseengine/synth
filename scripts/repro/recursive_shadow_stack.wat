;; VCR-MEM-001 layer-2 honest-fail fixture (#242, #383).
;;
;; A function that recurses THROUGH the shadow stack: each activation decrements
;; the stack-pointer global by a 16-byte frame before calling itself, so the
;; worst-case shadow-stack depth grows without bound. This is the case the
;; layer-2 budget derivation MUST refuse — deriving any finite budget for an
;; unbounded stack would silently under-reserve and overflow on silicon.
;;
;; scry classifies this exactly: sp_global identified, function recursive,
;; max_stack_bytes = Unbounded. The test
;; `layer2_unbounded_recursion_refuses_proven_budget_242` asserts that scry
;; behaviour AND that `budget_from_bound` never returns a ProvenStackDepth for
;; it — only the asserted fallback (if given) or an honest refuse.
(module
  (global $sp (mut i32) (i32.const 65536))
  (memory 1)
  (func $recurse (param $n i32)
    ;; allocate a 16-byte shadow-stack frame
    (global.set $sp (i32.sub (global.get $sp) (i32.const 16)))
    (if (local.get $n)
      (then (call $recurse (i32.sub (local.get $n) (i32.const 1)))))
    ;; free the frame
    (global.set $sp (i32.add (global.get $sp) (i32.const 16))))
  (func (export "run") (call $recurse (i32.const 10))))
