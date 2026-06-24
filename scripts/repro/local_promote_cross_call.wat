;; VCR-RA local-promotion with-call scenario (#390, epic #242).
;;
;; The exported `cross_call` holds an i32 local `acc` LIVE ACROSS a call to
;; `$helper`. `acc` is write-before-read, all accesses at control-flow depth 0,
;; i32, >=2 accesses — i.e. it satisfies every v1 promotion predicate EXCEPT the
;; LEAF-ONLY gate, which declines it because the function contains a `call`.
;;
;; Purpose: the artifact the leaf-only LIFT will need. Today (leaf-only ON)
;; promotion declines this function, so flag-on == flag-off == the frame path —
;; `acc` lives in a frame slot and survives the call trivially. When the gate is
;; lifted, `acc` is promoted to a callee-saved register (r4..r8) which survives
;; the `bl` by AAPCS; the range-reallocator pins it across the call boundary
;; (proven in isolation by reallocate_function_preserves_callee_saved_value_across_call,
;; PR #459). This fixture is what closes that proof end-to-end.
;;
;; `acc` is read AFTER the call result is combined, so a promotion that placed it
;; in a caller-saved register (the bug the leaf-only gate guards against) would see
;; it clobbered by the `bl` and produce a wrong result.
(module
  (func $helper (param i32) (result i32)
    ;; AAPCS-clobbers caller-saved r0..r3 per the call; doubles its arg.
    (i32.mul (local.get 0) (i32.const 2)))

  (func (export "cross_call") (param i32) (result i32)
    (local i32) ;; local 1 = acc
    ;; acc = p0 + 100  (write before any read; depth 0)
    (local.set 1 (i32.add (local.get 0) (i32.const 100)))
    ;; acc = acc + helper(p0)  — acc is LIVE ACROSS the call to $helper
    (local.set 1 (i32.add (local.get 1) (call $helper (local.get 0))))
    ;; result = acc ^ p0
    (i32.xor (local.get 1) (local.get 0))))
