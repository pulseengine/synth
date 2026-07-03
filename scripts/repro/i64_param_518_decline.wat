;; #518 — the DECLINE half of the fix, minus what #503-i64 closed. The leaf,
;; register-resident i64-param cases are lowered correctly (see
;; i64_param_518.wat); the REMAINING sub-case is declined LOUDLY (a
;; `warning: skipping function …` + absence from the symbol table) rather than
;; silently miscompiled, because its correct lowering is a tracked follow-up:
;;   - d_call: a REGISTER-resident i64 param in a function that CONTAINS A
;;     CALL — params are frame-backed to survive the call's caller-saved
;;     clobber, and that param_slots path sizes an i64 param's slot from a
;;     width set that excludes params, dropping the high half. Declined until
;;     the frame-backed i64 path lands.
;;   - d_past_r3 (an i64 param AAPCS-passed PAST R3, on the caller's stack)
;;     was the #503-i64 stack-param case and is now LOWERED (width-aware
;;     `aapcs_param_layout` incoming homing): emitted + executes correctly,
;;     gated below and by i64_stack_param_503_differential.py.
;; d_leaf is the control: a leaf register-resident i64 param IS emitted (proves
;; the decline is specific to d_call, not a blanket i64-param refusal).
(module
  (func $helper (param i32) (result i32) (local.get 0))

  ;; i64 param past R3 (R0,R1,R2 = the three i32s; the even-aligned pair does
  ;; not fit -> caller stack @ nsaa 0) -> LOWERED as of #503-i64
  (func (export "d_past_r3") (param i32 i32 i32 i64) (result i64)
    (i64.add (local.get 3) (i64.const 1)))

  ;; REGISTER-resident i64 param + a call -> frame-backed -> decline
  (func (export "d_call") (param i64) (result i64)
    (i64.add
      (local.get 0)
      (i64.extend_i32_u (call $helper (i32.const 7)))))

  ;; control: leaf i64 param in R0:R1 -> emitted correctly
  (func (export "d_leaf") (param i64) (result i64)
    (i64.add (local.get 0) (i64.const 3))))
