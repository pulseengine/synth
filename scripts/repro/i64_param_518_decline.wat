;; #518 — historically the DECLINE half of the fix. Every register-resident
;; i64-param case is now LOWERED and executes correctly; this fixture is kept as
;; the non-vacuity + AAPCS-matrix guard (all three functions emit + run):
;;   - d_call: a REGISTER-resident i64 param in a function that CONTAINS A
;;     CALL — params are frame-backed to survive the call's caller-saved
;;     clobber. #518 declined it because that param_slots path sized an i64
;;     param's slot from a width set (`i64_set`) that EXCLUDES params, dropping
;;     the high half. #837 sizes it from the DECLARED AAPCS width, so the pair
;;     is homed into the frame (`I64Str`) and reloaded after the call (`I64Ldr`):
;;     now emitted + executes correctly (d_call(p) = p + 7). The fuller gale
;;     gust:os/timer shape (mmio import + in-module call) is exercised by
;;     framebacking_i64param_837_differential.py.
;;   - d_past_r3 (an i64 param AAPCS-passed PAST R3, on the caller's stack)
;;     was the #503-i64 stack-param case and is LOWERED (width-aware
;;     `aapcs_param_layout` incoming homing): emitted + executes correctly,
;;     gated below and by i64_stack_param_503_differential.py.
;; d_leaf is the control: a leaf register-resident i64 param IS emitted.
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
