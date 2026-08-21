;; RQ-59-SUBTRACT (#242, VCR-SEL-001 increment 6): the sign-extension family.
;;
;; The v0.58 688-row corpus had ZERO coverage of i32.extend8_s/16_s and
;; i64.extend8/16/32_s — the byte-identity manifest could not discriminate
;; a change to exactly the arms increment 6 deletes. This fixture closes
;; that hole: every converted arm fires here, on both selector paths
;; (relocatable/direct and self-contained), with results that flow onward
;; (not dead) so the emission cannot be elided.
;;
;; Also exercises i32.wrap_i64 + i64.extend_i32_s mid-expression, the two
;; width conversions whose select_default hand-written constructions are
;; delegated to their existing increment-5 rules in the same lane.
(module
  ;; i32.extend8_s / i32.extend16_s on a param, combined so both results live
  (func (export "sx32") (param i32) (result i32)
    (i32.add
      (i32.extend8_s (local.get 0))
      (i32.extend16_s (i32.mul (local.get 0) (i32.const 3)))))

  ;; i64.extend8_s: narrow sign-extend an i64 mid-expression
  (func (export "sx64_8") (param i64) (result i64)
    (i64.add (i64.extend8_s (local.get 0)) (i64.const 1)))

  ;; i64.extend16_s
  (func (export "sx64_16") (param i64) (result i64)
    (i64.sub (i64.extend16_s (local.get 0)) (i64.const 1)))

  ;; i64.extend32_s, fed by a wrap/extend round trip so i32.wrap_i64 and
  ;; i64.extend_i32_s fire in the same stream
  (func (export "sx64_32") (param i64) (result i64)
    (i64.add
      (i64.extend32_s (local.get 0))
      (i64.extend_i32_s (i32.wrap_i64 (local.get 0)))))

  ;; all three narrow i64 forms chained, exercising pair-temp allocation
  (func (export "sx64_chain") (param i64) (result i64)
    (i64.extend8_s (i64.extend16_s (i64.extend32_s (local.get 0)))))
)
