;; #1189 — the i64 PAIR form of the join-register/home alias. An i64 param is
;; homed in R0:R1 on the ARM direct selector; the then-arm's `local.get 0`
;; pushes that pair uncopied, so the #313 join moves BOTH halves into the
;; local (`mov r0, r3; mov r1, r4` on main). Its own module because the RV32
;; selector declines an i64 PARAM outright (#312) and #952 fails a whole
;; `--all-exports` compile on one skipped export.
(module
  (func (export "i64p") (param i64) (result i64)
    (if (result i64) (i32.wrap_i64 (local.get 0)) (then (local.get 0)) (else (i64.const 9)))
    (local.get 0) i64.add))
