;; #518 — i64 binop with an i64 PARAM silently miscompiles on BOTH the optimized
;; and the direct (--relocatable/shipped) selectors. An i64 param occupies an
;; AAPCS register PAIR (param 0 = R0:R1), but both selectors treat a param as a
;; single i32-width register: the optimized path never homes the high half
;; (reads unhomed R4:R5 -> param dropped, returns the const); the direct path
;; materializes the const-low into R1, clobbering the param's high half before
;; `adc` reads it. Found by footgun/adversarial differential testing on v0.17.0
;; (flip-independent, pre-existing since >=0.16.0). i32 params are unaffected.
(module
  (func (export "t_add") (param i64) (result i64)
    (i64.add (local.get 0) (i64.const 5)))
  (func (export "t_sub") (param i64) (result i64)
    (i64.sub (local.get 0) (i64.const 5)))
  (func (export "t_or") (param i64) (result i64)
    (i64.or (local.get 0) (i64.const 0x100000007)))
  ;; i64 param NOT at index 0 (after an i32) — exercises pair-shift past a scalar
  (func (export "t_mixed") (param i32 i64) (result i64)
    (i64.add (local.get 1) (i64.extend_i32_u (local.get 0))))
  ;; --- AAPCS i64-param register-assignment matrix (the fix's hardest logic) ---
  ;; TWO i64 params: p0=R0:R1, p1=R2:R3 (consecutive even-aligned pairs). The
  ;; sequential `index_to_reg(i)` mapping puts p1 at R1 (wrong) and computes
  ;; p0.lo+p0.hi instead of p0+p1.
  (func (export "t_ii_add") (param i64 i64) (result i64)
    (i64.add (local.get 0) (local.get 1)))
  ;; i64 then i32: p0=R0:R1, p1=R2 (no even-align padding needed for the i32).
  (func (export "t_i64_i32") (param i64 i32) (result i64)
    (i64.add (local.get 0) (i64.extend_i32_u (local.get 1))))
  ;; read ONLY the SECOND i64 param (p1=R2:R3) + const: sequential mapping reads
  ;; p1 from R1 (wrong) AND the const clobbers R2 (the real p1.lo).
  (func (export "t_snd_i64") (param i64 i64) (result i64)
    (i64.add (local.get 1) (i64.const 9)))
  ;; control: i32 param binop must stay correct
  (func (export "t_i32") (param i32) (result i32)
    (i32.add (local.get 0) (i32.const 5))))
