;; #782(b) — the falcon "integer popped f32" class, minimized.
;;
;; The 12-function GI-FPU-002 decline class on the real falcon-flight-v1.123
;; fused core (incl. run-stabilization) is NOT register pressure: it is
;;   (a) untyped `select` over two f32/f64 values (falcon's clamp idiom
;;       `(x>k) ? k : x` — run-stabilization op 202, func_50 op 6, ...), and
;;   (b) an EXPLICIT `return` of an f32 result (func_35/42/43/92)
;; — both routed a VFP-resident value into the integer pop, which
;; loud-declined the whole function.
(module
  ;; (a) select over two f32 values — direct AAPCS-VFP params (S0, S1) + i32
  ;; cond (R0), result in S0.
  (func (export "sel32") (param f32 f32 i32) (result f32)
    (select (local.get 0) (local.get 1) (local.get 2)))

  ;; (a) bit-pattern variant: values enter as i32 bits and cross into the VFP
  ;; file via reinterpret (falcon's real dataflow) — exercises NaN payload
  ;; preservation exactly (select PICKS, never computes: strict bit compare).
  (func (export "sel32b") (param i32 i32 i32) (result i32)
    (i32.reinterpret_f32
      (select
        (f32.reinterpret_i32 (local.get 0))
        (f32.reinterpret_i32 (local.get 1))
        (local.get 2))))

  ;; (a) run-stabilization's exact clamp shape: cond computed by an f32
  ;; compare, val1 a const, val2 the live value.
  (func (export "clamp32") (param f32) (result f32)
    (select
      (f32.const 0x1.99999ap-4)  ;; 0.1  (picked when x > 0.1)
      (local.get 0)
      (f32.gt (local.get 0) (f32.const 0x1.99999ap-4))))

  ;; (a) select over two f64 values (D0, D1 + cond R0 -> D0).
  (func (export "sel64") (param f64 f64 i32) (result f64)
    (select (local.get 0) (local.get 1) (local.get 2)))

  ;; (b) explicit `return` of an f32 result from inside a block — previously
  ;; the integer Return pop loud-declined on the Float entry.
  (func (export "ret32") (param f32 i32) (result f32)
    (block
      (br_if 0 (i32.eqz (local.get 1)))
      (return (f32.add (local.get 0) (f32.const 1.0))))
    (f32.const 2.5))

  ;; (b) explicit `return` of an f64 result.
  (func (export "ret64") (param f64 i32) (result f64)
    (block
      (br_if 0 (i32.eqz (local.get 1)))
      (return (f64.add (local.get 0) (f64.const 1.0))))
    (f64.const 2.5))

  ;; (c) i64 select — found adversarially while clearing (a): the narrow
  ;; integer select moved only the LO register and pushed the result as i32,
  ;; silently keeping the WRONG hi half whenever cond == 0. Every target
  ;; (this one is not float-gated; soft-float f64 select rides this path too).
  (func (export "seli64") (param i64 i64 i32) (result i64)
    (select (local.get 0) (local.get 1) (local.get 2))))
