;; #665 — WASM `unreachable` MUST trap (WASM Core §4.4.5).
;;
;; synth compiled `unreachable` to a NO-OP on every backend: the decoder
;; dropped it as "intentionally ignorable" (wasm_decoder.rs), so control fell
;; through panic!/abort/exhaustiveness guards and returned undefined register
;; state. The selector trap arms (ARM: UDF #0, RV32: ebreak) existed but never
;; received the op.
;;
;; - boom:    body is just `unreachable` — must trap on entry (issue repro 1).
;; - guarded: error-guard shape — `unreachable` only on the negative branch
;;   (issue repro 2). guarded(-5) must trap; guarded(5) must return 1
;;   (NON-VACUITY: the trap instruction must not break the normal path).
;; - guarded_br: same guard desugared as block + br_if (the shape front-ends
;;   emit), exercising `unreachable` in straight-line dead-end position.
(module
  (func (export "boom") (param i32 i32) (result i32)
    unreachable)
  (func (export "guarded") (param i32) (result i32)
    (if (result i32) (i32.ge_s (local.get 0) (i32.const 0))
      (then (i32.const 1))
      (else (unreachable))))
  (func (export "guarded_br") (param i32) (result i32)
    (block
      (br_if 0 (i32.ge_s (local.get 0) (i32.const 0)))
      (unreachable))
    (i32.const 1)))
