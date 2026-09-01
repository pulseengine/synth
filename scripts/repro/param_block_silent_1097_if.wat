;; #1097 — silent-miscompile shape 1: `if (param i32)` WITHOUT an else.
;; The block PARAMETER (7) flows in; the then-arm adds 42. On the false path
;; the implicit else must pass the param through unchanged — wasmtime: ipe(0)
;; = 7, ipe(1) = 49. Pre-#1096 the false path returned a register the
;; then-arm alone had written: exit 0, wrong value.
(module
  (func (export "ipe") (param i32) (result i32)
    (i32.const 7)
    (if (param i32) (result i32) (local.get 0)
      (then (i32.const 42) (i32.add)))))
