;; #554 — `-b aarch64` must REJECT an UNSUPPORTED float op honestly, not silently
;; miscompile it. m3 (#787) landed the non-trapping scalar floats (add/sub/mul/…),
;; so the honesty test moves to a float op that DELIBERATELY stays declined:
;; `i32.trunc_f32_s`. A64 FCVTZS SATURATES where WASM TRAPS (the #709
;; more-total-than-WASM soundness class), so lowering it would be a silent wrong
;; result — the backend must loud-decline instead. `i32add` is the control: a
;; supported op that must still compile.
(module
  (func (export "f32trunc") (param f32) (result i32)
    (i32.trunc_f32_s (local.get 0)))
  (func (export "i32add") (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1))))
