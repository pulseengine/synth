;; #554 — `-b aarch64` must REJECT an UNSUPPORTED float op honestly, not silently
;; miscompile it. m3 (#787) landed the non-trapping scalar floats and m4 (#538)
;; landed the domain-guarded trapping truncations + min/max + copysign, so the
;; honesty test moves to a float op that DELIBERATELY stays declined: `f64.floor`
;; (rounding). It is DECODED (the ARM32 m7dp backend lowers it), so it reaches
;; the aarch64 SELECTOR, which must loud-decline (`unsupported wasm op`) — the
;; strongest form of the honesty check. `i32add` is the control: a supported op
;; that must still compile.
(module
  (func (export "f64floor") (param f64) (result f64)
    (f64.floor (local.get 0)))
  (func (export "i32add") (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1))))
