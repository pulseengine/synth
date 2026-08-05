;; #554 — `-b aarch64` must REJECT an UNSUPPORTED float construct honestly, not
;; silently miscompile it. The honesty target has MOVED as the surface closed:
;; m3 (#787) landed the non-trapping scalar floats, m4 (#538) the domain-guarded
;; trapping i32 truncations + min/max + copysign, and v0.54 L2 (#851) the last
;; four scalar-float classes (rounding, f32/f64 load/store, i64->float converts,
;; trapping i64-target truncations). With the SCALAR float surface complete, the
;; test now targets a float construct that DELIBERATELY stays declined: a
;; VALUE-CARRYING (f32-result) `block`.
;;
;; It is fully DECODED — no upstream drop masks it — so it reaches the aarch64
;; SELECTOR, which must loud-decline (a value-carrying block needs result-
;; register reconciliation across the branch). That is the strongest form of the
;; honesty check. `i32add` is the control: a supported op that must still
;; compile.
(module
  (func (export "f32block") (param f32) (result f32)
    (block (result f32) (local.get 0)))
  (func (export "i32add") (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1))))
