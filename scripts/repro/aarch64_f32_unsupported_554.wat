;; #554 — `-b aarch64` must REJECT an UNSUPPORTED float construct honestly, not
;; silently miscompile it. The honesty target has MOVED as the surface closed:
;; m3 (#787) landed the non-trapping scalar floats, m4 (#538) the domain-guarded
;; trapping i32 truncations + min/max + copysign, v0.54 L2 (#851) the last four
;; scalar-float classes (rounding, f32/f64 load/store, i64->float converts,
;; trapping i64-target truncations), and v0.55 L6 (VCR-A64-CF-001) the
;; VALUE-CARRYING (f32-result) `block` this fixture used to target — that shape
;; now LOWERS (the reconciliation register carries an f32 through `fmov d`) and
;; is execution-verified in aarch64_brtable_blockvals_851_differential.py.
;;
;; The target therefore moves again, to a float construct that DELIBERATELY
;; stays declined: a NON-LEAF function that reads an f32 PARAMETER. Float params
;; arrive in v0..v7, which a `bl` clobbers, so a non-leaf must HOME them to
;; stack slots — and this encoder has no FP store for the v-register file, so
;; the shape loud-declines rather than read a clobbered register.
;;
;; It is fully DECODED — no upstream drop masks it — so it reaches the aarch64
;; SELECTOR, which must loud-decline. That is the strongest form of the honesty
;; check. `i32add` is the control: a supported op that must still compile.
(module
  (func $twice (param f32) (result f32)
    (f32.add (local.get 0) (local.get 0)))
  (func (export "f32nonleaf") (param f32) (result f32)
    (call $twice (local.get 0)))
  (func (export "i32add") (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1))))
