;; #538 milestone-4 — the aarch64 SOUND-trapping-conversion acceptance module.
;;
;; Every export is a leaf function the m4 A64 selector lowers:
;;   - the TRAPPING float->int truncations (i32.trunc_f32_s/u, i32.trunc_f64_s/u):
;;     A64 FCVTZS/FCVTZU SATURATE where WASM TRAPS (#709), so the m4 lowering
;;     range-guards the operand (fcmp exact WASM boundary + ordered b.cond + brk)
;;     and converts ONLY on the proven-in-range path.
;;   - f32/f64.min/max: A64 FMIN/FMAX = IEEE 754-2019 minimum/maximum, which is
;;     exactly WASM's NaN-propagating, -0<+0 semantics (verified here, not assumed).
;;   - f32/f64.copysign: pure bit surgery through the GP file.
;;   - f32.sqrt: shipped in m3 but absent from the m3 differential's coverage.
;;
;; The differential (aarch64_m4_trunc_minmax_538_differential.py) executes each
;; under unicorn UC_ARCH_ARM64 AND natively on the arm64 host (trap cases in a
;; forked child so the SIGTRAP is observable), and diffs wasmtime ground truth —
;; the full #709 boundary table: every case where WASM traps must TRAP (brk),
;; every in-range case must match bit-exactly.
(module
  ;; ---- trapping float -> int truncations (#709 domain-guarded) ----
  (func (export "i32_trunc_f32_s") (param f32) (result i32)
    (i32.trunc_f32_s (local.get 0)))
  (func (export "i32_trunc_f32_u") (param f32) (result i32)
    (i32.trunc_f32_u (local.get 0)))
  (func (export "i32_trunc_f64_s") (param f64) (result i32)
    (i32.trunc_f64_s (local.get 0)))
  (func (export "i32_trunc_f64_u") (param f64) (result i32)
    (i32.trunc_f64_u (local.get 0)))

  ;; ---- min/max (WASM NaN-propagation + -0 < +0) ----
  (func (export "f32_min") (param f32 f32) (result f32)
    (f32.min (local.get 0) (local.get 1)))
  (func (export "f32_max") (param f32 f32) (result f32)
    (f32.max (local.get 0) (local.get 1)))
  (func (export "f64_min") (param f64 f64) (result f64)
    (f64.min (local.get 0) (local.get 1)))
  (func (export "f64_max") (param f64 f64) (result f64)
    (f64.max (local.get 0) (local.get 1)))

  ;; ---- copysign (bit-exact incl. NaN sign) ----
  (func (export "f32_copysign") (param f32 f32) (result f32)
    (f32.copysign (local.get 0) (local.get 1)))
  (func (export "f64_copysign") (param f64 f64) (result f64)
    (f64.copysign (local.get 0) (local.get 1)))

  ;; ---- f32.sqrt (m3 op, m4 differential coverage) ----
  (func (export "f32_sqrt") (param f32) (result f32)
    (f32.sqrt (local.get 0))))
