;; #538 milestone-2 — the aarch64 broadened integer-subset acceptance module.
;; Every export is a leaf integer function the m2 A64 selector lowers: the full
;; i32 AND i64 ALU — add/sub/mul/and/or/xor, shifts (shl/shr_s/shr_u), rotates
;; (rotl/rotr), clz/ctz, and the compare family (eq/ne/lt/gt/le/ge s+u, eqz).
;; The differential (aarch64_m2_538_differential.py) runs each under unicorn
;; UC_ARCH_ARM64 (and natively on an arm64 host) and diffs wasmtime ground truth.
;;
;; NOTE: division (div/rem) and popcnt are deliberately absent — the m2 selector
;; loud-declines them (A64 SDIV/UDIV don't trap; no scalar popcount), and the
;; decline is asserted separately in aarch64_m2_decline_538.py.
(module
  ;; ---- i32 shifts / rotates ----
  (func (export "i32_shl") (param i32 i32) (result i32)
    (i32.shl (local.get 0) (local.get 1)))
  (func (export "i32_shr_u") (param i32 i32) (result i32)
    (i32.shr_u (local.get 0) (local.get 1)))
  (func (export "i32_shr_s") (param i32 i32) (result i32)
    (i32.shr_s (local.get 0) (local.get 1)))
  (func (export "i32_rotr") (param i32 i32) (result i32)
    (i32.rotr (local.get 0) (local.get 1)))
  (func (export "i32_rotl") (param i32 i32) (result i32)
    (i32.rotl (local.get 0) (local.get 1)))

  ;; ---- i32 clz / ctz ----
  (func (export "i32_clz") (param i32) (result i32)
    (i32.clz (local.get 0)))
  (func (export "i32_ctz") (param i32) (result i32)
    (i32.ctz (local.get 0)))

  ;; ---- i32 compares ----
  (func (export "i32_eqz") (param i32) (result i32)
    (i32.eqz (local.get 0)))
  (func (export "i32_eq") (param i32 i32) (result i32)
    (i32.eq (local.get 0) (local.get 1)))
  (func (export "i32_ne") (param i32 i32) (result i32)
    (i32.ne (local.get 0) (local.get 1)))
  (func (export "i32_lt_s") (param i32 i32) (result i32)
    (i32.lt_s (local.get 0) (local.get 1)))
  (func (export "i32_lt_u") (param i32 i32) (result i32)
    (i32.lt_u (local.get 0) (local.get 1)))
  (func (export "i32_le_s") (param i32 i32) (result i32)
    (i32.le_s (local.get 0) (local.get 1)))
  (func (export "i32_le_u") (param i32 i32) (result i32)
    (i32.le_u (local.get 0) (local.get 1)))
  (func (export "i32_gt_s") (param i32 i32) (result i32)
    (i32.gt_s (local.get 0) (local.get 1)))
  (func (export "i32_gt_u") (param i32 i32) (result i32)
    (i32.gt_u (local.get 0) (local.get 1)))
  (func (export "i32_ge_s") (param i32 i32) (result i32)
    (i32.ge_s (local.get 0) (local.get 1)))
  (func (export "i32_ge_u") (param i32 i32) (result i32)
    (i32.ge_u (local.get 0) (local.get 1)))

  ;; ---- i64 arithmetic / bitwise ----
  (func (export "i64_add") (param i64 i64) (result i64)
    (i64.add (local.get 0) (local.get 1)))
  (func (export "i64_sub") (param i64 i64) (result i64)
    (i64.sub (local.get 0) (local.get 1)))
  (func (export "i64_mul") (param i64 i64) (result i64)
    (i64.mul (local.get 0) (local.get 1)))
  (func (export "i64_and") (param i64 i64) (result i64)
    (i64.and (local.get 0) (local.get 1)))
  (func (export "i64_or") (param i64 i64) (result i64)
    (i64.or (local.get 0) (local.get 1)))
  (func (export "i64_xor") (param i64 i64) (result i64)
    (i64.xor (local.get 0) (local.get 1)))

  ;; ---- i64 shifts / rotates ----
  (func (export "i64_shl") (param i64 i64) (result i64)
    (i64.shl (local.get 0) (local.get 1)))
  (func (export "i64_shr_u") (param i64 i64) (result i64)
    (i64.shr_u (local.get 0) (local.get 1)))
  (func (export "i64_shr_s") (param i64 i64) (result i64)
    (i64.shr_s (local.get 0) (local.get 1)))
  (func (export "i64_rotr") (param i64 i64) (result i64)
    (i64.rotr (local.get 0) (local.get 1)))
  (func (export "i64_rotl") (param i64 i64) (result i64)
    (i64.rotl (local.get 0) (local.get 1)))

  ;; ---- i64 clz / ctz ----
  (func (export "i64_clz") (param i64) (result i64)
    (i64.clz (local.get 0)))
  (func (export "i64_ctz") (param i64) (result i64)
    (i64.ctz (local.get 0)))

  ;; ---- i64 compares (result is i32 0/1) ----
  (func (export "i64_eqz") (param i64) (result i32)
    (i64.eqz (local.get 0)))
  (func (export "i64_eq") (param i64 i64) (result i32)
    (i64.eq (local.get 0) (local.get 1)))
  (func (export "i64_ne") (param i64 i64) (result i32)
    (i64.ne (local.get 0) (local.get 1)))
  (func (export "i64_lt_s") (param i64 i64) (result i32)
    (i64.lt_s (local.get 0) (local.get 1)))
  (func (export "i64_lt_u") (param i64 i64) (result i32)
    (i64.lt_u (local.get 0) (local.get 1)))
  (func (export "i64_le_s") (param i64 i64) (result i32)
    (i64.le_s (local.get 0) (local.get 1)))
  (func (export "i64_le_u") (param i64 i64) (result i32)
    (i64.le_u (local.get 0) (local.get 1)))
  (func (export "i64_gt_s") (param i64 i64) (result i32)
    (i64.gt_s (local.get 0) (local.get 1)))
  (func (export "i64_gt_u") (param i64 i64) (result i32)
    (i64.gt_u (local.get 0) (local.get 1)))
  (func (export "i64_ge_s") (param i64 i64) (result i32)
    (i64.ge_s (local.get 0) (local.get 1)))
  (func (export "i64_ge_u") (param i64 i64) (result i32)
    (i64.ge_u (local.get 0) (local.get 1)))

  ;; ---- i64 const ----
  (func (export "i64_const_big") (param i64) (result i64)
    (i64.add (local.get 0) (i64.const 0xBEEFDEAD00012345))))
