;; #1048: the Thumb-2 and A32 expansions of I64Shl / I64ShrU / I64ShrS opened
;; by masking the shift amount IN PLACE (`AND rm_lo, rm_lo, #63`) and writing
;; `amt-32` into the amount's HOME HIGH REGISTER (`SUBS rm_hi, rm_lo, #32`) —
;; the expansion destroyed its own input operand. Sibling class in the same
;; commit: I64Clz / I64Ctz / I64Popcnt ended with `MOV rnhi, #0` — a hi-word
;; clear aimed at the RESULT that lands on the OPERAND's home high register on
;; the direct selector (which allocates a fresh destination pair and zeroes
;; its own dst_hi).
;;
;; Every function here re-reads an operand AFTER the i64 pseudo-op consumed
;; it. The wired #599 differential could never see this class: all its
;; functions consume the shift result immediately and never read the amount
;; again, so the destroyed registers are dead in every one of its vectors.
(module
  (func (export "shl_reread") (param $x i64) (param $amt i64) (result i64)
    (i64.add (i64.shl (local.get $x) (local.get $amt)) (local.get $amt)))
  (func (export "shr_u_reread") (param $x i64) (param $amt i64) (result i64)
    (i64.add (i64.shr_u (local.get $x) (local.get $amt)) (local.get $amt)))
  (func (export "shr_s_reread") (param $x i64) (param $amt i64) (result i64)
    (i64.add (i64.shr_s (local.get $x) (local.get $amt)) (local.get $amt)))
  ;; value-operand re-read after a shift (guards the rn pair as well)
  (func (export "shl_reread_val") (param $x i64) (param $amt i64) (result i64)
    (i64.add (i64.shl (local.get $x) (local.get $amt)) (local.get $x)))
  ;; bit-count siblings: re-read the counted operand
  (func (export "clz_reread") (param $x i64) (result i64)
    (i64.add (i64.clz (local.get $x)) (local.get $x)))
  (func (export "ctz_reread") (param $x i64) (result i64)
    (i64.add (i64.ctz (local.get $x)) (local.get $x)))
  (func (export "popcnt_reread") (param $x i64) (result i64)
    (i64.add (i64.popcnt (local.get $x)) (local.get $x)))
  ;; #610 fixed-ABI wrapper family (div/rem, rotl/rotr): the wrapper
  ;; saves/restores R0-R3, so operand re-reads must already hold — pinned
  ;; here so a future wrapper regression is caught by execution, not by
  ;; nobody
  (func (export "div_u_reread") (param $x i64) (param $amt i64) (result i64)
    (i64.add (i64.div_u (local.get $x) (local.get $amt)) (local.get $amt)))
  (func (export "rotl_reread") (param $x i64) (param $amt i64) (result i64)
    (i64.add (i64.rotl (local.get $x) (local.get $amt)) (local.get $amt))))
