(module
  ;; #317 — RV32 i64.div_s / i64.rem_s sign clobber.
  ;;
  ;; The signed 64-bit div/rem lowering records each operand's sign
  ;; (`nsign`/`dsign`) then feeds |dividend| / |divisor| to the inline unsigned
  ;; long-division core. The core uses a FIXED register file (t0..t6 / s1..s3)
  ;; that bypasses the allocator; pre-fix, `nsign`/`dsign` were handed out by
  ;; the lowest-free allocator into t4/t5 — which are the core's DIV_D_LO /
  ;; DIV_D_HI. The core's input parallel-move copied the divisor into t4/t5,
  ;; clobbering the sign masks BEFORE `result_sign = nsign ^ dsign` was
  ;; computed, so the quotient/remainder came back with the wrong sign
  ;; (e.g. div_s(-100,3) → 0x1f instead of 0xffffffffffffffde).
  ;;
  ;; i64 *params* are unsupported on the RV32 selector today (skip-and-
  ;; continue), so the operands are built at runtime from two i32 params via
  ;; i64.extend_i32_s — this keeps them non-constant (unfoldable) while still
  ;; exercising the full signed div/rem path with the sign fix-up.

  (func (export "divs") (param $n i32) (param $d i32) (result i64)
    (i64.div_s
      (i64.extend_i32_s (local.get $n))
      (i64.extend_i32_s (local.get $d))))

  (func (export "rems") (param $n i32) (param $d i32) (result i64)
    (i64.rem_s
      (i64.extend_i32_s (local.get $n))
      (i64.extend_i32_s (local.get $d)))))
