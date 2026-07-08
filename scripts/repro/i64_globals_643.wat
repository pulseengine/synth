;; #643: i64 global.set/global.get on Thumb-2 truncated to 32 bits — the high
;; word was silently dropped (one str/ldr at [r9,#idx*4] instead of a pair, and
;; the 4-byte slot layout had no room for the second word).
;;
;; Fixture shape:
;;   * $c (i64, index 0) — the truncation target. Values straddle 32 bits.
;;   * $k (i32, index 1) — declared AFTER the i64 global: the LAYOUT-SHIFT
;;     canary. Its slot must move from [r9,#4] to [r9,#8]; a fix that pairs the
;;     i64 access but keeps idx*4 addressing makes set64 clobber $k (and
;;     vice versa).
;;   * set-then-get ACROSS calls (set64 / get_lo / get_hi) and within one call
;;     (roundtrip_hi — gale's exact #643 repro shape).
;;   * pure_add — global-free control: stays compilable everywhere (and is the
;;     non-vacuity anchor for the RV32 loud-skip check).
(module
  (global $c (mut i64) (i64.const 0))
  (global $k (mut i32) (i32.const 0))

  ;; store an i64 assembled from two i32 halves
  (func (export "set64") (param $lo i32) (param $hi i32)
    (global.set $c
      (i64.or
        (i64.extend_i32_u (local.get $lo))
        (i64.shl (i64.extend_i32_u (local.get $hi)) (i64.const 32)))))

  (func (export "get_lo") (result i32)
    (i32.wrap_i64 (global.get $c)))

  (func (export "get_hi") (result i32)
    (i32.wrap_i64 (i64.shr_u (global.get $c) (i64.const 32))))

  (func (export "set32") (param i32)
    (global.set $k (local.get 0)))

  (func (export "get32") (result i32)
    (global.get $k))

  ;; gale's #643 reproducer: set + get of the i64 global in ONE function,
  ;; returning the high word. Was 32 (the shift amount) instead of 0x12345678.
  (func (export "roundtrip_hi") (param i32 i32) (result i32)
    (global.set $c (i64.const 0x123456789ABCDEF0))
    (i32.wrap_i64 (i64.shr_u (global.get $c) (i64.const 32))))

  ;; global-free control
  (func (export "pure_add") (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1))))
