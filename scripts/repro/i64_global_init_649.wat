;; #649: nonzero i64.const GLOBAL INITIALIZERS were silently ZEROED — the
;; decoder captured only a leading `i32.const` (init_i32), so an i64 global's
;; init never reached the emitted image: reads returned 0 until a set.
;; (#645 fixed the get/set PAIR lowering + slot layout, but not initializers.)
;;
;; Fixture shape:
;;   * $g (i64, index 0) — nonzero i64 init straddling 32 bits, read via
;;     global.get BEFORE any set: the red case.
;;   * $c (i32, index 1) — declared AFTER the i64 global with its own nonzero
;;     init: the OFFSET canary. Its init must land at the summed-width slot
;;     ([r9,#8]), not idx*4 ([r9,#4] — which would alias $g's high word).
;;   * set64/set32 + re-reads — the #645 set-then-get pin (no regression).
;;   * get_lo is FIRST: the self-contained image's startup BLXes function 0,
;;     so function 0 must not mutate the globals before the harness reads them.
;;   * pure_add — global-free control.
(module
  (global $g (mut i64) (i64.const 0x123456789ABCDEF0))
  (global $c (mut i32) (i32.const 0x0C0FFEE1))

  (func (export "get_lo") (result i32)
    (i32.wrap_i64 (global.get $g)))

  (func (export "get_hi") (result i32)
    (i32.wrap_i64 (i64.shr_u (global.get $g) (i64.const 32))))

  (func (export "get32") (result i32)
    (global.get $c))

  ;; store an i64 assembled from two i32 halves (#643 harness shape)
  (func (export "set64") (param $lo i32) (param $hi i32)
    (global.set $g
      (i64.or
        (i64.extend_i32_u (local.get $lo))
        (i64.shl (i64.extend_i32_u (local.get $hi)) (i64.const 32)))))

  (func (export "set32") (param i32)
    (global.set $c (local.get 0)))

  ;; global-free control
  (func (export "pure_add") (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1))))
