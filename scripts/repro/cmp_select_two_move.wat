;; VCR-SEL-004 characterization fixture (#428) — forces the selector's TWO-MOVE
;; (non-in-place) select form: `val2` is a live param ($lo, read again below), so
;; the selector emits `cmp; SetCond D; cmp D,#0; movne dst,val1; moveq dst,val2`
;; (the two-move arm where mov{invert(c)} matters at runtime).
;;
;; FINDING (#428, gale gust_codegen_bench follow-up): fuse_cmp_select currently
;; DECLINES this — the boolean `D` is abandoned after the select (never redefined
;; before the return), so reg_dead_by_redef cannot prove it dead and conservatively
;; bails. This is the SAME mechanism that declines gale's gust_mix clamp #2, and it
;; makes the two-move arm effectively unreachable through the real selector. The
;; fix (recognize "abandoned + not-live-out" as dead) is a byte-changing VCR-SEL-004
;; follow-on; when it lands, the characterization test flips to assert fusion.
(module
  (memory (export "mem") 1)
  (func (export "two_move_sel") (param $a i32) (param $b i32) (param $lo i32) (result i32)
    (local $sel i32)
    (local.set $sel
      (select (local.get $a) (local.get $lo)
              (i32.lt_s (local.get $a) (local.get $b))))
    (i32.add
      (i32.mul (local.get $sel) (local.get $lo))
      (i32.sub (local.get $a) (local.get $b)))))
