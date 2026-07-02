;; #472 — RV32 cmp→select fusion (port of the ARM VCR-SEL-004 lever).
;; A comparison directly feeding a `select` fuses into the select's branch:
;; the boolean materialization (`slt`/`sltu`/`xor`+`sltiu`/`xori`) is deleted
;; and the branch tests the comparison itself (`blt a,b` instead of
;; `slt t,a,b; bne t,zero`). Flag-gated: SYNTH_RV_CMP_SELECT, default OFF.
;; Both the flag-on and flag-off codegen must match wasmtime; the flag-on
;; build must be smaller.
;;
;; One export per fusible i32 comparison kind, each selecting between two
;; arithmetic arms so the result distinguishes the arms even when a == b:
;;   sel_<cmp>(a, b) = cmp(a, b) ? a + 100 : b + 200
;; plus:
;;   sel_eqz    — the one-operand comparison (beq src, zero)
;;   sel_i64    — i32 comparison selecting i64 operands (both halves under
;;                the single fused branch); result = lo ^ hi of the pick
;;   sel_cmp_i64 — an i64 comparison feeding select (NOT fused — out of
;;                scope; must stay correct on the baseline path)
;;   clamp      — back-to-back fused selects (record invalidation stress)
(module
  (func $sel_eq (export "sel_eq") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.eq (local.get $a) (local.get $b))))

  (func $sel_ne (export "sel_ne") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.ne (local.get $a) (local.get $b))))

  (func $sel_lt_s (export "sel_lt_s") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.lt_s (local.get $a) (local.get $b))))

  (func $sel_gt_s (export "sel_gt_s") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.gt_s (local.get $a) (local.get $b))))

  (func $sel_le_s (export "sel_le_s") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.le_s (local.get $a) (local.get $b))))

  (func $sel_ge_s (export "sel_ge_s") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.ge_s (local.get $a) (local.get $b))))

  (func $sel_lt_u (export "sel_lt_u") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.lt_u (local.get $a) (local.get $b))))

  (func $sel_gt_u (export "sel_gt_u") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.gt_u (local.get $a) (local.get $b))))

  (func $sel_le_u (export "sel_le_u") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.le_u (local.get $a) (local.get $b))))

  (func $sel_ge_u (export "sel_ge_u") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.ge_u (local.get $a) (local.get $b))))

  ;; eqz: one-operand comparison → beq src, zero.
  (func $sel_eqz (export "sel_eqz") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.eqz (local.get $a))))

  ;; i32 comparison selecting i64 operands: both halves of the pick move
  ;; under ONE fused branch. Result folds lo ^ hi so a wrong half is loud.
  (func $sel_i64 (export "sel_i64") (param $a i32) (param $b i32) (result i32)
    (local $v i64)
    (local.set $v
      (select (i64.const 0x100000005) (i64.const 0x200000009)
              (i32.lt_u (local.get $a) (local.get $b))))
    (i32.xor (i32.wrap_i64 (local.get $v))
             (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 32)))))

  ;; i64 comparison feeding select — OUT of fusion scope (its boolean needs
  ;; the multi-instruction i64 sequence); must stay correct on the baseline
  ;; branch-on-boolean path with the flag on.
  (func $sel_cmp_i64 (export "sel_cmp_i64") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i64.lt_s (i64.extend_i32_s (local.get $a))
                      (i64.extend_i32_s (local.get $b)))))

  ;; Back-to-back fused selects (the gust-mix clamp shape from the ARM
  ;; lever): clamp(a) = min(max-clamp(a,100), floor 10).
  (func $clamp (export "clamp") (param $a i32) (param $b i32) (result i32)
    (local $x i32)
    (local.set $x (local.get $a))
    (local.set $x
      (select (i32.const 100) (local.get $x)
              (i32.gt_s (local.get $x) (i32.const 100))))
    (select (i32.const 10) (local.get $x)
            (i32.lt_s (local.get $x) (i32.const 10))))
)
