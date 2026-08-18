;; #973 — ARM: `select` on an i64-comparison condition with COMPUTED arms.
;;
;; The i64 comparison needs a consecutive register PAIR for each sign-extended
;; operand. `alloc_consecutive_pair` frees one by spilling the DEEPEST
;; register-resident vstack entry — which is the select's then-arm, sitting
;; under the else-arm and the condition. When `select` later pops its operands
;; the reload of that spilled then-arm allocated against `live_params` ONLY, so
;; it could pick the register still holding the LIVE else-arm (or the condition
;; itself): both `it` arms then moved the same register and the select always
;; returned the then-value.
;;
;; Every shape below is `cmp(a, b) ? a + 100 : b + 200` so the two arms are
;; DISTINCT for every argument pair, including a == b — a fixture whose arms
;; coincide cannot see this defect at all (and `i32.const` arms make it vanish
;; because nothing needs spilling).
;;
;; The bare comparisons are carried alongside as the CONTRAST: they were always
;; correct, so a run where they fail too is a different defect.
(module
  ;; ── the reported shape, once per signed/unsigned i64 comparison ──────────
  (func $sel_i64_lt_s (export "sel_i64_lt_s") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i64.lt_s (i64.extend_i32_s (local.get $a))
                      (i64.extend_i32_s (local.get $b)))))

  (func $sel_i64_lt_u (export "sel_i64_lt_u") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i64.lt_u (i64.extend_i32_u (local.get $a))
                      (i64.extend_i32_u (local.get $b)))))

  (func $sel_i64_gt_s (export "sel_i64_gt_s") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i64.gt_s (i64.extend_i32_s (local.get $a))
                      (i64.extend_i32_s (local.get $b)))))

  (func $sel_i64_le_s (export "sel_i64_le_s") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i64.le_s (i64.extend_i32_s (local.get $a))
                      (i64.extend_i32_s (local.get $b)))))

  (func $sel_i64_ge_u (export "sel_i64_ge_u") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i64.ge_u (i64.extend_i32_u (local.get $a))
                      (i64.extend_i32_u (local.get $b)))))

  (func $sel_i64_eq (export "sel_i64_eq") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i64.eq (i64.extend_i32_s (local.get $a))
                    (i64.extend_i32_s (local.get $b)))))

  (func $sel_i64_ne (export "sel_i64_ne") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i64.ne (i64.extend_i32_s (local.get $a))
                    (i64.extend_i32_s (local.get $b)))))

  ;; i64 comparison whose OPERANDS are themselves computed — more pressure, so
  ;; the spill/reload window is wider than in the minimal repro.
  (func $sel_i64_deep (export "sel_i64_deep") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i64.lt_s (i64.add (i64.extend_i32_s (local.get $a)) (i64.const 7))
                      (i64.mul (i64.extend_i32_s (local.get $b)) (i64.const 3)))))

  ;; ── the WIDE select: i64 ARMS under an i64-comparison condition ──────────
  ;; Result folds lo ^ hi so a wrong half is loud rather than invisible.
  (func $sel_wide_i64cmp (export "sel_wide_i64cmp") (param $a i32) (param $b i32) (result i32)
    (local $v i64)
    (local.set $v
      (select (i64.add (i64.extend_i32_s (local.get $a)) (i64.const 0x100000064))
              (i64.add (i64.extend_i32_s (local.get $b)) (i64.const 0x2000000C8))
              (i64.lt_s (i64.extend_i32_s (local.get $a))
                        (i64.extend_i32_s (local.get $b)))))
    (i32.xor (i32.wrap_i64 (local.get $v))
             (i32.wrap_i64 (i64.shr_u (local.get $v) (i64.const 32)))))

  ;; ── contrast: the comparisons ALONE were always correct ─────────────────
  (func $cmp_i64_lt_s (export "cmp_i64_lt_s") (param $a i32) (param $b i32) (result i32)
    (i64.lt_s (i64.extend_i32_s (local.get $a))
              (i64.extend_i32_s (local.get $b))))

  (func $cmp_i64_ge_u (export "cmp_i64_ge_u") (param $a i32) (param $b i32) (result i32)
    (i64.ge_u (i64.extend_i32_u (local.get $a))
              (i64.extend_i32_u (local.get $b))))

  ;; ── guards: shapes the fix must NOT change ──────────────────────────────
  ;; Constant arms: nothing to spill, so this passed before the fix too.
  (func $guard_const_arms (export "guard_const_arms") (param $a i32) (param $b i32) (result i32)
    (select (i32.const 100) (i32.const 200)
            (i64.lt_s (i64.extend_i32_s (local.get $a))
                      (i64.extend_i32_s (local.get $b)))))

  ;; i32-comparison condition with computed arms — the ordinary select path,
  ;; correct before and after (and byte-frozen elsewhere).
  (func $guard_i32cmp (export "guard_i32cmp") (param $a i32) (param $b i32) (result i32)
    (select (i32.add (local.get $a) (i32.const 100))
            (i32.add (local.get $b) (i32.const 200))
            (i32.lt_s (local.get $a) (local.get $b))))

  ;; BOTH arms are the same value: the two conditional moves LEGITIMATELY read
  ;; one register here, so "same source" is not by itself the defect signature.
  (func $guard_same_arm (export "guard_same_arm") (param $a i32) (param $b i32) (result i32)
    (select (local.get $a) (local.get $a)
            (i64.lt_s (i64.extend_i32_s (local.get $a))
                      (i64.extend_i32_s (local.get $b)))))

  ;; Nested selects on i64 conditions: the second select's operands are live
  ;; across the first one's spill window.
  (func $guard_nested (export "guard_nested") (param $a i32) (param $b i32) (result i32)
    (select (select (i32.add (local.get $a) (i32.const 100))
                    (i32.add (local.get $b) (i32.const 200))
                    (i64.lt_s (i64.extend_i32_s (local.get $a))
                              (i64.extend_i32_s (local.get $b))))
            (i32.add (local.get $b) (i32.const 300))
            (i64.gt_s (i64.extend_i32_s (local.get $a))
                      (i64.extend_i32_s (local.get $b)))))
)
