;; VCR-PERF-002 Phase 2b (#494) — divisor-nonzero trap-guard elision fixture.
;;
;; Four functions dividing by a PARAM divisor (the shape where the div/rem
;; trap guards are otherwise unavoidable — const_divisor cannot see a param):
;;
;;   func 0 qu   (i32) n / d  (div_u)  — 1 guard:  divide-by-zero
;;   func 1 qs   (i32) n / d  (div_s)  — 2 guards: divide-by-zero + INT32_MIN/-1
;;   func 2 ru   (i32) n % d  (rem_u)  — 1 guard:  divide-by-zero
;;   func 3 qs64 (i64) n / d  (div_s)  — 2 guards: divide-by-zero + INT64_MIN/-1
;;
;; Every function has the same op-index layout:
;;   0 local.get $n
;;   1 local.get $d   <- fact target (value_id 1: the divisor's producing op)
;;   2 div/rem
;;   3 end
;;
;; The harnesses append the schema-v1 `wsc.facts` section (the .wat itself is
;; facts-free): scripts/repro/fact_spec_div_494_differential.py and
;; crates/synth-cli/tests/fact_spec_div_494.rs.
;;
;; THE TWO-GUARD DISTINCTION (#633/#634): a value-range fact d ∈ [1, 64] on
;; func 1 discharges BOTH obligations (0 and -1 are excluded), so qs loses
;; both guards. A divisor-nonzero fact (kind 3) on func 3 discharges ONLY
;; UNSAT(P ∧ d == 0) — d ≠ 0 does not exclude d == -1 — so qs64 keeps the
;; INT64_MIN/-1 overflow guard: i64.div_s(INT64_MIN, -1) still traps.
(module
  (func (export "qu") (param $n i32) (param $d i32) (result i32)
    local.get $n
    local.get $d
    i32.div_u)
  (func (export "qs") (param $n i32) (param $d i32) (result i32)
    local.get $n
    local.get $d
    i32.div_s)
  (func (export "ru") (param $n i32) (param $d i32) (result i32)
    local.get $n
    local.get $d
    i32.rem_u)
  (func (export "qs64") (param $n i64) (param $d i64) (result i64)
    local.get $n
    local.get $d
    i64.div_s))
