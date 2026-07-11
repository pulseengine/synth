;; VCR-PERF-002 Phase 3 (#494) — the gust_mix clamp lowered BRANCHLESSLY.
;;
;; gust_mix is algebraically clamp(ch + 476, 1000, 2000). The Phase-2 fixture
;; (fact_spec_clamp_494.wat) writes the clamp with `if`/`end`; a real optimizing
;; front-end (and LLVM) lowers a min/max clamp BRANCHLESSLY with `select`:
;;
;;   max(v, 1000) = (v < 1000) ? 1000 : v
;;   min(v, 2000) = (v > 2000) ? 2000 : v
;;
;; Under the loom-proven premise ch ∈ [524, 1524] (forwarded as a schema-v1
;; `wsc.facts` value-range record on value_id 0 = the `local.get $ch` producing
;; ch), v = ch+476 ∈ [1000, 2000], so BOTH select conditions are constant-false.
;; The Phase-3 select-collapse pass (SYNTH_FACT_SPEC=1) discharges, per site,
;; UNSAT(P ∧ cond ≠ 0) through the ordeal-backed certificate-checked solver and
;; collapses each `select` to its identity operand — deleting the guard
;; comparison + the dead operand + the branchless `select` mux itself. This is
;; the shape Phase 2's `if`-elision cannot touch (no `if` in the stream); it is
;; the branchless sibling of that elision and the form gust_mix actually uses.
;;
;; The facts section is appended by the harnesses (the .wat itself is
;; facts-free): scripts/repro/fact_spec_select_494_differential.py.
;;
;; Op indices (value_id space, decoded order):
;;   0 local.get $ch   <- value-range fact target
;;   1 i32.const 476
;;   2 i32.add         v = ch+476
;;   3 local.set $v
;;   4 i32.const 1000  low-clamp val1 (deleted)
;;   5 local.get $v    low-clamp val2 (survives — identity)
;;   6 local.get $v   -+ low-clamp condition slice + select
;;   7 i32.const 1000  | (deleted: ops 6..=9)
;;   8 i32.lt_s        |
;;   9 select         -+
;;  10 local.set $v
;;  11 i32.const 2000  high-clamp val1 (deleted)
;;  12 local.get $v    high-clamp val2 (survives — identity)
;;  13 local.get $v   -+ high-clamp condition slice + select
;;  14 i32.const 2000  | (deleted: ops 13..=16)
;;  15 i32.gt_s        |
;;  16 select         -+
;;  17 end
(module
  (func (export "gust_mix") (param $ch i32) (result i32)
    (local $v i32)
    local.get $ch
    i32.const 476
    i32.add
    local.set $v
    ;; clamp low: max(v, 1000) = (v < 1000) ? 1000 : v
    i32.const 1000
    local.get $v
    local.get $v
    i32.const 1000
    i32.lt_s
    select
    local.set $v
    ;; clamp high: min(v, 2000) = (v > 2000) ? 2000 : v
    i32.const 2000
    local.get $v
    local.get $v
    i32.const 2000
    i32.gt_s
    select))
