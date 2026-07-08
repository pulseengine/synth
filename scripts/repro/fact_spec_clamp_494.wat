;; VCR-PERF-002 Phase 2 (#494) — the gust_mix clamp shape.
;;
;; gust_mix is algebraically clamp(ch + 476, 1000, 2000). Under the loom-proven
;; premise ch ∈ [524, 1524] (forwarded as a schema-v1 `wsc.facts` value-range
;; record on value_id 0 = the `local.get $ch` producing ch), BOTH clamp
;; comparisons are constant-false: v = ch+476 ∈ [1000, 2000], so `v < 1000`
;; and `v > 2000` never hold. The fact-spec pass (SYNTH_FACT_SPEC=1) elides
;; both `if` regions AND their condition slices after discharging, per site,
;; UNSAT(P ∧ cond ≠ 0) through the ordeal-backed certificate-checked solver —
;; collapsing the body toward the measured floor `add r0, #476; bx lr`
;; (gale gust_floor_bench, 0.45x of native).
;;
;; The facts section is appended by the harnesses (the .wat itself is
;; facts-free): scripts/repro/fact_spec_clamp_494_differential.py and
;; crates/synth-cli/tests/fact_spec_clamp_494.rs.
;;
;; Op indices (value_id space, decoded order):
;;   0 local.get $ch   <- value-range fact target
;;   1 i32.const 476
;;   2 i32.add
;;   3 local.set $v
;;   4 local.get $v    -+
;;   5 i32.const 1000   | low-clamp condition slice + branch + body
;;   6 i32.lt_s         | (elided: ops 4..=10)
;;   7 if               |
;;   8 i32.const 1000   |
;;   9 local.set $v     |
;;  10 end             -+
;;  11 local.get $v    -+
;;  12 i32.const 2000   | high-clamp (elided: ops 11..=17)
;;  13 i32.gt_s         |
;;  14 if               |
;;  15 i32.const 2000   |
;;  16 local.set $v     |
;;  17 end             -+
;;  18 local.get $v
;;  19 end
(module
  (func (export "gust_mix") (param $ch i32) (result i32)
    (local $v i32)
    local.get $ch
    i32.const 476
    i32.add
    local.set $v
    local.get $v
    i32.const 1000
    i32.lt_s
    if
      i32.const 1000
      local.set $v
    end
    local.get $v
    i32.const 2000
    i32.gt_s
    if
      i32.const 2000
      local.set $v
    end
    local.get $v))
