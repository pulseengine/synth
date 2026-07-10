;; #686 — gale gust_mix shape: clamp(1500 + ((ch - 1024) * 205 >> 8), 1000, 2000).
;; A Q8 fixed-point scale whose shift amount is a CONSTANT < 32 — the case where
;; the #682 mod-32 mask (`and r12,rK,#31`) is provably dead. gale measured the
;; unconditional mask at ~12% cyc/call (+14 B) on this shape (68 B at v0.37.0 →
;; 82 B at v0.37.1); SYNTH_SHIFT_MASK_ELIDE=1 folds the masked triple back to
;; the immediate shift (`asrs #8`). Pinned by shift_mask_elide_686.rs (per-
;; function no-grow/shrink) and i32_shift_mask_682_differential.py (semantics).
(module
  (func (export "gust_mix") (param i32) (result i32)
    (local i32)
    local.get 0
    i32.const 1024
    i32.sub
    i32.const 205
    i32.mul
    i32.const 8
    i32.shr_s
    i32.const 1500
    i32.add
    local.set 1
    local.get 1
    i32.const 1000
    local.get 1
    i32.const 1000
    i32.lt_s
    select
    local.set 1
    local.get 1
    i32.const 2000
    local.get 1
    i32.const 2000
    i32.gt_s
    select
  )
)
