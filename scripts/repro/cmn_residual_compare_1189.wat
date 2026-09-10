;; RQ-66-WATCHED (#1189) — the direct selector's hand-written `cmn` residual.
;;
;; `select_with_stack` folds an i32 comparison whose right operand is an
;; IMMEDIATELY-preceding `i32.const c` with c in [-0xFF, -1] into
;; `cmn a, #|c|; SetCond dst, <cond>` — `cmp a, #c` with a negative c is
;; not encodable, and `cmn a, #-c` sets the same flags. The POSITIVE fold and
;; the reg-reg path are Rocq-proved `sel_dsl` rules; the negative fold is the
;; RESIDUAL: a hand-written condition table with no proof and, before this
;; fixture, no execution oracle. The v0.65 mutation survey (RQ-65-MUTANTS)
;; inverted `I32Eq => Condition::EQ` in that table and the whole named suite
;; stayed green — on the corpus the only object that changed was
;; gust_kernel's `x == -1` sentinel check inside `gust_poll`.
;;
;; Every function here is `(param i32) (result i32)` and lands on the residual:
;; the constant sits DIRECTLY before the comparison (the fold requires it) and
;; is negative and within a byte. Three magnitudes: the -1 sentinel (the
;; gust_poll shape), a mid value, and the -0xFF boundary. The three `p_*`
;; controls use a POSITIVE immediate (the Rocq-proved `i32_cmp_imm_rule` path)
;; and `rr_eq`/`rr_lt_s` the reg-reg rule, so a regression that moved the
;; fold boundary would also be visible. `used_*` consume the SetCond value
;; arithmetically (dst is a temp, not R0) and `sel_*` feed it to a select.
(module
  ;; ---- the ten conditions at -1 (the gust_poll sentinel) ----
  (func (export "eq_m1")   (param i32) (result i32) local.get 0 i32.const -1 i32.eq)
  (func (export "ne_m1")   (param i32) (result i32) local.get 0 i32.const -1 i32.ne)
  (func (export "lt_s_m1") (param i32) (result i32) local.get 0 i32.const -1 i32.lt_s)
  (func (export "lt_u_m1") (param i32) (result i32) local.get 0 i32.const -1 i32.lt_u)
  (func (export "gt_s_m1") (param i32) (result i32) local.get 0 i32.const -1 i32.gt_s)
  (func (export "gt_u_m1") (param i32) (result i32) local.get 0 i32.const -1 i32.gt_u)
  (func (export "le_s_m1") (param i32) (result i32) local.get 0 i32.const -1 i32.le_s)
  (func (export "le_u_m1") (param i32) (result i32) local.get 0 i32.const -1 i32.le_u)
  (func (export "ge_s_m1") (param i32) (result i32) local.get 0 i32.const -1 i32.ge_s)
  (func (export "ge_u_m1") (param i32) (result i32) local.get 0 i32.const -1 i32.ge_u)

  ;; ---- the ten conditions at -37 (mid byte) ----
  (func (export "eq_m37")   (param i32) (result i32) local.get 0 i32.const -37 i32.eq)
  (func (export "ne_m37")   (param i32) (result i32) local.get 0 i32.const -37 i32.ne)
  (func (export "lt_s_m37") (param i32) (result i32) local.get 0 i32.const -37 i32.lt_s)
  (func (export "lt_u_m37") (param i32) (result i32) local.get 0 i32.const -37 i32.lt_u)
  (func (export "gt_s_m37") (param i32) (result i32) local.get 0 i32.const -37 i32.gt_s)
  (func (export "gt_u_m37") (param i32) (result i32) local.get 0 i32.const -37 i32.gt_u)
  (func (export "le_s_m37") (param i32) (result i32) local.get 0 i32.const -37 i32.le_s)
  (func (export "le_u_m37") (param i32) (result i32) local.get 0 i32.const -37 i32.le_u)
  (func (export "ge_s_m37") (param i32) (result i32) local.get 0 i32.const -37 i32.ge_s)
  (func (export "ge_u_m37") (param i32) (result i32) local.get 0 i32.const -37 i32.ge_u)

  ;; ---- the ten conditions at -255 (the fold's boundary magnitude) ----
  (func (export "eq_m255")   (param i32) (result i32) local.get 0 i32.const -255 i32.eq)
  (func (export "ne_m255")   (param i32) (result i32) local.get 0 i32.const -255 i32.ne)
  (func (export "lt_s_m255") (param i32) (result i32) local.get 0 i32.const -255 i32.lt_s)
  (func (export "lt_u_m255") (param i32) (result i32) local.get 0 i32.const -255 i32.lt_u)
  (func (export "gt_s_m255") (param i32) (result i32) local.get 0 i32.const -255 i32.gt_s)
  (func (export "gt_u_m255") (param i32) (result i32) local.get 0 i32.const -255 i32.gt_u)
  (func (export "le_s_m255") (param i32) (result i32) local.get 0 i32.const -255 i32.le_s)
  (func (export "le_u_m255") (param i32) (result i32) local.get 0 i32.const -255 i32.le_u)
  (func (export "ge_s_m255") (param i32) (result i32) local.get 0 i32.const -255 i32.ge_s)
  (func (export "ge_u_m255") (param i32) (result i32) local.get 0 i32.const -255 i32.ge_u)

  ;; ---- the SetCond value consumed (dst is a temp, not the R0 tail) ----
  (func (export "used_eq_m1") (param i32) (result i32)
    local.get 0 i32.const -1 i32.eq
    i32.const 100 i32.add)
  (func (export "used_lt_s_m9") (param i32) (result i32)
    local.get 0 i32.const -9 i32.lt_s
    local.get 0 i32.add)
  (func (export "used_ge_u_m200") (param i32) (result i32)
    local.get 0 i32.const -200 i32.ge_u
    i32.const 3 i32.mul)

  ;; ---- the SetCond value as a select condition ----
  (func (export "sel_eq_m1") (param i32) (result i32)
    i32.const 11 i32.const 22
    local.get 0 i32.const -1 i32.eq
    select)
  (func (export "sel_gt_s_m5") (param i32) (result i32)
    i32.const 33 i32.const 44
    local.get 0 i32.const -5 i32.gt_s
    select)

  ;; ---- CONTROLS: the proved paths, same conditions ----
  (func (export "p_eq_37")   (param i32) (result i32) local.get 0 i32.const 37 i32.eq)
  (func (export "p_lt_s_37") (param i32) (result i32) local.get 0 i32.const 37 i32.lt_s)
  (func (export "p_ge_u_255") (param i32) (result i32) local.get 0 i32.const 255 i32.ge_u)
  (func (export "rr_eq")   (param i32 i32) (result i32) local.get 0 local.get 1 i32.eq)
  (func (export "rr_lt_s") (param i32 i32) (result i32) local.get 0 local.get 1 i32.lt_s)
  ;; -256 is OUTSIDE the byte fold: must take the reg-reg (materialized) path.
  (func (export "out_eq_m256") (param i32) (result i32) local.get 0 i32.const -256 i32.eq)
)
