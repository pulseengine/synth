;; #881 (GI-FPU-002 + RA tail): VFP register-file exhaustion — the two decline
;; classes that block the falcon cascade entry points on cortex-m7dp:
;;
;;  * `deep_s`  — phase 1: an f32 expression tree with >16 simultaneously-live
;;    single-precision values (S0..S15 all live) — `position@0.7.0#tick` /
;;    `attitude@0.7.0#tick` / iekf `ekf@0.7.0#estimate`.
;;  * `deep_d`  — phase 2: an f64 expression with >8 simultaneously-live
;;    double-precision values (caller-saved D0..D7 all live) —
;;    `rate@0.7.0#tick` / `ekf@0.7.0#estimate`.
;;  * `deep_mix` — the v0.52 #869 shape: i64<->f32 conversions (whose lowerings
;;    run on D-register machinery) fired while a deep f32 stack is live —
;;    the exact "f32-only code with no f64 of its own" D-pressure gale reported.
;;
;; The real falcon-components-v1.128.tar.gz per-stage artifact is not
;; reachable from this environment, so these fixtures reproduce the SAME
;; exhaustion errors (message-for-message) as the falcon entry points, and the
;; gate is: all three compile to `nm -> T` symbols on
;; `-t cortex-m7dp --relocatable` AND execute bit-identical to wasmtime.
(module
  ;; Phase 1: 20 f32 values live at peak (params a..d kept live to the end,
  ;; plus a 16-deep constant tree), folded so every intermediate stays live.
  (func $deep_s (export "deep_s") (param $a f32) (param $b f32) (result f32)
    local.get $a
    local.get $b
    f32.const 1.5
    f32.const 2.5
    f32.const 3.25
    f32.const 4.125
    f32.const 5.0625
    f32.const 6.5
    f32.const 7.25
    f32.const 8.125
    f32.const 9.5
    f32.const 10.25
    f32.const 11.125
    f32.const 12.5
    f32.const 13.25
    f32.const 14.125
    f32.const 15.5
    f32.const 16.25
    f32.const 17.125
    f32.const 18.5
    ;; fold 20 values -> 1 (19 adds); peak simultaneous liveness = 20 > 16
    f32.add f32.add f32.add f32.add f32.add
    f32.add f32.add f32.add f32.add f32.add
    f32.add f32.add f32.add f32.add f32.add
    f32.add f32.add f32.add f32.add)

  ;; Phase 2: 10 f64 values live at peak > 8 caller-saved D registers.
  (func $deep_d (export "deep_d") (result f32)
    f64.const 1.5
    f64.const 2.25
    f64.const 3.125
    f64.const 4.0625
    f64.const 5.5
    f64.const 6.25
    f64.const 7.125
    f64.const 8.0625
    f64.const 9.5
    f64.const 10.25
    f64.add f64.add f64.add f64.add f64.add
    f64.add f64.add f64.add f64.add
    f32.demote_f64)

  ;; f32 spilled ACROSS a call: ~12 live f32 while calling a helper — the
  ;; spilled entries are frame-resident (no caller-saved preservation needed),
  ;; the register-resident rest rides the #719 VFP call-spill area.
  (func $helper (param $v f32) (result f32)
    local.get $v
    f32.const 2.0
    f32.mul)
  (func $spill_call (export "spill_call") (param $a f32) (result f32)
    f32.const 1.5
    f32.const 2.5
    f32.const 3.25
    f32.const 4.125
    f32.const 5.5
    f32.const 6.25
    f32.const 7.125
    f32.const 8.5
    f32.const 9.25
    f32.const 10.125
    f32.const 11.5
    f32.const 12.25
    f32.const 13.125
    f32.const 14.5
    f32.const 15.25
    local.get $a
    call $helper
    f32.add f32.add f32.add f32.add f32.add
    f32.add f32.add f32.add f32.add f32.add
    f32.add f32.add f32.add f32.add f32.add)

  ;; Pinned f32 local homes + a deep tree: homes are never spill victims,
  ;; the expression temps around them are.
  (func $deep_local (export "deep_local") (param $a f32) (result f32)
    (local $t f32) (local $u f32)
    local.get $a
    f32.const 3.0
    f32.mul
    local.set $t
    local.get $a
    f32.const 5.0
    f32.add
    local.set $u
    local.get $t
    local.get $u
    f32.const 1.5
    f32.const 2.5
    f32.const 3.25
    f32.const 4.125
    f32.const 5.5
    f32.const 6.25
    f32.const 7.125
    f32.const 8.5
    f32.const 9.25
    f32.const 10.125
    f32.const 11.5
    f32.const 12.25
    f32.const 13.125
    f32.const 14.5
    f32.const 15.25
    f32.const 16.125
    f32.add f32.add f32.add f32.add f32.add f32.add
    f32.add f32.add f32.add f32.add f32.add f32.add
    f32.add f32.add f32.add f32.add f32.add)

  ;; The falcon clamp idiom under pressure: select over two f32 with a deep
  ;; live stack (exercises the select reload window: [val1 val2 cond]).
  (func $deep_select (export "deep_select") (param $a f32) (param $c i32) (result f32)
    f32.const 1.5
    f32.const 2.5
    f32.const 3.25
    f32.const 4.125
    f32.const 5.5
    f32.const 6.25
    f32.const 7.125
    f32.const 8.5
    f32.const 9.25
    f32.const 10.125
    f32.const 11.5
    f32.const 12.25
    f32.const 13.125
    f32.const 14.5
    f32.const 15.25
    f32.const 16.125
    local.get $a
    f32.const 100.0
    local.get $c
    select
    f32.add f32.add f32.add f32.add f32.add f32.add
    f32.add f32.add f32.add f32.add f32.add f32.add
    f32.add f32.add f32.add f32.add)

  ;; Interleaved S/D pressure: live f32 values below live f64 values in the
  ;; ONE aliased register file, with promotes churning transient S-regs
  ;; between D allocations — D-alloc must keep finding ALIGNED pairs (or
  ;; spill until one frees) in a fragmented shared file.
  (func $deep_sd_mix (export "deep_sd_mix") (param $a f32) (result f32)
    local.get $a
    f32.const 1.5
    f32.const 2.5
    f32.const 3.25
    f32.const 4.125
    f32.const 5.5
    f32.const 6.25
    f32.const 7.125
    f64.const 10.25
    f64.const 11.5
    f64.const 12.25
    f64.const 13.125
    f64.const 14.5
    f64.const 15.25
    f64.add f64.add f64.add f64.add f64.add
    f32.demote_f64
    f32.add f32.add f32.add f32.add f32.add f32.add f32.add f32.add)

  ;; The #869 shape: i64->f32 converts (D-register machinery: exact two-word
  ;; f64 build + round-to-odd fixup + demote) under a live f32 stack.
  (func $deep_mix (export "deep_mix") (param $x i64) (param $y i64) (result f32)
    f32.const 1.5
    f32.const 2.5
    f32.const 3.5
    f32.const 4.5
    f32.const 5.5
    f32.const 6.5
    f32.const 7.5
    f32.const 8.5
    f32.const 9.5
    f32.const 10.5
    f32.const 11.5
    f32.const 12.5
    local.get $x
    f32.convert_i64_u
    local.get $y
    f32.convert_i64_s
    f32.add
    f32.add f32.add f32.add f32.add f32.add f32.add
    f32.add f32.add f32.add f32.add f32.add f32.add))
