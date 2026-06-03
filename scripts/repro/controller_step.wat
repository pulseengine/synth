;; #226 — controller_step: a long live range across three `select`-clamps.
;;
;; Reproduces the RV32 regalloc clobber gale found in v0.11.23: an
;; `updates << 24` value is computed first and left live on the operand stack
;; while three inlined `select`-based clamps run above it; the final pack `or`s
;; it back in. The clamps issue enough scratch allocations that a vstack-blind
;; round-robin allocator wraps the temp pool back onto the register pinning
;; `updates << 24`, losing the updates byte. wasmtime is the ground truth.
;;
;; Single leaf function (loom-dissolved — no calls), matching the gale repro.
;; Result layout:  updates<<24 | rudder<<16 | elevator<<8 | aileron
(module
  (memory (export "memory") 1)

  (func (export "controller_step_decide")
    (param $setpoint i32) (param $p1 i32) (param $position i32)
    (param $p3 i32) (param $rate i32) (param $p5 i32) (param $updates i32)
    (result i32)
    (local $t i32) (local $lo i32) (local $r i32)

    ;; updates<<24 computed FIRST; stays live on the stack to the final or.
    (i32.shl (local.get $updates) (i32.const 24))

    ;; ── rudder<<16 : clamp(setpoint - position, 0, 255) ──
    (local.set $t (i32.sub (local.get $setpoint) (local.get $position)))
    (local.set $lo
      (select (i32.const 0) (local.get $t)
        (i32.lt_s (local.get $t) (i32.const 0))))
    (local.set $r
      (select (i32.const 255) (local.get $lo)
        (i32.gt_s (local.get $lo) (i32.const 255))))
    (i32.or (i32.shl (local.get $r) (i32.const 16)))

    ;; ── elevator<<8 : clamp(position + rate, 0, 255) ──
    (local.set $t (i32.add (local.get $position) (local.get $rate)))
    (local.set $lo
      (select (i32.const 0) (local.get $t)
        (i32.lt_s (local.get $t) (i32.const 0))))
    (local.set $r
      (select (i32.const 255) (local.get $lo)
        (i32.gt_s (local.get $lo) (i32.const 255))))
    (i32.or (i32.shl (local.get $r) (i32.const 8)))

    ;; ── aileron : clamp(rate - setpoint, 0, 255) ──
    (local.set $t (i32.sub (local.get $rate) (local.get $setpoint)))
    (local.set $lo
      (select (i32.const 0) (local.get $t)
        (i32.lt_s (local.get $t) (i32.const 0))))
    (local.set $r
      (select (i32.const 255) (local.get $lo)
        (i32.gt_s (local.get $lo) (i32.const 255))))
    (i32.or (local.get $r)))
)
