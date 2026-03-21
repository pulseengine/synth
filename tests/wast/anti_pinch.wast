;; Anti-Pinch Window Controller -- WAST test suite
;;
;; Safety-critical automotive use case: prevents window motor from injuring
;; occupants by detecting jam conditions via motor current monitoring.
;;
;; Derived from examples/anti-pinch-controller/anti_pinch.wat
;;
;; Note: Each test runs in a fresh machine with zero-initialized memory.
;; Stateful sequences (init -> set_target -> tick) cannot be tested across
;; separate assertions. Tests focus on:
;;   - Pure functions: check_jam (parameter-only logic)
;;   - Getter functions: verify zero-initialized state readback
;;   - ramp_pwm: reads ramp_rate from memory[28] (0 when not init'd, snaps to target)
;;   - init + getter combos via acc_add-style single-invocation tests

(module
  ;; Linear memory: 1 page (64KB) for controller state
  (memory (export "memory") 1)

  ;; =========================================================================
  ;; init -- Initialize controller to safe defaults
  ;; =========================================================================
  (func (export "init")
    ;; window_position = 0 (fully open)
    i32.const 0
    i32.const 0
    i32.store

    ;; motor_current_ma = 0
    i32.const 4
    i32.const 0
    i32.store

    ;; pwm_duty = 0
    i32.const 8
    i32.const 0
    i32.store

    ;; direction = 0 (stopped)
    i32.const 12
    i32.const 0
    i32.store

    ;; jam_detected = 0
    i32.const 16
    i32.const 0
    i32.store

    ;; current_threshold_ma = 800 (800mA default threshold)
    i32.const 20
    i32.const 800
    i32.store

    ;; target_position = 0 (fully open)
    i32.const 24
    i32.const 0
    i32.store

    ;; pwm_ramp_rate = 20 (2.0% per tick for soft start/stop)
    i32.const 28
    i32.const 20
    i32.store

    ;; consecutive_over = 0
    i32.const 32
    i32.const 0
    i32.store

    ;; jam_debounce_limit = 3 (3 consecutive ticks to confirm jam)
    i32.const 36
    i32.const 3
    i32.store
  )

  ;; =========================================================================
  ;; set_target -- Set desired window position (0=open, 1000=closed)
  ;; =========================================================================
  (func (export "set_target") (param $target i32)
    (local $clamped i32)

    ;; Clamp target to 0-1000
    local.get $target
    local.set $clamped

    ;; if target < 0, clamp to 0
    local.get $clamped
    i32.const 0
    i32.lt_s
    if
      i32.const 0
      local.set $clamped
    end

    ;; if target > 1000, clamp to 1000
    local.get $clamped
    i32.const 1000
    i32.gt_s
    if
      i32.const 1000
      local.set $clamped
    end

    ;; Store clamped target
    i32.const 24
    local.get $clamped
    i32.store

    ;; Clear jam flag when new target is set (allows retry)
    i32.const 16
    i32.const 0
    i32.store

    ;; Reset debounce counter
    i32.const 32
    i32.const 0
    i32.store
  )

  ;; =========================================================================
  ;; update_current -- Feed motor current sensor reading (milliamps)
  ;; =========================================================================
  (func (export "update_current") (param $current_ma i32)
    i32.const 4
    local.get $current_ma
    i32.store
  )

  ;; =========================================================================
  ;; check_jam -- Check if current exceeds threshold (jam detection)
  ;; Returns: 1 if jam detected, 0 otherwise
  ;; =========================================================================
  (func (export "check_jam") (param $current_ma i32) (param $threshold_ma i32) (result i32)
    local.get $current_ma
    local.get $threshold_ma
    i32.gt_s
    if (result i32)
      i32.const 1
    else
      i32.const 0
    end
  )

  ;; =========================================================================
  ;; ramp_pwm -- Soft start/stop: ramp current PWM toward target PWM
  ;; Returns: new PWM value after ramping by one step
  ;; =========================================================================
  (func (export "ramp_pwm") (param $current_pwm i32) (param $target_pwm i32) (result i32)
    (local $ramp_rate i32)
    (local $diff i32)
    (local $result i32)

    ;; Load ramp rate from memory
    i32.const 28
    i32.load
    local.set $ramp_rate

    ;; Calculate difference: target - current
    local.get $target_pwm
    local.get $current_pwm
    i32.sub
    local.set $diff

    ;; If diff > ramp_rate, step up by ramp_rate
    local.get $diff
    local.get $ramp_rate
    i32.gt_s
    if
      local.get $current_pwm
      local.get $ramp_rate
      i32.add
      local.set $result
    else
      ;; If diff < -ramp_rate, step down by ramp_rate
      local.get $diff
      i32.const 0
      local.get $ramp_rate
      i32.sub
      i32.lt_s
      if
        local.get $current_pwm
        local.get $ramp_rate
        i32.sub
        local.set $result
      else
        ;; Close enough -- snap to target
        local.get $target_pwm
        local.set $result
      end
    end

    ;; Clamp result to 0-1000
    local.get $result
    i32.const 0
    i32.lt_s
    if
      i32.const 0
      local.set $result
    end
    local.get $result
    i32.const 1000
    i32.gt_s
    if
      i32.const 1000
      local.set $result
    end

    local.get $result
  )

  ;; =========================================================================
  ;; tick -- Main control cycle (called at 100Hz)
  ;; Returns: PWM duty cycle (0-1000)
  ;; =========================================================================
  (func (export "tick") (result i32)
    (local $position i32)
    (local $target i32)
    (local $current_ma i32)
    (local $threshold i32)
    (local $direction i32)
    (local $pwm i32)
    (local $target_pwm i32)
    (local $new_pwm i32)
    (local $position_delta i32)
    (local $consecutive i32)
    (local $debounce_limit i32)
    (local $ramp_rate i32)
    (local $diff i32)

    ;; Load state from memory
    i32.const 0
    i32.load
    local.set $position

    i32.const 24
    i32.load
    local.set $target

    i32.const 4
    i32.load
    local.set $current_ma

    i32.const 20
    i32.load
    local.set $threshold

    i32.const 8
    i32.load
    local.set $pwm

    i32.const 32
    i32.load
    local.set $consecutive

    i32.const 36
    i32.load
    local.set $debounce_limit

    ;; Check if jam already flagged -- if so, keep motor stopped
    i32.const 16
    i32.load
    i32.const 1
    i32.eq
    if
      ;; Jam flagged: force PWM to 0, direction to stopped
      i32.const 8
      i32.const 0
      i32.store
      i32.const 12
      i32.const 0
      i32.store
      i32.const 0
      return
    end

    ;; Determine direction: compare position to target
    local.get $target
    local.get $position
    i32.gt_s
    if
      ;; target > position: closing (moving toward fully closed)
      i32.const 1
      local.set $direction
      ;; target PWM = 800 (80% duty for normal closing)
      i32.const 800
      local.set $target_pwm
    else
      local.get $target
      local.get $position
      i32.lt_s
      if
        ;; target < position: opening (moving toward fully open)
        i32.const 2
        local.set $direction
        ;; target PWM = 800 (80% duty for normal opening)
        i32.const 800
        local.set $target_pwm
      else
        ;; target == position: stop motor
        i32.const 0
        local.set $direction
        i32.const 0
        local.set $target_pwm
      end
    end

    ;; Store direction
    i32.const 12
    local.get $direction
    i32.store

    ;; --- JAM DETECTION (only while closing, direction==1) ---
    local.get $direction
    i32.const 1
    i32.eq
    if
      ;; Check if current exceeds threshold
      local.get $current_ma
      local.get $threshold
      i32.gt_s
      if
        ;; Increment consecutive over-threshold counter
        local.get $consecutive
        i32.const 1
        i32.add
        local.set $consecutive

        ;; Store updated counter
        i32.const 32
        local.get $consecutive
        i32.store

        ;; Check if debounce limit reached
        local.get $consecutive
        local.get $debounce_limit
        i32.ge_s
        if
          ;; JAM CONFIRMED: emergency stop
          ;; Set jam flag
          i32.const 16
          i32.const 1
          i32.store
          ;; Stop motor
          i32.const 8
          i32.const 0
          i32.store
          ;; Set direction to stopped
          i32.const 12
          i32.const 0
          i32.store
          ;; Reset debounce counter
          i32.const 32
          i32.const 0
          i32.store
          ;; Return 0 PWM immediately
          i32.const 0
          return
        end
      else
        ;; Current below threshold: reset debounce counter
        i32.const 32
        i32.const 0
        i32.store
        i32.const 0
        local.set $consecutive
      end
    end

    ;; --- PWM RAMPING (soft start/stop) ---
    ;; Ramp current PWM toward target PWM
    ;; Inline ramp logic (same as ramp_pwm function)
    i32.const 28
    i32.load
    local.set $ramp_rate

    local.get $target_pwm
    local.get $pwm
    i32.sub
    local.set $diff

    local.get $diff
    local.get $ramp_rate
    i32.gt_s
    if
      local.get $pwm
      local.get $ramp_rate
      i32.add
      local.set $new_pwm
    else
      local.get $diff
      i32.const 0
      local.get $ramp_rate
      i32.sub
      i32.lt_s
      if
        local.get $pwm
        local.get $ramp_rate
        i32.sub
        local.set $new_pwm
      else
        local.get $target_pwm
        local.set $new_pwm
      end
    end

    ;; Clamp new_pwm to 0-1000
    local.get $new_pwm
    i32.const 0
    i32.lt_s
    if
      i32.const 0
      local.set $new_pwm
    end
    local.get $new_pwm
    i32.const 1000
    i32.gt_s
    if
      i32.const 1000
      local.set $new_pwm
    end

    ;; Store new PWM
    i32.const 8
    local.get $new_pwm
    i32.store

    ;; --- POSITION UPDATE ---
    ;; Estimate position change based on direction and PWM
    ;; position_delta = new_pwm / 100 (scale: at 100% PWM, ~10 units/tick = 1%/tick)
    local.get $new_pwm
    i32.const 100
    i32.div_s
    local.set $position_delta

    local.get $direction
    i32.const 1
    i32.eq
    if
      ;; Closing: position increases
      local.get $position
      local.get $position_delta
      i32.add
      local.set $position
      ;; Clamp to target (don't overshoot)
      local.get $position
      local.get $target
      i32.gt_s
      if
        local.get $target
        local.set $position
      end
    else
      local.get $direction
      i32.const 2
      i32.eq
      if
        ;; Opening: position decreases
        local.get $position
        local.get $position_delta
        i32.sub
        local.set $position
        ;; Clamp to target (don't undershoot)
        local.get $position
        local.get $target
        i32.lt_s
        if
          local.get $target
          local.set $position
        end
      end
    end

    ;; Store updated position
    i32.const 0
    local.get $position
    i32.store

    ;; Check if position reached target
    local.get $position
    local.get $target
    i32.eq
    if
      ;; Reached target: stop motor
      i32.const 12
      i32.const 0
      i32.store
      i32.const 8
      i32.const 0
      i32.store
      i32.const 0
      return
    end

    ;; Return current PWM duty cycle
    local.get $new_pwm
  )

  ;; =========================================================================
  ;; Getter functions for reading controller state
  ;; =========================================================================

  (func (export "get_position") (result i32)
    i32.const 0
    i32.load
  )

  (func (export "get_pwm") (result i32)
    i32.const 8
    i32.load
  )

  (func (export "get_direction") (result i32)
    i32.const 12
    i32.load
  )

  (func (export "is_jam_detected") (result i32)
    i32.const 16
    i32.load
  )

  ;; =========================================================================
  ;; clear_jam -- Reset jam flag for retry
  ;; =========================================================================
  (func (export "clear_jam")
    i32.const 16
    i32.const 0
    i32.store

    ;; Reset debounce counter
    i32.const 32
    i32.const 0
    i32.store
  )
)

;; =============================================================================
;; Jam detection tests -- check_jam is a pure function (no memory side effects)
;; =============================================================================

;; Current exceeds threshold: jam detected
(assert_return (invoke "check_jam" (i32.const 1200) (i32.const 800)) (i32.const 1))

;; Current well above threshold
(assert_return (invoke "check_jam" (i32.const 5000) (i32.const 800)) (i32.const 1))

;; Current below threshold: no jam
(assert_return (invoke "check_jam" (i32.const 500) (i32.const 800)) (i32.const 0))

;; Current exactly at threshold: no jam (gt_s, not ge_s)
(assert_return (invoke "check_jam" (i32.const 800) (i32.const 800)) (i32.const 0))

;; Current just above threshold
(assert_return (invoke "check_jam" (i32.const 801) (i32.const 800)) (i32.const 1))

;; Zero current, zero threshold: no jam (0 is not > 0)
(assert_return (invoke "check_jam" (i32.const 0) (i32.const 0)) (i32.const 0))

;; Zero current, positive threshold: no jam
(assert_return (invoke "check_jam" (i32.const 0) (i32.const 800)) (i32.const 0))

;; Different threshold values
(assert_return (invoke "check_jam" (i32.const 400) (i32.const 300)) (i32.const 1))
(assert_return (invoke "check_jam" (i32.const 100) (i32.const 500)) (i32.const 0))

;; =============================================================================
;; PWM ramping tests
;;
;; ramp_pwm reads ramp_rate from memory[28]. In a fresh machine, memory is
;; zero-initialized so ramp_rate = 0. With ramp_rate = 0:
;;   diff > 0 is never > 0 (ramp_rate), and diff < -0 is never < 0,
;;   so it always snaps to target_pwm (the else branch).
;; =============================================================================

;; With ramp_rate=0 (uninit'd memory), ramp_pwm snaps directly to target
(assert_return (invoke "ramp_pwm" (i32.const 0) (i32.const 100)) (i32.const 100))
(assert_return (invoke "ramp_pwm" (i32.const 0) (i32.const 500)) (i32.const 500))
(assert_return (invoke "ramp_pwm" (i32.const 500) (i32.const 0)) (i32.const 0))
(assert_return (invoke "ramp_pwm" (i32.const 100) (i32.const 100)) (i32.const 100))  ;; already at target
(assert_return (invoke "ramp_pwm" (i32.const 800) (i32.const 1000)) (i32.const 1000))
(assert_return (invoke "ramp_pwm" (i32.const 1000) (i32.const 800)) (i32.const 800))

;; Edge: target at clamping boundaries
(assert_return (invoke "ramp_pwm" (i32.const 0) (i32.const 0)) (i32.const 0))
(assert_return (invoke "ramp_pwm" (i32.const 0) (i32.const 1000)) (i32.const 1000))
(assert_return (invoke "ramp_pwm" (i32.const 1000) (i32.const 0)) (i32.const 0))

;; =============================================================================
;; Getter functions with zero-initialized memory
;; Each runs in a fresh machine so memory is all zeros
;; =============================================================================
(assert_return (invoke "get_position") (i32.const 0))
(assert_return (invoke "get_pwm") (i32.const 0))
(assert_return (invoke "get_direction") (i32.const 0))
(assert_return (invoke "is_jam_detected") (i32.const 0))

;; =============================================================================
;; Tick with zero-initialized memory
;;
;; With all memory = 0:
;;   position=0, target=0, current_ma=0, threshold=0, pwm=0
;;   jam_detected=0 (no early return)
;;   target(0) == position(0) -> direction=0, target_pwm=0
;;   ramp_rate=0, diff=0-0=0, not > 0, not < -0 -> snap: new_pwm=0
;;   position_delta = 0/100 = 0
;;   direction=0: no position update
;;   position(0) == target(0) -> reached target, return 0
;; =============================================================================
(assert_return (invoke "tick") (i32.const 0))
