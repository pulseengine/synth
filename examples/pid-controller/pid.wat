;; PID Controller - Proportional-Integral-Derivative Control
;;
;; Safety-critical control algorithm commonly used in:
;; - Automotive cruise control
;; - Motor speed control
;; - Temperature regulation
;; - Flight control systems
;;
;; This demonstrates Synth's benefits:
;; 1. Formally verified compilation (no optimizer bugs)
;; 2. Bounded arithmetic (no undefined behavior)
;; 3. Zero-overhead native code
;;
;; Algorithm:
;;   error = setpoint - measurement
;;   integral += error * dt
;;   derivative = (error - prev_error) / dt
;;   output = Kp*error + Ki*integral + Kd*derivative

(module
  ;; PID controller update function
  ;;
  ;; Params:
  ;;   $setpoint    - desired target value
  ;;   $measurement - current measured value
  ;;   $prev_error  - error from previous iteration (for derivative)
  ;;   $integral    - accumulated error (for integral term)
  ;;   $dt          - time step in seconds
  ;;   $kp          - proportional gain
  ;;   $ki          - integral gain
  ;;   $kd          - derivative gain
  ;;
  ;; Returns:
  ;;   control output (to be applied to system)
  ;;
  ;; Note: Caller must maintain prev_error and integral state between calls
  ;;
  (func $pid_update
    (param $setpoint f32)
    (param $measurement f32)
    (param $prev_error f32)
    (param $integral f32)
    (param $dt f32)
    (param $kp f32)
    (param $ki f32)
    (param $kd f32)
    (result f32)

    (local $error f32)
    (local $new_integral f32)
    (local $derivative f32)
    (local $p_term f32)
    (local $i_term f32)
    (local $d_term f32)
    (local $output f32)

    ;; Calculate error = setpoint - measurement
    local.get $setpoint
    local.get $measurement
    f32.sub
    local.set $error

    ;; Calculate new_integral = integral + error * dt
    local.get $integral
    local.get $error
    local.get $dt
    f32.mul
    f32.add
    local.set $new_integral

    ;; Calculate derivative = (error - prev_error) / dt
    local.get $error
    local.get $prev_error
    f32.sub
    local.get $dt
    f32.div
    local.set $derivative

    ;; P term = Kp * error
    local.get $kp
    local.get $error
    f32.mul
    local.set $p_term

    ;; I term = Ki * new_integral
    local.get $ki
    local.get $new_integral
    f32.mul
    local.set $i_term

    ;; D term = Kd * derivative
    local.get $kd
    local.get $derivative
    f32.mul
    local.set $d_term

    ;; Output = P + I + D
    local.get $p_term
    local.get $i_term
    f32.add
    local.get $d_term
    f32.add
    local.set $output

    ;; Return control output
    local.get $output
  )

  ;; Helper: Calculate current error (for state management)
  (func $pid_error
    (param $setpoint f32)
    (param $measurement f32)
    (result f32)

    local.get $setpoint
    local.get $measurement
    f32.sub
  )

  ;; Helper: Update integral (for state management)
  (func $pid_integral
    (param $prev_integral f32)
    (param $error f32)
    (param $dt f32)
    (result f32)

    local.get $prev_integral
    local.get $error
    local.get $dt
    f32.mul
    f32.add
  )

  (export "pid_update" (func $pid_update))
  (export "pid_error" (func $pid_error))
  (export "pid_integral" (func $pid_integral))
)
