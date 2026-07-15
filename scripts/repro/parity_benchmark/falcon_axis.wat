;; #735 parity benchmark — falcon-style f32 kernel (one complementary-filter
;; axis update, the shape at the heart of the falcon flight loop):
;;
;;   angle' = 0.98 * (angle + gyro * dt) + 0.02 * accel_angle      (dt = 5 ms)
;;
;; Faithful to the falcon f32 surface shipped in v0.40/v0.41 (#708/#719/#712):
;; genuine f32 params through the AAPCS-VFP argument pool (s0..s2), f32.mul /
;; f32.add arithmetic, f32 result in s0. Deliberately mul/add only — wasm has
;; no fused-multiply-add, so a bit-exact-vs-wasmtime compiler MUST keep the
;; intermediate rounding steps (see the vfma note in
;; artifacts/parity-benchmark.md: the native baseline is allowed contractions
;; wasm semantics forbid).
;;
;; Native C twin: falcon_axis.c (same expression, same constants).
;; Requires a hardware-FPU target: --target cortex-m4f (GI-FPU-002 declines
;; soft-float targets loudly).
(module
  (func (export "falcon_axis") (param $angle f32) (param $gyro f32) (param $accel f32) (result f32)
    local.get $angle
    local.get $gyro
    f32.const 0.005
    f32.mul
    f32.add
    f32.const 0.98
    f32.mul
    local.get $accel
    f32.const 0.02
    f32.mul
    f32.add))
