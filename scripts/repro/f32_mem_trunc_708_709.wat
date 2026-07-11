(module
  ;; #708/#709 phase-1b f32 differential fixture (thumb-2 hard-float).
  ;;  * #709: `i32.trunc_f32_{s,u}` must TRAP (UDF) on NaN/±Inf/out-of-range —
  ;;    the domain guard precedes the (now provably exact) VCVT.
  ;;  * #708: `f32.load` (VLDR twin via LDR+VMOV bitcast) + the f32<->i32
  ;;    reinterpret bit-casts (pure VMOV).
  (memory 1)
  (export "mem" (memory 0))
  (func (export "trunc_s") (param f32) (result i32) local.get 0 i32.trunc_f32_s)
  (func (export "trunc_u") (param f32) (result i32) local.get 0 i32.trunc_f32_u)
  (func (export "load")    (param i32) (result f32) local.get 0 f32.load)
  (func (export "r2i")     (param f32) (result i32) local.get 0 i32.reinterpret_f32)
  (func (export "i2r")     (param i32) (result f32) local.get 0 f32.reinterpret_i32)
  (func (export "rt")      (param i32) (result i32)
        local.get 0 f32.reinterpret_i32 i32.reinterpret_f32))
