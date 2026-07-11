(module
  ;; GI-FPU-002 (#619/#369) phase-1 f32 hard-float differential fixture.
  ;; All functions take hard-float (AAPCS-VFP) f32 args in S0/S1 and return in
  ;; S0 (or R0 for the i32-result trunc/compare). Exercised on FPU-boundary
  ;; values (0.0, 1.5, -2.25, large, denormal-ish) against wasmtime.
  (func (export "fadd") (param f32 f32) (result f32) local.get 0 local.get 1 f32.add)
  (func (export "fsub") (param f32 f32) (result f32) local.get 0 local.get 1 f32.sub)
  (func (export "fmul") (param f32 f32) (result f32) local.get 0 local.get 1 f32.mul)
  (func (export "fdiv") (param f32 f32) (result f32) local.get 0 local.get 1 f32.div)
  (func (export "flt")  (param f32 f32) (result i32) local.get 0 local.get 1 f32.lt)
  (func (export "fgt")  (param f32 f32) (result i32) local.get 0 local.get 1 f32.gt)
  ;; #712: all SIX comparisons go through encode_thumb_f32_compare — the
  ;; flag-clobber (MOVS after VMRS) hit every one, but the 619 harness only
  ;; exercised flt/fgt, so eq/ne/le/ge were fixed-but-ungated. Cover all six.
  (func (export "feq")  (param f32 f32) (result i32) local.get 0 local.get 1 f32.eq)
  (func (export "fne")  (param f32 f32) (result i32) local.get 0 local.get 1 f32.ne)
  (func (export "fle")  (param f32 f32) (result i32) local.get 0 local.get 1 f32.le)
  (func (export "fge")  (param f32 f32) (result i32) local.get 0 local.get 1 f32.ge)
  (func (export "trunc_s") (param f32) (result i32) local.get 0 i32.trunc_f32_s)
  (func (export "conv_s")  (param i32) (result f32) local.get 0 f32.convert_i32_s)
  (func (export "conv_u")  (param i32) (result f32) local.get 0 f32.convert_i32_u))
