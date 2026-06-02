(module
  ;; #209 Opt 1 regression fixture: constant-divisor strength reduction +
  ;; dead trap-guard elision. Each export divides/remainders its single i32
  ;; param by a compile-time constant, exercising every lowered form:
  ;;   pow2 div_u -> LSR, non-pow2 -> guard-elided UDIV, /1 -> MOV identity,
  ;;   2^31 -> LSR #31, rem_u -> guard-elided UDIV+MLS, %1 -> MOV #0,
  ;;   signed -> both guards elided when divisor != 0,-1.
  (func (export "divu_pow2")   (param i32) (result i32) local.get 0 i32.const 8          i32.div_u)
  (func (export "divu_500")    (param i32) (result i32) local.get 0 i32.const 500        i32.div_u)
  (func (export "divu_7")      (param i32) (result i32) local.get 0 i32.const 7          i32.div_u) ;; a=true,s=3
  (func (export "divu_641")    (param i32) (result i32) local.get 0 i32.const 641        i32.div_u) ;; a=false,s=0
  (func (export "divu_smax")   (param i32) (result i32) local.get 0 i32.const 0x7FFFFFFF i32.div_u) ;; a=true,s=31
  (func (export "divu_one")    (param i32) (result i32) local.get 0 i32.const 1          i32.div_u)
  (func (export "divu_2e31")   (param i32) (result i32) local.get 0 i32.const 0x80000000 i32.div_u)
  (func (export "remu_500")    (param i32) (result i32) local.get 0 i32.const 500        i32.rem_u)
  (func (export "remu_one")    (param i32) (result i32) local.get 0 i32.const 1          i32.rem_u)
  (func (export "divs_5")      (param i32) (result i32) local.get 0 i32.const 5          i32.div_s)
  (func (export "divs_neg7")   (param i32) (result i32) local.get 0 i32.const -7         i32.div_s)
  (func (export "rems_5")      (param i32) (result i32) local.get 0 i32.const 5          i32.rem_s)
  (func (export "divs_one")    (param i32) (result i32) local.get 0 i32.const 1          i32.div_s)
)
