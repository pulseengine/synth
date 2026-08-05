;; v0.54 L2 (#851) — the aarch64 float-completion surface: the four classes the
;; VCR-SEL-005 third-backend op-parity oracle enumerated as Err(reason).
;;
;;   ROUNDING        f{32,64}.{ceil,floor,trunc,nearest}   -> FRINT{P,M,Z,N}
;;   I64_TO_FP       f{32,64}.convert_i64_{s,u}            -> SCVTF/UCVTF (x)
;;   TRAP_TRUNC_I64  i64.trunc_f{32,64}_{s,u}              -> guarded FCVTZ (x)
;;   FP_MEM          f{32,64}.{load,store}                 -> LDR/STR s|d
;;
;; The FP_MEM functions round-trip a value through linear memory so a wrong
;; width, a wrong register file or a dropped bounds check all show up as a
;; value/trap mismatch. Address 65532 is deliberately IN bounds for f32 and OUT
;; for f64 on this one-page memory.
(module
  (memory 1 1)

  ;; --- rounding ---
  (func (export "f32_ceil") (param f32) (result f32) (f32.ceil (local.get 0)))
  (func (export "f32_floor") (param f32) (result f32) (f32.floor (local.get 0)))
  (func (export "f32_trunc") (param f32) (result f32) (f32.trunc (local.get 0)))
  (func (export "f32_nearest") (param f32) (result f32) (f32.nearest (local.get 0)))
  (func (export "f64_ceil") (param f64) (result f64) (f64.ceil (local.get 0)))
  (func (export "f64_floor") (param f64) (result f64) (f64.floor (local.get 0)))
  (func (export "f64_trunc") (param f64) (result f64) (f64.trunc (local.get 0)))
  (func (export "f64_nearest") (param f64) (result f64) (f64.nearest (local.get 0)))

  ;; --- i64 -> float converts ---
  (func (export "f32_convert_i64_s") (param i64) (result f32)
    (f32.convert_i64_s (local.get 0)))
  (func (export "f32_convert_i64_u") (param i64) (result f32)
    (f32.convert_i64_u (local.get 0)))
  (func (export "f64_convert_i64_s") (param i64) (result f64)
    (f64.convert_i64_s (local.get 0)))
  (func (export "f64_convert_i64_u") (param i64) (result f64)
    (f64.convert_i64_u (local.get 0)))

  ;; --- TRAPPING i64-target truncations (the soundness-critical class) ---
  (func (export "i64_trunc_f32_s") (param f32) (result i64)
    (i64.trunc_f32_s (local.get 0)))
  (func (export "i64_trunc_f32_u") (param f32) (result i64)
    (i64.trunc_f32_u (local.get 0)))
  (func (export "i64_trunc_f64_s") (param f64) (result i64)
    (i64.trunc_f64_s (local.get 0)))
  (func (export "i64_trunc_f64_u") (param f64) (result i64)
    (i64.trunc_f64_u (local.get 0)))

  ;; --- FP linear memory (store then load back from the same address) ---
  (func (export "f32_mem_rt") (param i32 f32) (result f32)
    (f32.store (local.get 0) (local.get 1))
    (f32.load (local.get 0)))
  (func (export "f64_mem_rt") (param i32 f64) (result f64)
    (f64.store (local.get 0) (local.get 1))
    (f64.load (local.get 0)))
  ;; A non-zero static memarg offset: exercises the scaled-imm12 fold AND the
  ;; offset accounting inside the bounds constant K.
  (func (export "f32_mem_off") (param i32 f32) (result f32)
    (f32.store offset=16 (local.get 0) (local.get 1))
    (f32.load offset=16 (local.get 0)))
)
