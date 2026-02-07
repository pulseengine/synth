;; i64 shift tests for Synth
;; Tests 64-bit integer shift operations on ARM Cortex-M (32-bit)
;; On ARM Thumb-2: 64-bit shifts require multi-instruction sequences
;; operating on register pairs R0:R1 (value) with shift amount from R2

(module
  ;; 64-bit shift left
  (func (export "shl") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.shl)

  ;; 64-bit arithmetic shift right (signed)
  (func (export "shr_s") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.shr_s)

  ;; 64-bit logical shift right (unsigned)
  (func (export "shr_u") (param i64 i64) (result i64)
    local.get 0
    local.get 1
    i64.shr_u)
)

;; ===== i64.shl tests =====
;; Shift by 0 (identity)
(assert_return (invoke "shl" (i64.const 1) (i64.const 0)) (i64.const 1))
;; Small shifts within low word
(assert_return (invoke "shl" (i64.const 1) (i64.const 1)) (i64.const 2))
(assert_return (invoke "shl" (i64.const 1) (i64.const 4)) (i64.const 16))
(assert_return (invoke "shl" (i64.const 1) (i64.const 31)) (i64.const 0x80000000))
;; Shift crossing 32-bit boundary (low -> high word)
(assert_return (invoke "shl" (i64.const 1) (i64.const 32)) (i64.const 0x100000000))
(assert_return (invoke "shl" (i64.const 1) (i64.const 33)) (i64.const 0x200000000))
(assert_return (invoke "shl" (i64.const 1) (i64.const 63)) (i64.const 0x8000000000000000))
;; Shift by 0 with larger value
(assert_return (invoke "shl" (i64.const 0x100000000) (i64.const 0)) (i64.const 0x100000000))
;; Shift amount masked to 6 bits (WASM spec: shift mod 64)
(assert_return (invoke "shl" (i64.const 1) (i64.const 64)) (i64.const 1))
;; Multi-bit value shift
(assert_return (invoke "shl" (i64.const 0xFF) (i64.const 8)) (i64.const 0xFF00))

;; ===== i64.shr_s tests =====
;; Shift by 0 (identity)
(assert_return (invoke "shr_s" (i64.const 4) (i64.const 0)) (i64.const 4))
;; Small shifts
(assert_return (invoke "shr_s" (i64.const 4) (i64.const 1)) (i64.const 2))
(assert_return (invoke "shr_s" (i64.const 16) (i64.const 4)) (i64.const 1))
;; Shift from high word to low word
(assert_return (invoke "shr_s" (i64.const 0x100000000) (i64.const 32)) (i64.const 1))
(assert_return (invoke "shr_s" (i64.const 0x200000000) (i64.const 33)) (i64.const 1))
;; Signed: negative value preserves sign
(assert_return (invoke "shr_s" (i64.const -1) (i64.const 1)) (i64.const -1))
(assert_return (invoke "shr_s" (i64.const -2) (i64.const 1)) (i64.const -1))
(assert_return (invoke "shr_s" (i64.const -1024) (i64.const 10)) (i64.const -1))
;; Shift amount masked to 6 bits (WASM spec: shift mod 64)
(assert_return (invoke "shr_s" (i64.const 4) (i64.const 64)) (i64.const 4))

;; ===== i64.shr_u tests =====
;; Shift by 0 (identity)
(assert_return (invoke "shr_u" (i64.const 4) (i64.const 0)) (i64.const 4))
;; Small shifts
(assert_return (invoke "shr_u" (i64.const 4) (i64.const 1)) (i64.const 2))
(assert_return (invoke "shr_u" (i64.const 16) (i64.const 4)) (i64.const 1))
;; Shift from high word to low word
(assert_return (invoke "shr_u" (i64.const 0x100000000) (i64.const 32)) (i64.const 1))
;; Unsigned: high bit shifts in zeros (not sign-extend)
(assert_return (invoke "shr_u" (i64.const 0x8000000000000000) (i64.const 1)) (i64.const 0x4000000000000000))
(assert_return (invoke "shr_u" (i64.const 0x8000000000000000) (i64.const 63)) (i64.const 1))
(assert_return (invoke "shr_u" (i64.const 0xFFFFFFFFFFFFFFFF) (i64.const 32)) (i64.const 0xFFFFFFFF))
;; Shift amount masked to 6 bits (WASM spec: shift mod 64)
(assert_return (invoke "shr_u" (i64.const 4) (i64.const 64)) (i64.const 4))
