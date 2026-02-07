;; Shift tests for Synth
;; Tests SHL, SHR_S, SHR_U operations

(module
  ;; Shift left
  (func (export "shl") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.shl)

  ;; Shift right signed (arithmetic)
  (func (export "shr_s") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.shr_s)

  ;; Shift right unsigned (logical)
  (func (export "shr_u") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.shr_u)
)

;; SHL tests
(assert_return (invoke "shl" (i32.const 1) (i32.const 1)) (i32.const 2))
(assert_return (invoke "shl" (i32.const 1) (i32.const 0)) (i32.const 1))
(assert_return (invoke "shl" (i32.const 1) (i32.const 31)) (i32.const 0x80000000))
(assert_return (invoke "shl" (i32.const 1) (i32.const 32)) (i32.const 1))  ;; shift wraps at 32
(assert_return (invoke "shl" (i32.const 0xFF) (i32.const 4)) (i32.const 0xFF0))
(assert_return (invoke "shl" (i32.const 0x80000000) (i32.const 1)) (i32.const 0))

;; SHR_S tests (arithmetic shift - sign extends)
(assert_return (invoke "shr_s" (i32.const 4) (i32.const 1)) (i32.const 2))
(assert_return (invoke "shr_s" (i32.const 4) (i32.const 0)) (i32.const 4))
(assert_return (invoke "shr_s" (i32.const 0x80000000) (i32.const 1)) (i32.const 0xC0000000))
(assert_return (invoke "shr_s" (i32.const 0x80000000) (i32.const 31)) (i32.const 0xFFFFFFFF))
(assert_return (invoke "shr_s" (i32.const -1) (i32.const 1)) (i32.const -1))
(assert_return (invoke "shr_s" (i32.const 0x7FFFFFFF) (i32.const 1)) (i32.const 0x3FFFFFFF))

;; SHR_U tests (logical shift - zero extends)
(assert_return (invoke "shr_u" (i32.const 4) (i32.const 1)) (i32.const 2))
(assert_return (invoke "shr_u" (i32.const 4) (i32.const 0)) (i32.const 4))
(assert_return (invoke "shr_u" (i32.const 0x80000000) (i32.const 1)) (i32.const 0x40000000))
(assert_return (invoke "shr_u" (i32.const 0x80000000) (i32.const 31)) (i32.const 1))
(assert_return (invoke "shr_u" (i32.const 0xFFFFFFFF) (i32.const 1)) (i32.const 0x7FFFFFFF))
(assert_return (invoke "shr_u" (i32.const 0x7FFFFFFF) (i32.const 1)) (i32.const 0x3FFFFFFF))
