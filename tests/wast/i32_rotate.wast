;; Rotate tests for Synth
;; Tests ROTL, ROTR operations

(module
  ;; Rotate left
  (func (export "rotl") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.rotl)

  ;; Rotate right
  (func (export "rotr") (param i32 i32) (result i32)
    local.get 0
    local.get 1
    i32.rotr)
)

;; ROTL tests
(assert_return (invoke "rotl" (i32.const 1) (i32.const 1)) (i32.const 2))
(assert_return (invoke "rotl" (i32.const 1) (i32.const 0)) (i32.const 1))
(assert_return (invoke "rotl" (i32.const 1) (i32.const 31)) (i32.const 0x80000000))
(assert_return (invoke "rotl" (i32.const 1) (i32.const 32)) (i32.const 1))  ;; full rotation
(assert_return (invoke "rotl" (i32.const 0x80000000) (i32.const 1)) (i32.const 1))
(assert_return (invoke "rotl" (i32.const 0xFF000000) (i32.const 8)) (i32.const 0x000000FF))
(assert_return (invoke "rotl" (i32.const 0xABCD1234) (i32.const 16)) (i32.const 0x1234ABCD))

;; ROTR tests
(assert_return (invoke "rotr" (i32.const 2) (i32.const 1)) (i32.const 1))
(assert_return (invoke "rotr" (i32.const 2) (i32.const 0)) (i32.const 2))
(assert_return (invoke "rotr" (i32.const 1) (i32.const 1)) (i32.const 0x80000000))
(assert_return (invoke "rotr" (i32.const 1) (i32.const 32)) (i32.const 1))  ;; full rotation
(assert_return (invoke "rotr" (i32.const 0x80000000) (i32.const 31)) (i32.const 1))
(assert_return (invoke "rotr" (i32.const 0x000000FF) (i32.const 8)) (i32.const 0xFF000000))
(assert_return (invoke "rotr" (i32.const 0xABCD1234) (i32.const 16)) (i32.const 0x1234ABCD))
