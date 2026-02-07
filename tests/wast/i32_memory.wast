;; Basic i32 memory tests for Synth
;; These tests verify that Synth correctly compiles i32.load and i32.store
;; operations and produces correct results when executed on Cortex-M
;;
;; Linear memory is mapped to SRAM starting at 0x20000100 on the target.

(module
  (memory 1)  ;; 1 page = 64KB linear memory

  ;; Store a value at an address, then load it back
  ;; This is the simplest possible memory roundtrip test
  (func (export "store_load") (param i32 i32) (result i32)
    local.get 0    ;; address
    local.get 1    ;; value
    i32.store      ;; store value at address
    local.get 0    ;; address
    i32.load)      ;; load from address (should return stored value)
)

;; Basic roundtrip: store 42 at address 0, load it back
(assert_return (invoke "store_load" (i32.const 0) (i32.const 42)) (i32.const 42))

;; Store at offset 4 (word-aligned)
(assert_return (invoke "store_load" (i32.const 4) (i32.const 100)) (i32.const 100))

;; Store zero
(assert_return (invoke "store_load" (i32.const 0) (i32.const 0)) (i32.const 0))

;; Store negative value (i32 is signed)
(assert_return (invoke "store_load" (i32.const 8) (i32.const -1)) (i32.const -1))

;; Store large positive value
(assert_return (invoke "store_load" (i32.const 12) (i32.const 0x7FFFFFFF)) (i32.const 0x7FFFFFFF))
