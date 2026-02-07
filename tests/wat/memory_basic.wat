;; Basic memory load/store test for Synth
;; Tests that R11-based memory addressing works correctly

(module
  ;; Declare 1 page of linear memory (64KB)
  (memory 1)

  ;; Test: store value, load it back
  ;; store_load(addr, value) -> value
  (func (export "store_load") (param $addr i32) (param $value i32) (result i32)
    ;; Store value at addr
    (i32.store (local.get $addr) (local.get $value))
    ;; Load and return
    (i32.load (local.get $addr))
  )

  ;; Test: store and load with offset
  ;; store_load_offset(addr, value) -> value
  (func (export "store_load_offset") (param $addr i32) (param $value i32) (result i32)
    ;; Store value at addr+4
    (i32.store offset=4 (local.get $addr) (local.get $value))
    ;; Load from addr+4
    (i32.load offset=4 (local.get $addr))
  )

  ;; Test: simple constant store/load at fixed address
  ;; fixed_test() -> 42
  (func (export "fixed_test") (result i32)
    ;; Store 42 at address 0
    (i32.store (i32.const 0) (i32.const 42))
    ;; Load from address 0
    (i32.load (i32.const 0))
  )
)
