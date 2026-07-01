;; #538 milestone-1b — the aarch64 integer-subset acceptance module. Each export
;; is a leaf i32 function the milestone-1 A64 selector lowers (params in w0..,
;; add/sub/mul/and/or/xor + const, result to w0, ret). The differential runs each
;; under unicorn UC_ARCH_ARM64 and diffs wasmtime.
(module
  (func (export "add") (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1)))
  (func (export "muladd") (param i32 i32 i32) (result i32)
    (i32.add (i32.mul (local.get 0) (local.get 1)) (local.get 2)))
  (func (export "const_sub") (param i32) (result i32)
    (i32.sub (local.get 0) (i32.const 7)))
  (func (export "xor_or") (param i32 i32) (result i32)
    (i32.or (i32.xor (local.get 0) (local.get 1)) (local.get 0))))
