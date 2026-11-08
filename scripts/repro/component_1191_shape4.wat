;; #1191 shape 4: two plain core modules in one component. wasmtime: g() = 101.
;; Pre-#1191 the flattened decode bound `g` to the body `i32.const 2`.
;; Assembles to sha256 c64f6bd0…03f3, the input hash in the fused fixture's
;; meld attestation.
(component
  (core module $A (func (export "f") (result i32) i32.const 1))
  (core module $B
    (import "x" "f" (func $f (result i32)))
    (func (result i32) i32.const 2)
    (func (export "g") (result i32) call $f i32.const 100 i32.add))
  (core instance $a (instantiate $A))
  (core instance $b (instantiate $B (with "x" (instance $a))))
  (func $g (result u32) (canon lift (core func $b "g")))
  (export "g" (func $g)))
