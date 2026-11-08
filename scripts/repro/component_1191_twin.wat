;; #1191 control: shape 4's bodies as ONE core module (g() = 101).
(module
  (func $f (export "f") (result i32) i32.const 1)
  (func (result i32) i32.const 2)
  (func (export "g") (result i32) call $f i32.const 100 i32.add))
