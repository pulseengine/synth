(module
  (memory $m0 1 1)
  (global $sp (mut i32) (i32.const 0x1000))
  (data (memory $m0) (i32.const 0x2000) "\11\11\11\11\22\22\22\22")
  (func (export "read0_static") (result i32)
    (i32.load $m0 (i32.const 0x2000)))
)
