(module
  (memory (export "mem") 1)
  ;; load at offset > 4095 (0x2000 = 8192)
  (func (export "load_hi") (param i32) (result i32)
    local.get 0
    i32.load offset=0x2000)
  ;; store at offset > 4095 then read it back
  (func (export "store_hi") (param i32) (param i32)
    local.get 0
    local.get 1
    i32.store offset=0x2000)
)
