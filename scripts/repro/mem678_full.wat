(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 4096))
  (data (i32.const 4160) "\2a\00\00\00")
  (func (export "run") (param i32) (result i32) (local $slot i32)
    ;; shadow-stack roundtrip: store param at [sp-4], read back
    global.get $sp
    i32.const 4
    i32.sub
    local.tee $slot
    local.get 0
    i32.store
    ;; bss static at 4200: store param+1, read back
    i32.const 4200
    local.get 0
    i32.const 1
    i32.add
    i32.store
    ;; sum = data-seg(42) + bss(param+1) + stack(param)
    i32.const 4160
    i32.load
    i32.const 4200
    i32.load
    i32.add
    local.get $slot
    i32.load
    i32.add))
