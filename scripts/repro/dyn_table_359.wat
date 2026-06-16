(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 65536))
  ;; action->value table at the high .rodata offset (the #359 pattern)
  (data (i32.const 65536) "\0a\00\00\00\14\00\00\00\1e\00\00\00\28\00\00\00")  ;; [10,20,30,40]
  (func (export "lookup") (param $i i32) (result i32)
    (i32.load offset=65536 (i32.shl (local.get $i) (i32.const 2)))))  ;; table[i]
