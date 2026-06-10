(module
  ;; #237 (gale, mutex-on-silicon): the gmutex shadow-stack shape — a mutable
  ;; __stack_pointer global initialized by wasm-ld to the stack top (4096),
  ;; moved down for a frame, stored through, read back, and restored.
  (memory (export "memory") 1)
  (global $__stack_pointer (mut i32) (i32.const 4096))
  (data (i32.const 4096) "\2a\00\00\00")
  (func (export "frame_roundtrip") (param $v i32) (result i32)
    (local $sp i32)
    ;; prologue: sp = SP - 16; SP = sp
    (local.set $sp (i32.sub (global.get $__stack_pointer) (i32.const 16)))
    (global.set $__stack_pointer (local.get $sp))
    ;; spill v into the frame, read it back
    (i32.store (local.get $sp) (local.get $v))
    ;; epilogue: SP = sp + 16
    (global.set $__stack_pointer (i32.add (local.get $sp) (i32.const 16)))
    (i32.load (local.get $sp))))
