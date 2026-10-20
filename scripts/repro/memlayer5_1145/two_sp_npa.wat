;; meld --domain shape: one __stack_pointer per domain; domain 1's SP init is
;; LARGER than domain 0's and still <= memory 0's 64 KiB.
(module
  (memory $m0 1 1)
  (memory $m1 2 2)
  (global $sp0 (mut i32) (i32.const 0x1000))
  (global $sp1 (mut i32) (i32.const 0x8000))
  (data (memory $m0) (i32.const 0x2000) "\11\11\11\11")
  (data (memory $m1) (i32.const 0x7ff0) "\ee\ee\ee\ee")
  ;; domain-1 frame read: the word just below domain 1's stack top, in MEMORY 1
  (func (export "d1_frame_peek") (result i32)
    (i32.load $m1 (i32.sub (global.get $sp1) (i32.const 16))))
)
