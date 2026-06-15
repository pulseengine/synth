(module
  (memory (export "memory") 1)
  (global $sp (mut i32) (i32.const 65536))
  ;; sret-style: write a 16-byte result through param0 via memory.copy from a source.
  (func (export "writer") (param $dst i32) (param $a i32)
    (local $src i32)
    (local.set $src (i32.const 2048))
    ;; build a 16-byte source block
    (i32.store (local.get $src) (local.get $a))
    (i32.store offset=4 (local.get $src) (i32.const 0xAA))
    (i32.store offset=8 (local.get $src) (local.get $a))
    (i32.store offset=12 (local.get $src) (local.get $a))
    ;; copy 16 bytes from src to dst (the sret pointer) — THE sret write
    (memory.copy (local.get $dst) (local.get $src) (i32.const 16))))
