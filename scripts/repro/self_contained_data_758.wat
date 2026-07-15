(module
  (memory (export "mem") 1)
  ;; Two active data segments at distinct offsets, plus a deliberately
  ;; UNINITIALIZED region (offset 512) that must read back as zero.
  (data (i32.const 256) "\11\22\33\44\55\66\77\88")   ;; seg A @256
  ;; seg C overlaps seg A's last byte: WASM instantiation is in-order, so the
  ;; LATER segment wins — byte @263 becomes 0x99 (was 0x88). Pins overlap order.
  (data (i32.const 263) "\99\aa")                     ;; seg C @263 (overwrites 263)
  (data (i32.const 300) "\de\ad\be\ef")               ;; seg B @300 (unaligned start)
  ;; loads from the initialized regions
  (func (export "lo")  (result i32) (i32.load (i32.const 256)))  ;; 0x44332211
  (func (export "hi")  (result i32) (i32.load (i32.const 260)))  ;; 0x88776655
  (func (export "segB") (result i32) (i32.load (i32.const 300))) ;; 0xefbeadde
  ;; byte load from the middle of seg A
  (func (export "byteC") (result i32) (i32.load8_u (i32.const 258))) ;; 0x33
  ;; byte @263 — overlap discriminator: seg C (later) overwrote seg A here
  (func (export "ovl") (result i32) (i32.load8_u (i32.const 263)))   ;; 0x99
  ;; a load from a region NO segment initializes: must be zero
  (func (export "zero") (result i32) (i32.load (i32.const 512)))     ;; 0
)
