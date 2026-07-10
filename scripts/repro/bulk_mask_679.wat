(module
  ;; #679 — `--safety-bounds mask` was a silent no-op for memory.copy /
  ;; memory.fill: the bulk lowering was emitted byte-identical to `none`
  ;; (no fold, no clamp) while the safety manifest still attested `mask`.
  (memory 1)
  (export "memory" (memory 0))

  ;; issue reproducer: copy 1 byte [100] -> dst=local0, read back [16].
  ;; With mem_size=4096 and dst=4112: masked dst folds 4112&4095=16 -> 171.
  ;; Escaped (pre-fix): raw write at 4112, [16] untouched -> 0.
  (func (export "cpy_esc") (param i32 i32) (result i32)
    (i32.store8 (i32.const 100) (i32.const 171))
    (i32.store8 (i32.const 16) (i32.const 0))
    (memory.copy (local.get 0) (i32.const 100) (i32.const 1))
    (i32.load8_u (i32.const 16)))

  ;; fill escape: fill 1 byte 238 at dst=local0, read back [24].
  (func (export "fil_esc") (param i32 i32) (result i32)
    (i32.store8 (i32.const 24) (i32.const 0))
    (memory.fill (local.get 0) (i32.const 238) (i32.const 1))
    (i32.load8_u (i32.const 24)))

  ;; src escape: stage 205 at [40]; copy 1 byte src=local0 -> [8]; read [8].
  ;; With src=4136: masked src folds 4136&4095=40 -> 205.
  (func (export "cpy_src_esc") (param i32 i32) (result i32)
    (i32.store8 (i32.const 40) (i32.const 205))
    (i32.store8 (i32.const 8) (i32.const 0))
    (memory.copy (i32.const 8) (local.get 0) (i32.const 1))
    (i32.load8_u (i32.const 8)))

  ;; len clamp: stage 119 at [3]; copy len=local1 bytes [0..) -> [4092..).
  ;; With len=400 and mem_size=4096: len clamps to 4096-4092=4 — the copy
  ;; ends exactly at the bound; read back [4095] (= staged byte [3]).
  (func (export "cpy_clamp") (param i32 i32) (result i32)
    (i32.store8 (i32.const 3) (i32.const 119))
    (memory.copy (i32.const 4092) (i32.const 0) (local.get 1))
    (i32.load8_u (i32.const 4095))))
