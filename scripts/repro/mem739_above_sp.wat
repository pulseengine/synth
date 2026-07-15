(module
  ;; #739: meld-fused shared-memory geometry — 17-page (1088 KiB) linear
  ;; memory, one __stack_pointer global init 0x100000 (1 MiB), and statics
  ;; ABOVE sp_init (meld `--memory shared` places a fused component's data
  ;; above the shared SP).
  ;;
  ;; The access shape is the wit-bindgen byte-copy one: a DYNAMIC index in a
  ;; register plus a STATIC-REGION memarg offset on a sub-word load/store.
  ;; Pre-fix the selector lowered these through the raw
  ;; `[R11 + addr + #offset]` path, baking the 1 MiB linmem offset as a plain
  ;; `movw/movt ip` immediate (NO relocation) — invisible to the
  ;; `--shadow-stack-size` rebase (#678) and to the post-link in-range
  ;; oracle, i.e. the #739 silent OOB miscompile.
  (memory (export "memory") 17)
  (global $sp (mut i32) (i32.const 1048576))
  ;; An initialized (data) segment ABOVE sp_init at 0x100020 (the "log
  ;; buffer that correctly lives in .data").
  (data (i32.const 1048608) "\11\22\33\44")
  ;; BSS static above sp_init at 0x10000C: store a computed byte through the
  ;; dynamic-index + static-offset shape, then read it back.
  (func (export "run") (param i32) (result i32)
    local.get 0
    local.get 0
    i32.const 2
    i32.mul
    i32.const 43
    i32.add
    i32.store8 offset=1048588
    local.get 0
    i32.load8_u offset=1048588)
  ;; .data static above sp_init: byte read from the initialized segment.
  (func (export "peek_data") (param i32) (result i32)
    local.get 0
    i32.load8_u offset=1048608))
