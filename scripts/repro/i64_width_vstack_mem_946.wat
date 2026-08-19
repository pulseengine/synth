;; #946 — the bulk-memory half of the i64-width vstack drift (see
;; i64_width_vstack_946.wat for the class). `memory.copy`/`memory.fill` pop
;; (dst, src/val, len) = 3 operands; the old `wasm_stack_effect` wildcard
;; absorbed them as (0, 0), leaving three stale width entries — the i64 local
;; set right after was inferred i32 and single-word stored (executed pre-fix:
;; returned 0 where wasmtime returns 1, unicorn cortex-m4 --relocatable).
;;
;; Separate fixture because the memory section excludes a module from the
;; corpus sweep's execution phase (unicorn would read zeros where wasmtime
;; reads the image); this file still gets Phase-A compile coverage, and the
;; execution-level pin lives in the unit tests
;; (crates/synth-synthesis/tests/i64_width_vstack_946.rs).
(module
  (memory 1)

  (func (export "f_memcopy") (result i32)
    (local $x i64)
    i64.const 0x100000005
    i32.const 0
    i32.const 16
    i32.const 4
    memory.copy
    local.set $x
    local.get $x
    i64.const 32
    i64.shr_u
    i32.wrap_i64)

  (func (export "f_memfill") (result i32)
    (local $x i64)
    i64.const 0x100000005
    i32.const 0
    i32.const 0xAB
    i32.const 4
    memory.fill
    local.set $x
    local.get $x
    i64.const 32
    i64.shr_u
    i32.wrap_i64))
