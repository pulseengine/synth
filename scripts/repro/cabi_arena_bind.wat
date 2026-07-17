;; #418 — the wit-bindgen `cabi-realloc-extern` / meld-dissolve shape:
;; `cabi_realloc` stays exported but routes to the embedder-provided
;; `env::__cabi_arena_realloc` arena import (grow-free — no memory.grow).
;;
;; Layout mirrors a Rust/wasm-ld component: mutable __stack_pointer global,
;; exported __data_end/__heap_base layout globals, an active data segment.
;; synth's self-contained binding must place its arena ABOVE all of these.
;;
;; The test exports return POINTER-INDEPENDENT observables (preserved
;; contents, disjointness, alignment residue, the (0,0,align,0) -> align
;; contract case), so the differential passes only on contract-conformant
;; allocator SEMANTICS — never on both sides happening to pick the same base.
(module
  (import "env" "__cabi_arena_realloc"
    (func $arena (param i32 i32 i32 i32) (result i32)))
  (memory (export "memory") 1)
  (global $__stack_pointer (mut i32) (i32.const 4096))
  (global $__data_end i32 (i32.const 5136))
  (global $__heap_base i32 (i32.const 6144))
  (export "__data_end" (global 1))
  (export "__heap_base" (global 2))
  (data (i32.const 5120) "\01\02\03\04\05\06\07\08\09\0a\0b\0c\0d\0e\0f\10")

  ;; canonical realloc, routed to the arena (the cabi-realloc-extern body)
  (func (export "cabi_realloc") (param i32 i32 i32 i32) (result i32)
    local.get 0
    local.get 1
    local.get 2
    local.get 3
    call $arena)

  ;; contract: old_len == 0 && new_len == 0 -> returns align verbatim
  (func (export "case_zero") (param i32) (result i32)
    i32.const 0
    i32.const 0
    local.get 0
    i32.const 0
    call $arena)

  ;; RawVec-grow: alloc 4, store, realloc to 8 — old contents PRESERVED
  (func (export "grow_preserves") (result i32)
    (local i32 i32)
    (local.set 0
      (call $arena (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 4)))
    (i32.store (local.get 0) (i32.const 0x11223344))
    (local.set 1
      (call $arena (local.get 0) (i32.const 4) (i32.const 4) (i32.const 8)))
    (i32.store offset=4 (local.get 1) (i32.const 0x55667788))
    (i32.add
      (i32.load (local.get 1))
      (i32.load offset=4 (local.get 1))))

  ;; two live allocations must not alias
  (func (export "disjoint") (result i32)
    (local i32 i32)
    (local.set 0
      (call $arena (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 4)))
    (i32.store (local.get 0) (i32.const 7))
    (local.set 1
      (call $arena (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 4)))
    (i32.store (local.get 1) (i32.const 9))
    (i32.add
      (i32.mul (i32.load (local.get 0)) (i32.const 100))
      (i32.load (local.get 1))))

  ;; returned pointer honors the requested alignment (residue must be 0)
  (func (export "align_ok") (param i32) (result i32)
    (i32.and
      (call $arena (i32.const 0) (i32.const 0) (local.get 0) (i32.const 3))
      (i32.sub (local.get 0) (i32.const 1))))

  ;; bounded arena: exhaustion TRAPS (never memory.grow)
  (func (export "exhaust") (result i32)
    (call $arena (i32.const 0) (i32.const 0) (i32.const 4) (i32.const 0x40000000)))
)
