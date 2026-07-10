(module
  ;; #707: a multi-provider meld-fused shared-memory node. `meld fuse --memory
  ;; shared` merges the memories of N components but leaves each component's own
  ;; `__stack_pointer` global distinct — so the fused module carries N mutable
  ;; i32 globals ALL initialized to the same stack top (sp_init). They all point
  ;; into the ONE shared reservation. `--shadow-stack-size` used to refuse
  ;; ("N globals have init == sp_init; refusing") because it could not pick a
  ;; unique SP global; #707 re-bases the whole equivalence class (they alias).
  (memory (export "memory") 1)
  (global $sp0 (mut i32) (i32.const 4096))
  (global $sp1 (mut i32) (i32.const 4096))
  (global $sp2 (mut i32) (i32.const 4096))
  ;; An IMMUTABLE constant that merely COINCIDES with sp_init (4096). It is NOT a
  ;; shadow-stack pointer, so the shrink must leave it at 4096 — re-basing it
  ;; would corrupt a program constant. The re-base predicate keys on `mutable`,
  ;; not on the value, exactly so this slot is untouched.
  (global $konst i32 (i32.const 4096))
  (func (export "f0") (param $v i32) (result i32)
    (local $s i32)
    (local.set $s (i32.sub (global.get $sp0) (i32.const 16)))
    (global.set $sp0 (local.get $s))
    (i32.store (local.get $s) (local.get $v))
    (global.set $sp0 (i32.add (local.get $s) (i32.const 16)))
    (i32.load (local.get $s)))
  (func (export "f1") (param $v i32) (result i32)
    (local $s i32)
    (local.set $s (i32.sub (global.get $sp1) (i32.const 16)))
    (global.set $sp1 (local.get $s))
    (i32.store (local.get $s) (local.get $v))
    (global.set $sp1 (i32.add (local.get $s) (i32.const 16)))
    (i32.load (local.get $s)))
  (func (export "f2") (param $v i32) (result i32)
    (local $s i32)
    (local.set $s (i32.sub (global.get $sp2) (i32.const 16)))
    (global.set $sp2 (local.get $s))
    (i32.store (local.get $s) (local.get $v))
    (global.set $sp2 (i32.add (local.get $s) (i32.const 16)))
    (i32.load (local.get $s)))
  ;; reads the immutable constant so its slot is materialized and reachable.
  (func (export "getk") (result i32) (global.get $konst)))
