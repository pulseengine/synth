;; #499 — optimized-path spill frame must be deallocated on EVERY return.
;;
;; Two shapes that drive the flag-off `Opcode::Const` oldest-vreg eviction
;; spill (optimizer_bridge.rs) so the bridge emits a `sub sp,#N` spill frame:
;;
;;  * `min_fields` — the MINIMAL straight-line shape: five i32.stores keep
;;    10 const vregs live past the R4-R11/R3 pool, forcing at least one
;;    spill slot. No control flow, no explicit `return` — the function falls
;;    off the end, so its return is APPENDED by the bridge. Before the fix
;;    the appended return had no `add sp,#N`, so the `pop {…,pc}` epilogue
;;    (#490) read PC from a spill slot.
;;  * `nested` — the original #499 reproducer: same spill pressure UNDER
;;    control flow (block/br_if/br), both branch directions.
;;
;; Compiled with SYNTH_BASE_CSE=0 by spill_frame_499_differential.py: the
;; #592 default-on base-CSE relieves the register pressure on these shapes
;; (each store's address const folds away), which would make the oracle
;; vacuous — the bug is in the frame teardown, not in base-CSE.
(module
  (memory 1)
  (export "memory" (memory 0))
  (func (export "min_fields")
    (i32.store (i32.const 0)  (i32.const 11))
    (i32.store (i32.const 4)  (i32.const 22))
    (i32.store (i32.const 8)  (i32.const 33))
    (i32.store (i32.const 12) (i32.const 44))
    (i32.store (i32.const 16) (i32.const 55)))
  (func (export "nested") (param $sel i32)
    (i32.store (i32.const 20) (i32.const 55))
    (block $outer
      (block $inner
        (br_if $inner (i32.eqz (local.get $sel)))
        (br $outer))
      (i32.store8  (i32.const 24) (i32.const 66))
      (i32.store16 (i32.const 26) (i32.const 77))
      (i32.store8  (i32.const 28) (i32.const 88)))
    (i32.store (i32.const 32) (i32.const 99))))
