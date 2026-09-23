;; RQ-71-VFPALIAS (#881) — a FRAME-HOMED VFP local written TWICE.
;;
;; The #1069 rung frame-homes an overflow f32 local from birth: `local.set`
;; stores to the local's PERMANENT [sp,#slot] and "the def IS the store"
;; (instruction_selector.rs, the `f32_frame` arm). A wasm local may legally be
;; redefined, so that slot legitimately holds two different values over the
;; function's extent, with the first one dead.
;;
;; `check_vfp_slot_aliasing` (liveness.rs) polices EVERY `[sp,#off]` VFP
;; store/reload. It excuses a re-store it can prove identical (`src_word` +
;; `src_version`), but a redefinition is a DIFFERENT value, so it reports
;; VfpSpillSlotAliased and the compile is REFUSED as "a compiler bug".
;;
;; This is the VFP twin of the #1321 false positive v0.70 fixed for the
;; INTEGER check by SCOPING it to the allocator's own spill areas
;; (`validate_final_allocation_in_areas`). The VFP twin never received that
;; narrowing: it takes no areas parameter at all.
;;
;; Three legs, one variable — whether the second store carries a new value:
;;   redef_none  NEGATIVE CONTROL: every local written once      -> compiles
;;   redef_diff  local 24 rewritten with a DIFFERENT value       -> the red
;;   redef_same  local 24 re-stored with the IDENTICAL value     -> compiles
;;               (the `src_version` benign path, working as designed — it is
;;                what proves the red is about REDEFINITION, not re-storing)
;;
;; All three need 24 locals so the base path exhausts and the backend's retry
;; ladder engages the frame-home rung; `local 24` is high enough to be
;; frame-homed rather than register-homed (the S7 cap).
(module
  (func $redef_none (param f32) (result f32) (local f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32)
    local.get 0
    f32.const 1.5
    f32.mul
    local.set 1
    local.get 0
    f32.const 2.5
    f32.mul
    local.set 2
    local.get 0
    f32.const 3.5
    f32.mul
    local.set 3
    local.get 0
    f32.const 4.5
    f32.mul
    local.set 4
    local.get 0
    f32.const 5.5
    f32.mul
    local.set 5
    local.get 0
    f32.const 6.5
    f32.mul
    local.set 6
    local.get 0
    f32.const 7.5
    f32.mul
    local.set 7
    local.get 0
    f32.const 8.5
    f32.mul
    local.set 8
    local.get 0
    f32.const 9.5
    f32.mul
    local.set 9
    local.get 0
    f32.const 10.5
    f32.mul
    local.set 10
    local.get 0
    f32.const 11.5
    f32.mul
    local.set 11
    local.get 0
    f32.const 12.5
    f32.mul
    local.set 12
    local.get 0
    f32.const 13.5
    f32.mul
    local.set 13
    local.get 0
    f32.const 14.5
    f32.mul
    local.set 14
    local.get 0
    f32.const 15.5
    f32.mul
    local.set 15
    local.get 0
    f32.const 16.5
    f32.mul
    local.set 16
    local.get 0
    f32.const 17.5
    f32.mul
    local.set 17
    local.get 0
    f32.const 18.5
    f32.mul
    local.set 18
    local.get 0
    f32.const 19.5
    f32.mul
    local.set 19
    local.get 0
    f32.const 20.5
    f32.mul
    local.set 20
    local.get 0
    f32.const 21.5
    f32.mul
    local.set 21
    local.get 0
    f32.const 22.5
    f32.mul
    local.set 22
    local.get 0
    f32.const 23.5
    f32.mul
    local.set 23
    local.get 0
    f32.const 24.5
    f32.mul
    local.set 24
    local.get 1
    local.get 2
    f32.mul
    local.get 3
    f32.mul
    local.get 4
    f32.mul
    local.get 5
    f32.mul
    local.get 6
    f32.mul
    local.get 7
    f32.mul
    local.get 8
    f32.mul
    local.get 9
    f32.mul
    local.get 10
    f32.mul
    local.get 11
    f32.mul
    local.get 12
    f32.mul
    local.get 13
    f32.mul
    local.get 14
    f32.mul
    local.get 15
    f32.mul
    local.get 16
    f32.mul
    local.get 17
    f32.mul
    local.get 18
    f32.mul
    local.get 19
    f32.mul
    local.get 20
    f32.mul
    local.get 21
    f32.mul
    local.get 22
    f32.mul
    local.get 23
    f32.mul
    local.get 24
    f32.mul)
  (export "redef_none" (func $redef_none))
  (func $redef_diff (param f32) (result f32) (local f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32)
    local.get 0
    f32.const 1.5
    f32.mul
    local.set 1
    local.get 0
    f32.const 2.5
    f32.mul
    local.set 2
    local.get 0
    f32.const 3.5
    f32.mul
    local.set 3
    local.get 0
    f32.const 4.5
    f32.mul
    local.set 4
    local.get 0
    f32.const 5.5
    f32.mul
    local.set 5
    local.get 0
    f32.const 6.5
    f32.mul
    local.set 6
    local.get 0
    f32.const 7.5
    f32.mul
    local.set 7
    local.get 0
    f32.const 8.5
    f32.mul
    local.set 8
    local.get 0
    f32.const 9.5
    f32.mul
    local.set 9
    local.get 0
    f32.const 10.5
    f32.mul
    local.set 10
    local.get 0
    f32.const 11.5
    f32.mul
    local.set 11
    local.get 0
    f32.const 12.5
    f32.mul
    local.set 12
    local.get 0
    f32.const 13.5
    f32.mul
    local.set 13
    local.get 0
    f32.const 14.5
    f32.mul
    local.set 14
    local.get 0
    f32.const 15.5
    f32.mul
    local.set 15
    local.get 0
    f32.const 16.5
    f32.mul
    local.set 16
    local.get 0
    f32.const 17.5
    f32.mul
    local.set 17
    local.get 0
    f32.const 18.5
    f32.mul
    local.set 18
    local.get 0
    f32.const 19.5
    f32.mul
    local.set 19
    local.get 0
    f32.const 20.5
    f32.mul
    local.set 20
    local.get 0
    f32.const 21.5
    f32.mul
    local.set 21
    local.get 0
    f32.const 22.5
    f32.mul
    local.set 22
    local.get 0
    f32.const 23.5
    f32.mul
    local.set 23
    local.get 0
    f32.const 24.5
    f32.mul
    local.set 24
    local.get 0
    f32.const 99.25
    f32.mul
    local.set 24
    local.get 1
    local.get 2
    f32.mul
    local.get 3
    f32.mul
    local.get 4
    f32.mul
    local.get 5
    f32.mul
    local.get 6
    f32.mul
    local.get 7
    f32.mul
    local.get 8
    f32.mul
    local.get 9
    f32.mul
    local.get 10
    f32.mul
    local.get 11
    f32.mul
    local.get 12
    f32.mul
    local.get 13
    f32.mul
    local.get 14
    f32.mul
    local.get 15
    f32.mul
    local.get 16
    f32.mul
    local.get 17
    f32.mul
    local.get 18
    f32.mul
    local.get 19
    f32.mul
    local.get 20
    f32.mul
    local.get 21
    f32.mul
    local.get 22
    f32.mul
    local.get 23
    f32.mul
    local.get 24
    f32.mul)
  (export "redef_diff" (func $redef_diff))
  (func $redef_same (param f32) (result f32) (local f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32 f32)
    local.get 0
    f32.const 1.5
    f32.mul
    local.set 1
    local.get 0
    f32.const 2.5
    f32.mul
    local.set 2
    local.get 0
    f32.const 3.5
    f32.mul
    local.set 3
    local.get 0
    f32.const 4.5
    f32.mul
    local.set 4
    local.get 0
    f32.const 5.5
    f32.mul
    local.set 5
    local.get 0
    f32.const 6.5
    f32.mul
    local.set 6
    local.get 0
    f32.const 7.5
    f32.mul
    local.set 7
    local.get 0
    f32.const 8.5
    f32.mul
    local.set 8
    local.get 0
    f32.const 9.5
    f32.mul
    local.set 9
    local.get 0
    f32.const 10.5
    f32.mul
    local.set 10
    local.get 0
    f32.const 11.5
    f32.mul
    local.set 11
    local.get 0
    f32.const 12.5
    f32.mul
    local.set 12
    local.get 0
    f32.const 13.5
    f32.mul
    local.set 13
    local.get 0
    f32.const 14.5
    f32.mul
    local.set 14
    local.get 0
    f32.const 15.5
    f32.mul
    local.set 15
    local.get 0
    f32.const 16.5
    f32.mul
    local.set 16
    local.get 0
    f32.const 17.5
    f32.mul
    local.set 17
    local.get 0
    f32.const 18.5
    f32.mul
    local.set 18
    local.get 0
    f32.const 19.5
    f32.mul
    local.set 19
    local.get 0
    f32.const 20.5
    f32.mul
    local.set 20
    local.get 0
    f32.const 21.5
    f32.mul
    local.set 21
    local.get 0
    f32.const 22.5
    f32.mul
    local.set 22
    local.get 0
    f32.const 23.5
    f32.mul
    local.set 23
    local.get 0
    f32.const 24.5
    f32.mul
    local.set 24
    local.get 24
    local.set 24
    local.get 1
    local.get 2
    f32.mul
    local.get 3
    f32.mul
    local.get 4
    f32.mul
    local.get 5
    f32.mul
    local.get 6
    f32.mul
    local.get 7
    f32.mul
    local.get 8
    f32.mul
    local.get 9
    f32.mul
    local.get 10
    f32.mul
    local.get 11
    f32.mul
    local.get 12
    f32.mul
    local.get 13
    f32.mul
    local.get 14
    f32.mul
    local.get 15
    f32.mul
    local.get 16
    f32.mul
    local.get 17
    f32.mul
    local.get 18
    f32.mul
    local.get 19
    f32.mul
    local.get 20
    f32.mul
    local.get 21
    f32.mul
    local.get 22
    f32.mul
    local.get 23
    f32.mul
    local.get 24
    f32.mul)
  (export "redef_same" (func $redef_same))
)
