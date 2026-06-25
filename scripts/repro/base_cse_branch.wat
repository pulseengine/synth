;; VCR-RA lever 3 base-CSE (#468, epic #242) — CONTROL-FLOW non-vacuity fixture.
;;
;; The base-CSE hoist materializes the linear-memory base into R11 once at entry.
;; R11 is OUTSIDE the range-reallocator's R0–R8 pool, so it is identity-preserved
;; across every straight-line segment — the single entry materialization must stay
;; valid across a branch. This fixture splits the constant-address stores with a
;; `br_if`, so the differential exercises the path where a hoisted base is USED
;; after a control-flow edge (the cross-segment hazard the R11 choice neutralizes,
;; and which a purely straight-line fixture could never surface).
;;
;; init_branch(sel): always stores fields 0,4; if sel!=0 also stores fields 8,12.
;; Generic — neutral addresses/values, tied to nothing real.
(module
  (memory 1)
  (export "memory" (memory 0))
  (func (export "init_branch") (param $sel i32)
    (i32.store   (i32.const 0)  (i32.const 11))
    (i32.store   (i32.const 4)  (i32.const 22))
    (block $skip
      (br_if $skip (i32.eqz (local.get $sel)))
      (i32.store   (i32.const 8)  (i32.const 33))
      (i32.store16 (i32.const 12) (i32.const 44)))))
