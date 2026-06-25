(module
  (memory 1)
  ;; #490 fixture (epic #242): functions the OPTIMIZED path lowers using r4-r8 as
  ;; scratch. Before the fix the optimized path emitted no prologue and silently
  ;; clobbered a caller's callee-saved registers; the differential sets r4-r8 to
  ;; sentinels, runs each function, and asserts the sentinels survive AND the
  ;; result matches wasmtime — proving the push/pop the fix adds preserves them.
  ;;
  ;; Pressure is tuned to exercise the callee-saved range WITHOUT exhausting the
  ;; R0-R8 pool (the optimized path has no spill, so an exhausting fold would hit
  ;; a separate pre-existing miscompile and conflate two issues). Each function
  ;; below is differential-verified to compute correctly on the optimized path.

  ;; low: two live temps → 16-bit `push {r4,r5,r6,lr}` (r6 is shrink's even-pad).
  (func $low (export "low") (param i32) (result i32)
    (i32.add (local.get 0) (i32.const 100)))

  ;; mid: three live subterms → `push {r4,r5,r6,lr}`.
  (func $mid (export "mid") (param i32 i32) (result i32)
    (i32.add (i32.mul (local.get 0) (local.get 1))
             (i32.sub (local.get 0) (local.get 1))))

  ;; wide: enough simultaneously-live products to reach r8 → 32-bit Thumb-2
  ;; `push.w {r4-r8,lr}`, exercising the high-register save the 16-bit form
  ;; cannot encode.
  (func $wide (export "wide") (param i32 i32 i32) (result i32)
    (i32.add
      (i32.add (i32.mul (local.get 0) (local.get 1))
               (i32.mul (local.get 1) (local.get 2)))
      (i32.mul (local.get 0) (local.get 2))))
)
