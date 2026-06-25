(module
  (memory 1)
  (export "memory" (memory 0))

  ;; #483 canonical repro: a forward `block` + `br_if` exit. The br_if target
  ;; (block end) must skip the guarded stores when taken. i32.store16 inside the
  ;; block is the size-estimator trigger (Strh encodes 4 bytes, was sized 2).
  (func (export "init_branch") (param $sel i32)
    (i32.store (i32.const 0) (i32.const 11))
    (i32.store (i32.const 4) (i32.const 22))
    (block $skip
      (br_if $skip (i32.eqz (local.get $sel)))
      (i32.store   (i32.const 8)  (i32.const 33))
      (i32.store16 (i32.const 12) (i32.const 44))))

  ;; Nested blocks + an unconditional `br 1` exiting the OUTER block from inside
  ;; the inner one — exercises the `Br` path and label resolution across nested
  ;; Ends (each End must carry the id of the block it closes). Kept light (single
  ;; guarded word store) to isolate the branch resolution from spill/frame paths.
  (func (export "nested") (param $sel i32)
    (block $outer
      (block $inner
        (br_if $inner (local.get $sel))            ;; sel!=0 → skip to $inner end
        (br $outer))                               ;; sel==0 → exit $outer entirely
      (i32.store (i32.const 24) (i32.const 77)))   ;; reached only when sel!=0
    (i32.store (i32.const 32) (i32.const 99)))     ;; always reached
)
