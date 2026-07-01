;; #554 — `-b aarch64` (milestone-1, integer-only) must REJECT scalar f32 ops
;; honestly, not silently miscompile them. `f32.add` is dropped by the decoder
;; (`_ => None`), so it never reaches the selector's unsupported-op guard; before
;; the fix the backend lowered the remaining `[LocalGet, LocalGet, End]` into
;; `mov w0, w1 ; ret` (returns the 2nd operand, no add). `i32add` is the control:
;; a fully-supported milestone-1 op that must still compile.
(module
  (func (export "f32add") (param f32 f32) (result f32)
    (f32.add (local.get 0) (local.get 1)))
  (func (export "i32add") (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1))))
