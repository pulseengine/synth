;; #791 — const-only-body exports on the OPTIMIZED (default self-contained) path.
;;
;; The optimized lowering (`optimizer_bridge::ir_to_arm`) materializes a bare
;; `i32.const` result into a callee-saved temp (r4/r6/...) and never moves it
;; to R0 — AAPCS callers read garbage (the caller's own saved r4, restored by
;; the epilogue `pop {r4,pc}`). Every function here must return its constant.
(module
  ;; The minimal repro: body is a single i32.const.
  (func (export "c100") (result i32) (i32.const 100))

  ;; i64 const-only body (R0:R1 pair) — green pre-fix, pinned as a guard.
  (func (export "c64") (result i64) (i64.const 0x1122334455667788))

  ;; Declared-but-unused locals must not change the story.
  (func (export "clocals") (result i32) (local i32 i32) (i32.const 42))

  ;; WRONG-VALUE variant: an earlier op leaves a stale last-result vreg, the
  ;; final const lands in a different temp — pre-fix this returns garbage
  ;; instead of 100 (not even the stale 3).
  (func (export "stale") (result i32) (local i32)
    (local.set 0 (i32.add (i32.const 1) (i32.const 2)))
    (i32.const 100))

  ;; Tail-position explicit `return` of a const — same missing move.
  (func (export "tailret") (result i32)
    (return (i32.const 77)))

  ;; local.get of a zero-init local — green pre-fix, pinned as a guard.
  (func (export "getzero") (result i32) (local i32) (local.get 0))
)
