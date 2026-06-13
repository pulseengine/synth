;; synth#329 reproducer — multi-value CALL result feeding `select`.
;; wasm-tools: VALID.  synth (v0.11.40, --cortex-m --all-exports): SKIPS 'f'
;;   with "stack underflow at select" — the abstract value-stack under-counts
;;   the 2-value call result to 1, so select (pops 3) sees too few operands.
;; This is the minimal shape of falcon-flight func_39 (the Select case).
;; EXPECTED AFTER FIX: compiles; `f` is `select(10, 20, cond=local.0)`, so it
;;   returns 10 when the param is non-zero and 20 when it is zero. Golden from
;;   wasmtime: f(1)=10, f(0)=20. (NOT "a+b+1" — that was a stray copy of the
;;   falcon make()/high-word context; this minimal func takes a single param.)
;; NOTE: the fix is two-sided — the caller must push BOTH call results AND the
;;   callee must return multi-values in r0:r1 (today `$two` leaves them in
;;   r4:r5), so a caller-only push would compile-but-miscompile. See synth#329.
(module
  (func $two (result i32 i32) i32.const 10 i32.const 20)
  (func (export "f") (param i32) (result i32)
    call $two          ;; pushes 2
    local.get 0        ;; pushes 1  -> stack depth 3
    select))           ;; pops 3 -> synth underflows here
