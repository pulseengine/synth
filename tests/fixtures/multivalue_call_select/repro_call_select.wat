;; synth#329 reproducer — multi-value CALL result feeding `select`.
;; wasm-tools: VALID.  synth (v0.11.40, --cortex-m --all-exports): SKIPS 'f'
;;   with "stack underflow at select" — the abstract value-stack under-counts
;;   the 2-value call result to 1, so select (pops 3) sees too few operands.
;; This is the minimal shape of falcon-flight func_39 (the Select case).
;; EXPECTED AFTER FIX: compiles; f(a,b) returns a+b+1 (the high word of make()).
(module
  (func $two (result i32 i32) i32.const 10 i32.const 20)
  (func (export "f") (param i32) (result i32)
    call $two          ;; pushes 2
    local.get 0        ;; pushes 1  -> stack depth 3
    select))           ;; pops 3 -> synth underflows here
