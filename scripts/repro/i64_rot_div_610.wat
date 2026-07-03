;; #610: i64.rotl / i64.rotr / i64.div_u / i64.rem_u silently compiled to code
;; returning 0 for EVERY input on the ARM Cortex-M path (self-contained, no
;; relocations — not a missing libcall). Root cause was in the encoder's
;; multi-instruction expansions, one disease in two forms:
;;   - rotl/rotr: the expansion used hardcoded R3/R4 scratch that collided
;;     with the selector-assigned registers, then `POP {R4}` restored the
;;     saved scratch OVER the computed result (rd_lo == R4) — the op returned
;;     the caller's stale R4 (0 under qemu/unicorn reset state).
;;   - div_u/rem_u (and div_s/rem_s): the expansion IGNORED its register
;;     fields outright (hardcoded R0:R1 / R2:R3 in, result to R0:R1) while the
;;     selector allocated rd elsewhere (e.g. R4:R5) — and the core's own POP
;;     restored stale values over that pair too.
;; Fixed by the #610 fixed-ABI wrapper: save R0-R3, marshal operands via the
;; stack (permutation-safe), run the fixed-reg core, MOV the result into the
;; selector's rd pair, restore R0-R3 skipping the result registers. Divide by
;; zero now traps (UDF #0), matching WASM semantics and the i32 guard.
;;
;; lo/hi function pairs let the harness check BOTH halves of every 64-bit
;; result through the i32 return register. wasmtime oracle per vector.
(module
  ;; --- variable-amount rotates ---
  (func (export "rotl") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.rotl (local.get 0) (local.get 1))))
  (func (export "rotl_hi") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.shr_u (i64.rotl (local.get 0) (local.get 1)) (i64.const 32))))
  (func (export "rotr") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.rotr (local.get 0) (local.get 1))))
  (func (export "rotr_hi") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.shr_u (i64.rotr (local.get 0) (local.get 1)) (i64.const 32))))
  ;; --- const-amount rotates (the issue's exact repro shape) ---
  (func (export "rotl8") (param i64) (result i32)
    (i32.wrap_i64 (i64.rotl (local.get 0) (i64.const 8))))
  (func (export "rotl0") (param i64) (result i32)
    (i32.wrap_i64 (i64.rotl (local.get 0) (i64.const 0))))
  (func (export "rotr8") (param i64) (result i32)
    (i32.wrap_i64 (i64.rotr (local.get 0) (i64.const 8))))
  ;; --- unsigned divide / remainder ---
  (func (export "div_u") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.div_u (local.get 0) (local.get 1))))
  (func (export "div_u_hi") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.shr_u (i64.div_u (local.get 0) (local.get 1)) (i64.const 32))))
  (func (export "rem_u") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.rem_u (local.get 0) (local.get 1))))
  (func (export "rem_u_hi") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.shr_u (i64.rem_u (local.get 0) (local.get 1)) (i64.const 32))))
  (func (export "divu7") (param i64) (result i32)
    (i32.wrap_i64 (i64.div_u (local.get 0) (i64.const 7))))
  ;; --- signed divide / remainder (same fixed-ABI disease, fixed together) ---
  (func (export "div_s") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.div_s (local.get 0) (local.get 1))))
  (func (export "rem_s") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.rem_s (local.get 0) (local.get 1))))
  ;; --- control: correct before the fix (issue table) ---
  (func (export "shl4") (param i64) (result i32)
    (i32.wrap_i64 (i64.shl (local.get 0) (i64.const 4)))))
