;; PRE-EXISTING MISCOMPILE — read-before-write non-param local is not zero-inited.
;;
;; Found while building the VCR-RA local-promotion validation fixture (#390, #242).
;; wasm zero-initializes non-param locals, so `rbw(p0)` must return p0 + 0 = p0.
;; synth's ARM backend instead emits `adds r2, r0, r1; mov r0, r2` — it reads the
;; INCOMING r1 (no second param exists; r1 is caller garbage) rather than 0.
;;
;; ROOT CAUSE: `count_params` (crates/synth-backend/src/arm_backend.rs:126) infers
;; the param count from access patterns — a local whose FIRST access is a read is
;; assumed to be a param (`is_read_first` → num_params = max(read-first idx)+1).
;; A zero-init read-before-write local is indistinguishable from a param to this
;; heuristic, so it is homed in the param register and read instead of zeroed.
;;
;; Observed (./target/debug/synth compile ... --target cortex-m4 --relocatable):
;;   00000000 <func_0>:
;;      0: b510   push {r4, lr}
;;      2: 1842   adds r2, r0, r1   <-- reads r1 (garbage), should add 0
;;      4: 4610   mov  r0, r2
;;      6: bd10   pop  {r4, pc}
;;
;; Expected: r0 = r0 (+ 0). This is a real correctness gap independent of the
;; promotion lever; promotion v1 must therefore DECLINE read-before-write locals
;; (promote only write-before-read locals, frame fallback otherwise) until the
;; param-count heuristic is fixed to consult the declared signature.
(module
  (func (export "rbw") (param i32) (result i32)
    (local i32) ;; local 1: never written → must read 0
    (i32.add (local.get 0) (local.get 1))))
