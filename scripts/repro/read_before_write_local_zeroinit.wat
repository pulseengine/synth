;; #457 — read-before-write non-param local must observe the wasm-mandated 0.
;;
;; Found while building the VCR-RA local-promotion validation fixture (#390, #242).
;; wasm zero-initializes non-param locals, so `rbw(p0)` must return p0 + 0 = p0.
;;
;; ROOT CAUSE (fixed in #457): `count_params` (arm_backend.rs / riscv
;; backend.rs / aarch64 backend.rs) infers the param count from access patterns
;; — a local whose FIRST access is a read is assumed to be a param
;; (`is_read_first` → num_params = max(read-first idx)+1). A zero-init
;; read-before-write local is indistinguishable from a param to this heuristic,
;; so it was homed in the param register and read caller garbage instead of 0:
;;   00000000 <func_0>:                 (pre-fix --relocatable output)
;;      0: b510   push {r4, lr}
;;      2: 1842   adds r2, r0, r1   <-- reads r1 (garbage), should add 0
;;      4: 4610   mov  r0, r2
;;      6: bd10   pop  {r4, pc}
;;
;; FIX: the driver plumbs the DECLARED param count
;; (`CompileConfig::current_func_param_count`, from the type section) and the
;; backends cap the inference with it (`min` — a function whose inference is
;; <= declared stays byte-identical). The reclassified local lands in a frame
;; slot which the direct selector / RV32 selector zero-initialize at entry;
;; the ARM optimized path detect-and-declines the shape to the direct selector.
;;
;; Oracle: read_before_write_local_zeroinit_differential.py (unicorn-vs-wasmtime,
;; dirty-register + dirty-frame passes; gates ARM direct, ARM optimized, RV32).
(module
  ;; 1 param + 1 never-written local: must return p0 + 0 = p0.
  (func (export "rbw") (param i32) (result i32)
    (local i32)
    (i32.add (local.get 0) (local.get 1)))
  ;; 0 params (the declared-count-0 edge: a param-width table that is EMPTY for
  ;; this function must still cap the inference) + 1 never-written local:
  ;; must return 0.
  (func (export "rbw0") (result i32)
    (local i32)
    (local.get 0)))
