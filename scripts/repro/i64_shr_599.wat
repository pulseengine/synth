;; #599: i64.shr_u / i64.shr_s miscompiled on the single-function CLI path
;; (`-n <name>`) — that path never plumbed the module's declared param widths
;; (func_params_i64) into the CompileConfig, so a read-only i64 param stayed
;; classified i32 and the shift-amount constant was materialized INTO the
;; param's live high register (r1). shr_u/shr_s by 32 returned the shift
;; amount itself; other amounts leaked spurious high bits. The all-exports
;; path (which plumbs the widths, #518) was already correct.
;; wasmtime oracle per function is computed by the differential harness.
(module
  (func (export "shr_u_32") (param i64) (result i32)
    (i32.wrap_i64 (i64.shr_u (local.get 0) (i64.const 32))))
  (func (export "shr_s_32") (param i64) (result i32)
    (i32.wrap_i64 (i64.shr_s (local.get 0) (i64.const 32))))
  (func (export "shr_u_1") (param i64) (result i32)
    (i32.wrap_i64 (i64.shr_u (local.get 0) (i64.const 1))))
  (func (export "shr_u_63") (param i64) (result i32)
    (i32.wrap_i64 (i64.shr_u (local.get 0) (i64.const 63))))
  (func (export "shr_s_63") (param i64) (result i32)
    (i32.wrap_i64 (i64.shr_s (local.get 0) (i64.const 63))))
  (func (export "shr_u_var") (param i64 i64) (result i32)
    (i32.wrap_i64 (i64.shr_u (local.get 0) (local.get 1))))
  (func (export "shl_4") (param i64) (result i32)
    ;; control: i64.shl was already correct (issue table)
    (i32.wrap_i64 (i64.shl (local.get 0) (i64.const 4)))))
