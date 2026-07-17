;; #80: P3 async error-context intrinsic — the ONE lowered family.
;; error-context.* are pure scalar handle ops that marshal like any AAPCS C
;; call, so synth compiles the call site to a field-name BL through the
;; existing relocatable host-link path (#197). Compiling this must SUCCEED.
(module
  ;; error-context.drop takes a scalar error-context handle, returns nothing.
  (import "pulseengine:async" "error-context.drop" (func $ec_drop (param i32)))

  ;; Exported function that drops an error-context handle then returns it.
  (func (export "use_error_context") (param $ec i32) (result i32)
    local.get $ec
    call $ec_drop
    local.get $ec
  )
)
