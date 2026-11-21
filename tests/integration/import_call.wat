;; WAT module with an imported function, used for static linking PoC test.
;;
;; The "env"/"log" import becomes import index 0. Synth compiles a module that
;; calls a function import as a host-linked object (as with --relocatable): the call
;; is a direct AAPCS `bl log` with the argument in R0, producing a relocatable
;; ELF with the undefined symbol `log` and an R_ARM_THM_CALL relocation.
(module
  ;; Import: env.log takes one i32 parameter, returns nothing
  (import "env" "log" (func $log (param i32)))

  ;; Exported function that calls the import
  (func (export "call_log") (param $val i32) (result i32)
    ;; Call the imported log function with the parameter
    local.get $val
    call $log

    ;; Return the parameter unchanged (so the function has a result)
    local.get $val
  )
)
