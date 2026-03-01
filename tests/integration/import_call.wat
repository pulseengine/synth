;; WAT module with an imported function, used for static linking PoC test.
;;
;; The "env"/"log" import becomes import index 0. When compiled by Synth,
;; it should generate: MOV R0, #0; BL __meld_dispatch_import
;; producing a relocatable ELF with an undefined symbol and R_ARM_CALL relocation.
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
