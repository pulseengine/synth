;; #80 SOUNDNESS: error-context.new carries a linmem message pointer (canonical
;; ABI), so despite being in the error-context family it is DECLINED — the same
;; buffer class as stream. Only error-context.drop (scalar) is lowered.
(module
  (import "pulseengine:async" "error-context.new"
    (func $ec_new (param i32 i32) (result i32)))
  (func (export "make_ec") (param $ptr i32) (param $len i32) (result i32)
    local.get $ptr
    local.get $len
    call $ec_new))
