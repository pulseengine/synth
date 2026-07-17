;; #80: future family — DECLINED (readable/writable-end buffer protocol
;; unimplemented). Compiling must loud-decline.
(module
  (import "pulseengine:async" "future.read"
    (func $future_read (param i32 i32) (result i32)))
  (func (export "read_future") (param $f i32) (param $p i32) (result i32)
    local.get $f
    local.get $p
    call $future_read))
