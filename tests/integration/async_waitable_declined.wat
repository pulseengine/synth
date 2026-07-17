;; #80: waitable-set family — DECLINED (register save/restore across the
;; scheduler yield at waitable-set.wait unimplemented). Must loud-decline.
(module
  (import "pulseengine:async" "waitable-set.wait"
    (func $wait (param i32 i32) (result i32)))
  (func (export "do_wait") (param $ws i32) (param $p i32) (result i32)
    local.get $ws
    local.get $p
    call $wait))
