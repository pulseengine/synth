;; #80: task family — DECLINED (same yield-point class as waitable-set).
;; Must loud-decline.
(module
  (import "pulseengine:async" "task.return" (func $task_return (param i32)))
  (func (export "finish_task") (param $r i32)
    local.get $r
    call $task_return))
