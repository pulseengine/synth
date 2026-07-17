;; #80: P3 async stream intrinsic — a DECLINED family. Synth does not yet
;; generate the bounds-checked linear-memory buffer layout stream.read needs,
;; so compiling this module must LOUD-DECLINE by name rather than emit a
;; silently-miscompiling BL. (Honest degradation, #275-style.)
(module
  ;; stream.read(stream, ptr, len) -> i32 (RFC #46 shape, approximate).
  (import "pulseengine:async" "stream.read"
    (func $stream_read (param i32 i32 i32) (result i32)))

  (func (export "read_stream") (param $s i32) (param $p i32) (param $n i32) (result i32)
    local.get $s
    local.get $p
    local.get $n
    call $stream_read
  )
)
