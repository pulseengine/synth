(module $u64.wasm
  (type (;0;) (func (param i32 i32) (result i64)))
  (type (;1;) (func (param i32 i32) (result i32)))
  (table (;0;) 1 1 funcref)
  (memory (;0;) 1)
  (global $__stack_pointer (;0;) (mut i32) i32.const 65536)
  (export "memory" (memory 0))
  (export "check" (func $check))
  (func $make (;0;) (type 0) (param i32 i32) (result i64)
    local.get 0
    local.get 1
    i32.add
    i32.const 1
    i32.add
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 1
    i64.or
  )
  (func $check (;1;) (type 1) (param i32 i32) (result i32)
    (local i64 i32 i32)
    local.get 0
    local.get 1
    local.set 4
    local.set 3
    local.get 3
    local.get 4
    i32.add
    i32.const 1
    i32.add
    i64.extend_i32_u
    i64.const 32
    i64.shl
    i64.const 1
    i64.or
    local.tee 2
    i64.const 32
    i64.shr_u
    i32.wrap_i64
    i32.const 57005
    local.get 2
    i64.const 255
    i64.and
    i64.const 1
    i64.eq
    select
  )
  (@custom "target_features" (after code) "\08+\0bbulk-memory+\0fbulk-memory-opt+\16call-indirect-overlong+\0amultivalue+\0fmutable-globals+\13nontrapping-fptoint+\0freference-types+\08sign-ext")
)
