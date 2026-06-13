;; CONTROL (should COMPILE): two single-result calls feeding select work today.
;; Discriminates: the bug is NOT select-fed-by-calls in general.
(module
  (func $one (result i32) i32.const 10)
  (func (export "f") (param i32) (result i32)
    call $one
    call $one
    local.get 0
    select))
