;; CONTROL (should COMPILE): multi-result call consumed by drop works today.
;; Discriminates: the multi-result CALL is counted as 2 correctly by `drop`;
;; only the call-result x select interaction under-counts.
(module
  (func $two (result i32 i32) i32.const 10 i32.const 20)
  (func (export "f") (result i32)
    call $two
    drop))
