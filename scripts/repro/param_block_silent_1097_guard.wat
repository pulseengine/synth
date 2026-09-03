;; #1097 — negative control: the SUPPORTED neighbours of the declined class.
;; The #1096 guard must decline parameter-taking block types and NOTHING
;; else: a plain `if (result i32)` and a value-carrying forward `br_if` out
;; of a `block (result i32)` (the #483/#509-fixed shape) must still compile
;; on ARM and RV32 and match wasmtime. If this module ever declines, the
;; guard grew past its class.
(module
  (func (export "gie") (param i32) (result i32)
    (if (result i32) (local.get 0)
      (then (i32.const 49))
      (else (i32.const 7))))
  (func (export "gbr") (param i32) (result i32)
    (block (result i32)
      (i32.const 7)
      (local.get 0)
      (br_if 0)
      (drop)
      (i32.const 49))))
