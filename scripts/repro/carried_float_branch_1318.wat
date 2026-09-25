;; RQ-76-FALCON (#1318) — a value-carrying branch at f32.
;;
;; cpetig's `opt.wasm` declines 6 functions on this shape. Each contains a
;; `block` with an f32 RESULT reached by a branch. The direct selector lands a
;; carried value in the target block's designated result register; that register
;; is a CORE register, so a carried f32 hits the INTEGER peek and the compile
;; refuses with a message blaming the module.
;;
;; The i32 twin of every function below compiles today, which is the
;; discriminator: the shape is supported, the TYPE is not.
(module
  ;; S1 — the reporter's own eight-line reduction, verbatim in shape.
  (func (export "brif_f32") (param f32 i32) (result f32)
    (block (result f32)
      local.get 0
      local.get 1
      br_if 0
      f32.const 1.0
      f32.add))

  ;; S2 — unconditional br carrying f32 (same edge, no condition).
  (func (export "br_f32") (param f32) (result f32)
    (block (result f32)
      local.get 0
      br 0))

  ;; S3 — br_if to depth 1, so the carried value crosses an inner block.
  (func (export "brif_f32_d1") (param f32 i32) (result f32)
    (block (result f32)
      (block
        local.get 0
        local.get 1
        br_if 1
        drop)
      f32.const 9.5))

  ;; S4 — br_table carrying f32 (the third edge kind).
  (func (export "brtable_f32") (param f32 i32) (result f32)
    (block (result f32)
      local.get 0
      local.get 1
      br_table 0 0))

  ;; CONTROLS — the i32 twins. These compile TODAY and must keep compiling;
  ;; they are what makes "the type, not the shape" a measurement.
  (func (export "brif_i32") (param i32 i32) (result i32)
    (block (result i32)
      local.get 0
      local.get 1
      br_if 0
      i32.const 1
      i32.add))
  (func (export "br_i32") (param i32) (result i32)
    (block (result i32)
      local.get 0
      br 0)))
