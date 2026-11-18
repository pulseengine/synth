;; #1740 (RQ-92-A64BELOW): AArch64 dead code that pops BELOW its frame's entry
;; height. WASM validates code after an unconditional transfer (br / br_table /
;; return / unreachable) against a POLYMORPHIC stack, so it may pop values the
;; straight-line model holds for the code BENEATH the frame. The AArch64
;; selector lowered that dead code against its model and popped the live
;; values beneath out of it: a debug build panicked ("void frame must restore
;; stack height"), a release build declined with `binop underflow`.
;;
;; Every `b_*` export is a below-entry shape; each has a `l_*` twin that is the
;; SAME function with the dead code deleted. Dead code is never executed, so the
;; pair must agree with wasmtime and (the Rust test pins this) compile to
;; byte-identical AArch64 text. Every export takes one i32 `x`; the oracle calls
;; each with x in {0, 1, 5, 7} (the transfer is taken when x == 0 unless noted).
(module
  ;; the #1691 fixture's refusal pin: dead `drop drop` reach the 100 beneath
  (func (export "b_refuse_below") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        i32.const 1
        br 1
        drop
        drop
      end
      i32.const 7
    end
    i32.sub)
  (func (export "l_refuse_below") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        i32.const 1
        br 1
      end
      i32.const 7
    end
    i32.sub)

  ;; a value beneath INSIDE the block, consumed by a live add after the if
  (func (export "b_inner_beneath") (param i32) (result i32)
    i32.const 100
    block (result i32)
      i32.const 5
      local.get 0
      i32.eqz
      if
        i32.const 1
        br 1
        drop
        drop
      end
      i32.const 7
      i32.add
    end
    i32.sub)
  (func (export "l_inner_beneath") (param i32) (result i32)
    i32.const 100
    block (result i32)
      i32.const 5
      local.get 0
      i32.eqz
      if
        i32.const 1
        br 1
      end
      i32.const 7
      i32.add
    end
    i32.sub)

  ;; a dead binop that consumes the value beneath a void block
  (func (export "b_dead_binop") (param i32) (result i32)
    i32.const 100
    block
      local.get 0
      i32.eqz
      if
        br 1
        i32.const 9
        i32.add
        drop
      end
    end
    i32.const 7
    i32.sub)
  (func (export "l_dead_binop") (param i32) (result i32)
    i32.const 100
    block
      local.get 0
      i32.eqz
      if
        br 1
      end
    end
    i32.const 7
    i32.sub)

  ;; dead then-arm reaches below; the else arm is live
  (func (export "b_then_below_else_live") (param i32) (result i32)
    i32.const 100
    local.get 0
    i32.eqz
    if (result i32)
      i32.const 1
      return
      drop
      drop
      i32.const 0
    else
      i32.const 7
    end
    i32.sub)
  (func (export "l_then_below_else_live") (param i32) (result i32)
    i32.const 100
    local.get 0
    i32.eqz
    if (result i32)
      i32.const 1
      return
    else
      i32.const 7
    end
    i32.sub)

  ;; dead control frames nested in the dead code (a dead if pops its
  ;; condition from below; a dead block and loop pop below inside)
  (func (export "b_dead_frames") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        i32.const 1
        br 1
        if
          br 0
          drop
        else
          unreachable
          drop
          drop
        end
        block
          br 0
          drop
        end
        loop
          br 0
          i32.add
          drop
        end
      end
      i32.const 7
    end
    i32.sub)
  (func (export "l_dead_frames") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        i32.const 1
        br 1
      end
      i32.const 7
    end
    i32.sub)

  ;; a live value-carrying block AFTER the dead region (block-arity ordinals
  ;; must stay aligned past the skipped dead frames)
  (func (export "b_ordinal_after") (param i32) (result i32)
    i32.const 100
    block
      local.get 0
      i32.eqz
      if
        br 1
        block (result i32 i32)
          unreachable
        end
        drop
        drop
        drop
      end
    end
    block (result i32)
      local.get 0
      i32.const 3
      i32.add
    end
    i32.sub)
  (func (export "l_ordinal_after") (param i32) (result i32)
    i32.const 100
    block
      local.get 0
      i32.eqz
      if
        br 1
      end
    end
    block (result i32)
      local.get 0
      i32.const 3
      i32.add
    end
    i32.sub)

  ;; after `unreachable` (x == 0 traps on both sides) and after br_table
  (func (export "b_after_unreachable") (param i32) (result i32)
    i32.const 100
    local.get 0
    i32.eqz
    if
      unreachable
      i32.add
      drop
    end
    i32.const 7
    i32.sub)
  (func (export "l_after_unreachable") (param i32) (result i32)
    i32.const 100
    local.get 0
    i32.eqz
    if
      unreachable
    end
    i32.const 7
    i32.sub)
  (func (export "b_after_br_table") (param i32) (result i32)
    i32.const 100
    block
      local.get 0
      i32.eqz
      if
        i32.const 0
        br_table 1
        i32.sub
        drop
      end
    end
    i32.const 7
    i32.sub)
  (func (export "l_after_br_table") (param i32) (result i32)
    i32.const 100
    block
      local.get 0
      i32.eqz
      if
        i32.const 0
        br_table 1
      end
    end
    i32.const 7
    i32.sub)

  ;; i64 and f32 / f64 values beneath
  (func (export "b_i64") (param i32) (result i64)
    i64.const 100
    block (result i64)
      local.get 0
      i32.eqz
      if
        i64.const 1
        br 1
        i64.add
        drop
      end
      i64.const 7
    end
    i64.sub)
  (func (export "l_i64") (param i32) (result i64)
    i64.const 100
    block (result i64)
      local.get 0
      i32.eqz
      if
        i64.const 1
        br 1
      end
      i64.const 7
    end
    i64.sub)
  (func (export "b_f32") (param i32) (result f32)
    f32.const 1
    block (result f32)
      local.get 0
      i32.eqz
      if
        f32.const 0.25
        br 1
        f32.mul
        drop
      end
      f32.const 2
    end
    f32.sub)
  (func (export "l_f32") (param i32) (result f32)
    f32.const 1
    block (result f32)
      local.get 0
      i32.eqz
      if
        f32.const 0.25
        br 1
      end
      f32.const 2
    end
    f32.sub)
  (func (export "b_f64") (param i32) (result f64)
    f64.const 100
    block
      local.get 0
      i32.eqz
      if
        br 1
        f64.neg
        drop
      end
    end
    f64.const 7
    f64.sub)
  (func (export "l_f64") (param i32) (result f64)
    f64.const 100
    block
      local.get 0
      i32.eqz
      if
        br 1
      end
    end
    f64.const 7
    f64.sub)
)
