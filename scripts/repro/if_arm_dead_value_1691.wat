;; #1691 (RQ-91-O2FLOAT): an `if` arm that ends in an unconditional transfer
;; (br / br_table / return / unreachable) must not leave its dead values on the
;; direct selector's simulated operand stack. Every export below puts a value
;; BENEATH the if (or the block around it) and consumes it after, so a dead
;; arm's leftover that survives the arm's end is read instead of that value.
;;
;; Every export takes one i32 `x`; the oracle calls each with x in
;; {0, 1, 5, 7} (the transfer is taken when x == 0 unless noted).
;;
;; `t_*` exports are the RED shapes. `ctl_*` exports are CONTROLS: their dead
;; arm leaves exactly the if's arity, which the selector already handled, so
;; they must execute correctly on the base tree too (and their bytes do not
;; move). `refuse_below` is the loud-refusal pin: its dead code drops BELOW
;; the if's entry height, which the selector cannot model, so it is declined.
(module
  ;; ---- i32 -------------------------------------------------------------
  ;; then-arm br, else-less if (the #1691 shape at i32)
  (func (export "t_i32_then") (param i32) (result i32)
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
  ;; else-arm br
  (func (export "t_i32_else") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        nop
      else
        i32.const 1
        br 1
      end
      i32.const 7
    end
    i32.sub)
  ;; both arms br (void if; its end is unreachable)
  (func (export "t_i32_both") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        i32.const 1
        br 1
      else
        i32.const 2
        br 1
      end
      i32.const 7
    end
    i32.sub)
  ;; br from a block nested inside the arm
  (func (export "t_i32_nested") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        block
          i32.const 1
          br 2
        end
      end
      i32.const 7
    end
    i32.sub)
  ;; br_table
  (func (export "t_i32_br_table") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        i32.const 1
        i32.const 0
        br_table 1
      end
      i32.const 7
    end
    i32.sub)
  ;; unreachable: x == 0 traps on both sides; x != 0 must not read the
  ;; dead arm's value
  (func (export "t_i32_unreachable") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        i32.const 1
        unreachable
      end
      i32.const 7
    end
    i32.sub)
  ;; return leaves the operand BELOW its result behind
  (func (export "t_i32_return_extra") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        i32.const 9
        i32.const 1
        return
      end
      i32.const 7
    end
    i32.sub)
  ;; the carried value unwound into a VOID block
  (func (export "t_i32_void_target") (param i32) (result i32)
    i32.const 100
    block
      local.get 0
      i32.eqz
      if
        i32.const 1
        br 1
      end
    end
    i32.const 7
    i32.sub)
  ;; mismatched counts at a result-typed if/else: the dead then arm leaves 2
  (func (export "t_i32_mismatch_then") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if (result i32)
        i32.const 1
        i32.const 2
        br 1
      else
        i32.const 7
      end
    end
    i32.sub)
  ;; mismatched counts: the dead ELSE arm leaves 2
  (func (export "t_i32_mismatch_else") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if (result i32)
        i32.const 7
      else
        i32.const 1
        i32.const 2
        br 1
      end
    end
    i32.sub)
  ;; result-typed if, both arms dead with different counts
  (func (export "t_i32_both_result") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if (result i32)
        i32.const 1
        br 1
      else
        i32.const 2
        i32.const 3
        br 1
      end
    end
    i32.sub)
  ;; a result loop exited from an if (the spec labels.wast loop1 shape),
  ;; with a value beneath the block
  (func (export "t_i32_loop_exit") (param i32) (result i32)
    (local i32)
    i32.const 1000
    block (result i32)
      loop (result i32)
        local.get 1
        i32.const 1
        i32.add
        local.set 1
        local.get 1
        local.get 0
        i32.const 3
        i32.add
        i32.eq
        if
          local.get 1
          br 2
        end
        br 0
      end
    end
    i32.sub)

  ;; ---- i64 (the value beneath is i64) ------------------------------------
  (func (export "t_i64_void_target") (param i32) (result i64)
    i64.const 100
    block
      local.get 0
      i32.eqz
      if
        i64.const 1
        br 1
      end
    end
    i64.const 7
    i64.sub)
  (func (export "t_i64_beneath_i32_carried") (param i32) (result i64)
    i64.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if
        i32.const 1
        br 1
      end
      i32.const 7
    end
    i64.extend_i32_u
    i64.sub)

  ;; ---- f32 (the reporter's shape) ----------------------------------------
  (func (export "t_f32_then") (param i32) (result f32)
    f32.const 1
    block (result f32)
      local.get 0
      i32.eqz
      if
        f32.const 0
        br 1
      end
      local.get 0
      f32.convert_i32_s
      f32.const 2
      f32.mul
    end
    f32.sub)
  (func (export "t_f32_else") (param i32) (result f32)
    f32.const 1
    block (result f32)
      local.get 0
      i32.eqz
      if
        nop
      else
        f32.const 0.5
        br 1
      end
      f32.const 2
    end
    f32.sub)
  (func (export "t_f32_both") (param i32) (result f32)
    f32.const 1
    block (result f32)
      local.get 0
      i32.eqz
      if
        f32.const 0.25
        br 1
      else
        f32.const 0.5
        br 1
      end
      f32.const 2
    end
    f32.sub)
  (func (export "t_f32_nested") (param i32) (result f32)
    f32.const 1
    block (result f32)
      local.get 0
      i32.eqz
      if
        block
          f32.const 0.25
          br 2
        end
      end
      f32.const 2
    end
    f32.sub)
  (func (export "t_f32_br_table") (param i32) (result f32)
    f32.const 1
    block (result f32)
      local.get 0
      i32.eqz
      if
        f32.const 0.25
        i32.const 0
        br_table 1
      end
      f32.const 2
    end
    f32.sub)
  (func (export "t_f32_unreachable") (param i32) (result f32)
    f32.const 1
    block (result f32)
      local.get 0
      i32.eqz
      if
        f32.const 0.25
        unreachable
      end
      f32.const 2
    end
    f32.sub)
  (func (export "t_f32_void_target") (param i32) (result f32)
    f32.const 1
    block
      local.get 0
      i32.eqz
      if
        f32.const 0.25
        br 1
      end
    end
    f32.const 2
    f32.sub)

  ;; ---- f64 (double-precision targets) ------------------------------------
  (func (export "t_f64_void_target") (param i32) (result f64)
    f64.const 100
    block
      local.get 0
      i32.eqz
      if
        f64.const 1
        br 1
      end
    end
    f64.const 7
    f64.sub)
  (func (export "t_f64_beneath_f32_carried") (param i32) (result f64)
    f64.const 100
    block (result f32)
      local.get 0
      i32.eqz
      if
        f32.const 0.25
        br 1
      end
      f32.const 2
    end
    f64.promote_f32
    f64.sub)

  ;; ---- controls: a dead arm that left exactly the if's arity --------------
  (func (export "ctl_i32_arity_held") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.eqz
      if (result i32)
        i32.const 1
        br 1
      else
        i32.const 7
      end
    end
    i32.sub)
  (func (export "ctl_i32_no_dead_arm") (param i32) (result i32)
    i32.const 100
    block (result i32)
      local.get 0
      i32.const 1
      br_if 0
      drop
      i32.const 7
    end
    i32.sub)

  ;; ---- loud refusal: dead code drops BELOW the if's entry height ----------
  (func (export "refuse_below") (param i32) (result i32)
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
)
