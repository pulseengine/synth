(module
  ;; #882 minimal repro — gale i2c_step shape: a `return` on the fall-through
  ;; path of a block whose end label is a br_if target. The old lower_seq
  ;; broke out of the walk at `return`, so the `end` never emitted `Lend0`.
  (func $f (export "f") (param i32) (result i32)
    block ;; end label = Lend0, referenced by the br_if
      local.get 0
      br_if 0
      i32.const 1
      return
    end
    i32.const 7)

  ;; if/else where the then-arm returns — the else arm is REACHABLE via the
  ;; beq to Lelse; the old break skipped it entirely (undefined `Lelse`).
  (func $g (export "g") (param i32) (result i32)
    local.get 0
    if (result i32)
      i32.const 11
      return
    else
      i32.const 22
    end)

  ;; nested: inner block falls through into reachable tail code after its end
  ;; (the exact i2c_step nesting), outer end also a br_if target.
  (func $h (export "h") (param i32) (param i32) (result i32)
    block
      local.get 0
      br_if 0
      block
        local.get 1
        br_if 0
        i32.const 3
        return
      end
      ;; reachable via the inner br_if
      i32.const 5
      return
    end
    i32.const 9)
)
