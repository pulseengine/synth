(module
  (func (export "filter_axis_decide") (param i32 i32 i32) (result i32)
    local.get 0 local.get 1 i32.add
    i32.const 980 i32.mul
    local.get 2 i32.const 20 i32.mul
    i32.add
    i32.const 1000 i32.div_s))
