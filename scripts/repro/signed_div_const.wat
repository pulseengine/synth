(module
  (memory (export "memory") 1)
  (func (export "filter_axis_decide") (param $prev i32) (param $gyro i32) (param $accel i32) (result i32)
    (i32.div_s
      (i32.add
        (i32.mul (i32.add (local.get $prev) (local.get $gyro)) (i32.const 980))
        (i32.mul (local.get $accel) (i32.const 20)))
      (i32.const 1000))))
