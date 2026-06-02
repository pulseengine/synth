(module $flight_seam.wasm
  (type (;0;) (func (param i32 i32) (result i32)))
  (type (;1;) (func (param i32 i32)))
  (type (;2;) (func (param i32) (result i32)))
  (func $flight_algo (type 0) (param i32 i32) (result i32)
    (local i32 i32 i32 i32 i32 i32 i32)
    local.get 0
    local.get 1
    local.set 3
    local.set 2
    local.get 2
    local.get 3
    i32.load16_s offset=4
    local.tee 4
    i32.store offset=20
    local.get 2
    local.get 3
    i32.load16_s
    local.tee 5
    i32.store offset=16
    local.get 2
    local.get 3
    i32.load16_s offset=2
    local.tee 6
    i32.store offset=12
    local.get 2
    local.get 4
    local.get 2
    i32.load offset=8
    i32.add
    i32.store offset=8
    local.get 2
    local.get 5
    local.get 2
    i32.load offset=4
    i32.add
    i32.const 980
    i32.mul
    local.get 3
    i32.load16_s offset=8
    i32.const 20
    i32.mul
    i32.add
    i32.const 1000
    i32.div_s
    i32.store offset=4
    local.get 2
    local.get 6
    local.get 2
    i32.load
    i32.add
    i32.const 980
    i32.mul
    local.get 3
    i32.load16_s offset=6
    i32.const 20
    i32.mul
    i32.add
    i32.const 1000
    i32.div_s
    i32.store
    local.get 0
    local.set 7
    local.get 7
    i32.load offset=24
    i32.const 24
    i32.shl
    i32.const 0
    local.get 7
    i32.load offset=4
    i32.const 6
    i32.shr_s
    local.get 7
    i32.load offset=16
    i32.const 7
    i32.shr_s
    i32.add
    i32.sub
    local.tee 8
    i32.const -127
    local.get 8
    i32.const -127
    i32.gt_s
    select
    local.tee 8
    i32.const 127
    local.get 8
    i32.const 127
    i32.lt_s
    select
    i32.const 255
    i32.and
    i32.or
    i32.const 0
    local.get 7
    i32.load
    i32.const 6
    i32.shr_s
    local.get 7
    i32.load offset=12
    i32.const 7
    i32.shr_s
    i32.add
    i32.sub
    local.tee 8
    i32.const -127
    local.get 8
    i32.const -127
    i32.gt_s
    select
    local.tee 8
    i32.const 127
    local.get 8
    i32.const 127
    i32.lt_s
    select
    i32.const 8
    i32.shl
    i32.const 65280
    i32.and
    i32.or
    i32.const 0
    local.get 7
    i32.load offset=8
    i32.const 6
    i32.shr_s
    local.get 7
    i32.load offset=20
    i32.const 7
    i32.shr_s
    i32.add
    i32.sub
    local.tee 7
    i32.const -127
    local.get 7
    i32.const -127
    i32.gt_s
    select
    local.tee 7
    i32.const 127
    local.get 7
    i32.const 127
    i32.lt_s
    select
    i32.const 16
    i32.shl
    i32.const 16711680
    i32.and
    i32.or)
  (func $filter_step (type 1) (param i32 i32)
    (local i32 i32 i32)
    local.get 0
    local.get 1
    i32.load16_s offset=4
    local.tee 2
    i32.store offset=20
    local.get 0
    local.get 1
    i32.load16_s
    local.tee 3
    i32.store offset=16
    local.get 0
    local.get 1
    i32.load16_s offset=2
    local.tee 4
    i32.store offset=12
    local.get 0
    local.get 2
    local.get 0
    i32.load offset=8
    i32.add
    i32.store offset=8
    local.get 0
    local.get 3
    local.get 0
    i32.load offset=4
    i32.add
    i32.const 980
    i32.mul
    local.get 1
    i32.load16_s offset=8
    i32.const 20
    i32.mul
    i32.add
    i32.const 1000
    i32.div_s
    i32.store offset=4
    local.get 0
    local.get 4
    local.get 0
    i32.load
    i32.add
    i32.const 980
    i32.mul
    local.get 1
    i32.load16_s offset=6
    i32.const 20
    i32.mul
    i32.add
    i32.const 1000
    i32.div_s
    i32.store)
  (func $controller_step (type 2) (param i32) (result i32)
    (local i32)
    local.get 0
    i32.load offset=24
    i32.const 24
    i32.shl
    i32.const 0
    local.get 0
    i32.load offset=4
    i32.const 6
    i32.shr_s
    local.get 0
    i32.load offset=16
    i32.const 7
    i32.shr_s
    i32.add
    i32.sub
    local.tee 1
    i32.const -127
    local.get 1
    i32.const -127
    i32.gt_s
    select
    local.tee 1
    i32.const 127
    local.get 1
    i32.const 127
    i32.lt_s
    select
    i32.const 255
    i32.and
    i32.or
    i32.const 0
    local.get 0
    i32.load
    i32.const 6
    i32.shr_s
    local.get 0
    i32.load offset=12
    i32.const 7
    i32.shr_s
    i32.add
    i32.sub
    local.tee 1
    i32.const -127
    local.get 1
    i32.const -127
    i32.gt_s
    select
    local.tee 1
    i32.const 127
    local.get 1
    i32.const 127
    i32.lt_s
    select
    i32.const 8
    i32.shl
    i32.const 65280
    i32.and
    i32.or
    i32.const 0
    local.get 0
    i32.load offset=8
    i32.const 6
    i32.shr_s
    local.get 0
    i32.load offset=20
    i32.const 7
    i32.shr_s
    i32.add
    i32.sub
    local.tee 0
    i32.const -127
    local.get 0
    i32.const -127
    i32.gt_s
    select
    local.tee 0
    i32.const 127
    local.get 0
    i32.const 127
    i32.lt_s
    select
    i32.const 16
    i32.shl
    i32.const 16711680
    i32.and
    i32.or)
  (table (;0;) 1 1 funcref)
  (memory (;0;) 1)
  (global $__stack_pointer (mut i32) (i32.const 65536))
  (export "memory" (memory 0))
  (export "flight_algo" (func $flight_algo))
  (export "filter_step" (func $filter_step))
  (export "controller_step" (func $controller_step)))
