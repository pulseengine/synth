;; #650 — multi-table call_indirect: the contiguous R11 region.
;;
;; Two funcref tables with OVERLAPPING indices but DISTINCT functions — the
;; aliasing canary: table0[i] and table1[i] must dispatch to different code
;; (a backend that ignores the table index and always indexes table 0 returns
;; table 0's results for f1). Layout contract: table 0 at R11+0 (3 entries),
;; table 1 at R11 + 3*4 = R11+12 (3 entries).
;;
;; Each table is homogeneous in the shared type $t, so the #642 closed-world
;; type verification discharges per (table, type). OOB on EITHER table must
;; trap against THAT table's own size.
(module
  (type $t (func (param i32) (result i32)))
  (table $t0 3 3 funcref)
  (table $t1 3 3 funcref)
  (func $a0 (type $t) (i32.add (local.get 0) (i32.const 100)))
  (func $a1 (type $t) (i32.add (local.get 0) (i32.const 200)))
  (func $a2 (type $t) (i32.add (local.get 0) (i32.const 300)))
  (func $b0 (type $t) (i32.mul (local.get 0) (i32.const 3)))
  (func $b1 (type $t) (i32.sub (i32.const 1000) (local.get 0)))
  (func $b2 (type $t) (i32.xor (local.get 0) (i32.const 0xFF)))
  (elem (table $t0) (i32.const 0) func $a0 $a1 $a2)
  (elem (table $t1) (i32.const 0) func $b0 $b1 $b2)
  (func (export "f0") (param $x i32) (param $sel i32) (result i32)
    (call_indirect $t0 (type $t) (local.get $x) (local.get $sel)))
  (func (export "f1") (param $x i32) (param $sel i32) (result i32)
    (call_indirect $t1 (type $t) (local.get $x) (local.get $sel))))
