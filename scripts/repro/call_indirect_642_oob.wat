;; #642: Thumb-2 call_indirect emitted NO table bounds check and NO type
;; check — an out-of-bounds index read past the table and BLXed whatever
;; word lay there: an uncontrolled indirect branch instead of the WASM Core
;; §4.4.8 trap. In-bounds dispatch was correct (the #594/#597 arc), which is
;; exactly why a probe driving only valid indices cannot see it.
;;
;; wasmtime oracle (a=5): f(5,0)=15 (add), f(5,1)=-5 (sub), f(5,2)=50 (mul);
;; f(5,5) and f(5,99) TRAP ("undefined element" / OOB table access).
;;
;; The table is fully covered by the elem segment and every entry shares
;; $bin — the closed-world property the compile-time type check verifies.
(module
  (type $bin (func (param i32 i32) (result i32)))
  (table 3 funcref)
  (elem (i32.const 0) $add $sub $mul)
  (func $add (param i32 i32) (result i32)
    (i32.add (local.get 0) (local.get 1)))
  (func $sub (param i32 i32) (result i32)
    (i32.sub (local.get 0) (local.get 1)))
  (func $mul (param i32 i32) (result i32)
    (i32.mul (local.get 0) (local.get 1)))
  (func (export "f") (param i32 i32) (result i32)
    (call_indirect (type $bin) (local.get 0) (i32.const 10) (local.get 1))))
