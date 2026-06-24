;; perf repro (#390, epic #242): consecutive stores to constant addresses
;; re-materialize the linear-memory base on EVERY store.
;;
;; The absolute / native-pointer store path lowers `i32.store* (i32.const ADDR) V`
;; as: `movw ip,#<base_lo>; movt ip,#<base_hi>; add ip,ip,ADDR; str V,[ip]`. The
;; base (e.g. 0x20000100) is a loop-invariant compile-time constant, but it is
;; materialized fresh (movw+movt = 8 B, ~2 cyc) before each store. A straight-line
;; run of N stores pays N base-materializations where 1 would do — hoisting the base
;; into a stable register and addressing each store as `add ip,base,ADDR` saves
;; (N-1) * (movw+movt). Common in struct/field initializers.
;;
;; Generic addresses/values — exhibits the pattern, tied to nothing real.
(module
  (memory 1)
  (func (export "init_fields")
    (i32.store   (i32.const 0)  (i32.const 11))
    (i32.store   (i32.const 4)  (i32.const 22))
    (i32.store   (i32.const 8)  (i32.const 33))
    (i32.store16 (i32.const 12) (i32.const 44))
    (i32.store16 (i32.const 14) (i32.const 55))
    (i32.store8  (i32.const 16) (i32.const 66))
    (i32.store8  (i32.const 17) (i32.const 77))))
