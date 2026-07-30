;; #851 lane L3 — aarch64 globals execution differential fixture.
;;
;; Interleaves i32 and i64 globals so a WRONG SLOT STRIDE shifts every later
;; global (the emitted region uses uniform 8-byte slots; a dense width-summed
;; layout would put `$big` at offset 4 and misalign everything after it).
;;
;; Every global is MUTABLE and every accessor is a LEAF or a simple function,
;; because the point under test is the region + its addressing, not the call ABI.
(module
  (global $counter (mut i32) (i32.const 41))
  (global $big     (mut i64) (i64.const 1234567890123))
  (global $second  (mut i32) (i32.const -7))

  ;; Read each global's INITIAL value (run before anything is written).
  (func (export "get_i32") (result i32) (global.get $counter))
  (func (export "get_i64") (result i64) (global.get $big))
  (func (export "get_second_i32") (result i32) (global.get $second))

  ;; Read-modify-write: proves the store lands in the region and PERSISTS.
  (func (export "bump") (param i32) (result i32)
    (global.set $counter (i32.add (global.get $counter) (local.get 0)))
    (global.get $counter))

  ;; A 64-bit store: BOTH words must reach the slot (the #649 class).
  (func (export "set_i64") (param i64) (result i64)
    (global.set $big (local.get 0))
    (global.get $big))

  ;; Touches all three at once, so a slot-stride error cannot hide behind a
  ;; single-global test.
  (func (export "sum_all") (result i64)
    (i64.add
      (i64.add
        (i64.extend_i32_s (global.get $counter))
        (global.get $big))
      (i64.extend_i32_s (global.get $second)))))
