;; #1021 — i32.popcnt Thumb-2/A32 expansion clobbers R11, the WASM linear
;; memory base. Fixture for popcnt_r11_clobber_1021_differential.py.
(module
  (memory (export "memory") 1)

  ;; The confirmed v0.58.0 repro: popcnt followed by a memory read in the SAME
  ;; function. Pre-fix the expansion's last R11 write is `lsr.w r11, rX, #16`,
  ;; so the following `ldr [r11]` reads through garbage — f(0xFF) observed
  ;; 0x20020008 (popcnt 8 + the word at ADDRESS 0, the vector table's initial
  ;; SP) instead of 1242.
  (func (export "pc_load") (param i32) (result i32)
    (i32.store (i32.const 0) (i32.const 1234))
    (i32.add (i32.popcnt (local.get 0)) (i32.load (i32.const 0))))

  ;; Store side of the same class: the popcnt result is written THROUGH the
  ;; corrupted base, then read back through the (also corrupted) base.
  (func (export "pc_store") (param i32) (result i32)
    (i32.store (i32.const 8) (i32.popcnt (local.get 0)))
    (i32.load (i32.const 8)))

  ;; THE LEAK, cross-call: R11 is not in the expansion's saved set, so a
  ;; callee's popcnt corrupts the CALLER's linear-memory base — the caller's
  ;; load AFTER the call goes through garbage even though the callee's own
  ;; return value is right.
  (func $leaf (param i32) (result i32)
    (i32.popcnt (local.get 0)))
  (func (export "pc_caller") (param i32) (result i32)
    (i32.store (i32.const 4) (i32.const 5678))
    (i32.add (call $leaf (local.get 0)) (i32.load (i32.const 4))))

  ;; Guards.
  ;; Plain popcnt: the value itself (must stay right after the rework).
  (func (export "pc") (param i32) (result i32)
    (i32.popcnt (local.get 0)))
  ;; i64.popcnt uses the R3/R4/R5/R12 pushed-scratch discipline and is NOT
  ;; affected — pinned here so the fix cannot regress the healthy sibling.
  (func (export "pc64") (param i32) (result i32)
    (i32.store (i32.const 12) (i32.const 4321))
    (i32.add
      (i32.wrap_i64 (i64.popcnt (i64.extend_i32_u (local.get 0))))
      (i32.load (i32.const 12))))
)
