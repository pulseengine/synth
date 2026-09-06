;; RQ-63-RVGLOBAL (#242, v0.63) — RV32 WASM globals fixture.
;;
;; Every global shape the RV32 lowering must get right, each observable
;; through an export the boot differential executes against wasmtime:
;;   $a   mutable i32, NONZERO init       — a dropped initializer reads 0
;;   $b   immutable i32, NEGATIVE init    — sign must survive the slot
;;   $c   mutable i64, both words nonzero — the #649 high-word-zeroed class
;;   $d   mutable i32, zero init          — the only shape a zeroed table
;;                                          "gets right" by accident
;;   $e   mutable i64, all-ones           — both words 0xFFFFFFFF
;;   $sp  mutable i32 pointer into linear memory — the `__stack_pointer`
;;        shape every toolchain module carries; exercises global.get/set
;;        feeding a real s11-relative load/store
;;
;; The slot layout is dense by declared width (#643): a=0 b=4 c=8 d=16 e=20
;; sp=28 — so $c and $e sit at 4-aligned-but-not-8-aligned offsets, which a
;; lowering that assumed uniform 8-byte slots would read wrong.
(module
  (memory 1)
  (global $a  (mut i32) (i32.const 7))
  (global $b  i32       (i32.const -123456))
  (global $c  (mut i64) (i64.const 0x1122334455667788))
  (global $d  (mut i32) (i32.const 0))
  (global $e  (mut i64) (i64.const -1))
  (global $sp (mut i32) (i32.const 1024))

  (func (export "get_a") (result i32) global.get $a)
  (func (export "set_a") (param i32) local.get 0 global.set $a)
  (func (export "get_b") (result i32) global.get $b)
  (func (export "get_c") (result i64) global.get $c)
  ;; i64 PARAMS decline on RV32 (#518), so the i64 write arrives as two i32s.
  (func (export "set_c_parts") (param i32 i32)
    local.get 0 i64.extend_i32_u
    local.get 1 i64.extend_i32_u i64.const 32 i64.shl
    i64.or
    global.set $c)
  (func (export "get_d") (result i32) global.get $d)
  ;; read-modify-write through the global, then read it back
  (func (export "bump_d") (param i32) (result i32)
    global.get $d local.get 0 i32.add global.set $d
    global.get $d)
  (func (export "get_e_lo") (result i32) global.get $e i32.wrap_i64)
  (func (export "get_e_hi") (result i32)
    global.get $e i64.const 32 i64.shr_u i32.wrap_i64)
  ;; e := 0 - e (void export: its effect is observed by the two reads above)
  (func (export "neg_e")
    i64.const 0 global.get $e i64.sub global.set $e)

  ;; a 4-byte push-down stack in linear memory driven by the $sp global
  (func (export "get_sp") (result i32) global.get $sp)
  (func (export "push") (param i32) (result i32)
    global.get $sp i32.const 4 i32.sub global.set $sp
    global.get $sp local.get 0 i32.store
    global.get $sp)
  (func (export "pop") (result i32)
    global.get $sp i32.load
    global.get $sp i32.const 4 i32.add global.set $sp))
